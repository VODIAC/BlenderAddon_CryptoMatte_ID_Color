bl_info = {
    "name": "CryptoMatte ID Color",
    "author": "61+",
    "version": (1, 1, 0),
    "blender": (4, 5, 0),
    "location": "Compositor > Sidebar > Tool",
    "description": "Generate real-time ID color compositor nodes using Cryptomatte.",
    "category": "Compositing",
}

import base64
import colorsys
import glob
import os
import random
import struct
import time
import zlib

import bpy
from bpy.app.handlers import persistent
from bpy.props import BoolProperty, FloatVectorProperty, StringProperty
from bpy.types import AddonPreferences, Operator, Panel
from bpy_extras.object_utils import world_to_camera_view
from mathutils import Vector
import numpy as np
import OpenImageIO as oiio
import PyOpenColorIO as ocio


# --- Add-on constants and runtime state ---

OBJECT_GROUP_NAME = "ObjectID"
MATERIAL_GROUP_NAME = "Material ID"
ID_INPUT_NAME = "ID input"
OUTPUT_NAME = "Image"
CRYPTO_X = -540
GAMMA_X = -260
SET_ALPHA_X = -80
ALPHA_OVER_X = 150
CRYPTO_ROW_STEP = 210
GAMMA_Y_OFFSET = -21
SET_ALPHA_Y_OFFSET = 19
ALPHA_OVER_Y_OFFSET = 105
OBJECT_GROUP_OFFSET = (513, 4)
MATERIAL_GROUP_OFFSET = (315, -98)
ADDON_PACKAGE = __package__ or __name__
EXR_OUTPUT_MARKER = "cryptomatte_id_color_exr_output"
PSD_OUTPUT_MARKER = "cryptomatte_id_color_psd_output"
PSD_LAYER_NAME_MARKER = "cryptomatte_id_color_psd_layer_name"
PSD_LAYER_FILE_MARKER = "cryptomatte_id_color_psd_layer_file"
DEFAULT_EXR_OUTPUT_DIR = "/tmp\\"

SHORTCUT_TARGETS = (
    ("object_id.create", "Object ID", "O", {"alt": True}),
    ("object_id.create_material", "Material ID", "M", {"alt": True}),
    ("object_id.change", "Change ID", "PERIOD", {"alt": True}),
    ("object_id.random", "Random ID", "COMMA", {"alt": True}),
)

SHORTCUT_KEYMAP_NAME = "Node Editor"
SHORTCUT_KEYMAP_SPACE_TYPE = "NODE_EDITOR"

RENDERABLE_TYPES = {
    "MESH",
    "CURVE",
    "SURFACE",
    "META",
    "FONT",
    "VOLUME",
    "GPENCIL",
    "GREASEPENCIL",
}

addon_keymaps = []
visibility_prepass_active = False
visibility_cache = {"key": None, "time": 0.0, "names": ()}
_icc_profile_bytes_cache = None


BLENDER_TO_PS_BLEND = {
    "MIX": b"norm", "DARKEN": b"dark", "MULTIPLY": b"mul ", "BURN": b"idiv",
    "LIGHTEN": b"lite", "SCREEN": b"scrn", "DODGE": b"div ", "ADD": b"lddg",
    "OVERLAY": b"over", "SOFT_LIGHT": b"sLit", "HARD_LIGHT": b"hLit",
    "DIFFERENCE": b"diff", "EXCLUSION": b"smud", "SUBTRACT": b"fsub",
    "DIVIDE": b"fdiv", "HUE": b"hue ", "SATURATION": b"sat ",
    "COLOR": b"colr", "VALUE": b"lum ", "PASS_THROUGH": b"pass",
}

# sRGB v4 profile, stored compressed to keep the embedded PSD library compact.
ICC_PROFILE_B64_SRGB_V4 = (
    "eNqVkblLQ0EQhz8TJaKRFKZIYZEiWhnRKKKdRLxALZIIRm2Sl0vI8XgvImIr2AoWHo1XYWOtrWAtCIIX4l9gpWgj4TmbBBKEFM6y"
    "O9/+dmb2AttiVsuZzf2QyxeN0FTQuxhd8jpesOHBiVhMM/W58GSEhvb9QJPy935Vi/9ZeyJpatDUKjym6UZReFp4fr2oK94XdmuZ"
    "WEL4QrjXkAMKPyk9XuF3xeky21RNtxEJjQu7hb3pOo7XsZYxcsJDwr5cdk2rnkfdxJnML4SVLr0LkxBTBPEywwTjDDPAqIzD+AnQ"
    "JzMa5AfK+fMUJFeTUWcDg1XSZCjSK+qaVE+KT4melJaVCDH1B3/f1kwNBio7OIPQ8mZZn93g2IXSjmX9nFhW6RTsr3Cdr+UXjmHk"
    "S/SdmuY7AtcWXN7UtPgeXG2D51mPGbGyZJduS6Xg4xw6otB5B23LlXerrnP2CJFNmL2Fg0PokXjXyi97CGbR"
)


# --- Generic socket helpers ---

def _socket_by_name(sockets, names, fallback_index=None):
    for name in names:
        socket = sockets.get(name)
        if socket:
            return socket

    wanted = {name.lower() for name in names}
    for socket in sockets:
        if socket.name.lower() in wanted or socket.identifier.lower() in wanted:
            return socket

    if fallback_index is not None and len(sockets) > fallback_index:
        return sockets[fallback_index]

    return None


# --- Camera visibility prepass ---

class VisibilityPrepassError(RuntimeError):
    pass


@persistent
def invalidate_visibility_cache(_scene, _depsgraph):
    if visibility_prepass_active:
        return
    visibility_cache["key"] = None
    visibility_cache["time"] = 0.0
    visibility_cache["names"] = ()


def _visible_renderable_objects(context):
    view_layer = context.view_layer
    objects = []

    for obj in view_layer.objects:
        if obj.type not in RENDERABLE_TYPES or obj.hide_render:
            continue

        try:
            visible = obj.visible_get(view_layer=view_layer)
        except TypeError:
            visible = obj.visible_get()

        if visible:
            objects.append(obj)

    objects.sort(key=lambda item: item.name.lower())
    return objects


def _visibility_mask_color(index):
    code = ((index + 1) * 0x9E3779) & 0xFFFFFF
    return (((code >> 16) & 255) / 255.0, ((code >> 8) & 255) / 255.0, (code & 255) / 255.0, 1.0)


def _visibility_color_key(color):
    red, green, blue = (max(0, min(255, round(value * 255))) for value in color[:3])
    return (red << 16) | (green << 8) | blue


def _camera_projection_intersects(scene, obj):
    try:
        projected = [world_to_camera_view(scene, scene.camera, obj.matrix_world @ Vector(corner)) for corner in obj.bound_box]
    except Exception:
        return True
    if not projected or all(point.z <= 0.0 for point in projected):
        return False
    if any(point.z <= 0.0 for point in projected):
        return True
    minimum_x = min(point.x for point in projected)
    maximum_x = max(point.x for point in projected)
    minimum_y = min(point.y for point in projected)
    maximum_y = max(point.y for point in projected)
    return maximum_x >= 0.0 and minimum_x <= 1.0 and maximum_y >= 0.0 and minimum_y <= 1.0


def _visibility_cache_key(scene, candidates, width, height, depsgraph):
    camera_matrix = tuple(round(value, 6) for row in scene.camera.matrix_world for value in row)
    camera = scene.camera.data
    camera_state = tuple(
        getattr(camera, name, None)
        for name in (
            "type", "lens", "sensor_fit", "sensor_width", "sensor_height",
            "shift_x", "shift_y", "ortho_scale", "clip_start", "clip_end",
        )
    )
    object_state = tuple(
        (
            obj.as_pointer(),
            obj.name,
            getattr(obj.data, "as_pointer", lambda: 0)(),
            tuple(round(value, 5) for row in obj.matrix_world for value in row),
            tuple(
                round(value, 5)
                for corner in obj.evaluated_get(depsgraph).bound_box
                for value in corner
            ),
            obj.hide_render,
        )
        for obj in candidates
    )
    return (
        scene.as_pointer(), scene.frame_current, width, height,
        scene.render.pixel_aspect_x, scene.render.pixel_aspect_y,
        camera_matrix, camera_state, object_state,
    )


def _camera_visible_renderable_objects(context):
    """Return objects hit by the current camera's first opaque surface per pixel."""
    scene = context.scene
    view_layer = context.view_layer
    candidates = _visible_renderable_objects(context)
    if not candidates or scene.camera is None:
        return candidates

    final_width = max(1, round(scene.render.resolution_x * scene.render.resolution_percentage / 100.0))
    final_height = max(1, round(scene.render.resolution_y * scene.render.resolution_percentage / 100.0))
    scale = min(1.0, 1024.0 / max(final_width, final_height))
    mask_width = max(1, round(final_width * scale))
    mask_height = max(1, round(final_height * scale))

    depsgraph = context.evaluated_depsgraph_get()
    projected_candidates = []
    for obj in candidates:
        evaluated = obj.evaluated_get(depsgraph)
        if _camera_projection_intersects(scene, evaluated):
            projected_candidates.append(obj)
    candidates = projected_candidates
    if not candidates:
        return []

    cache_key = _visibility_cache_key(scene, candidates, mask_width, mask_height, depsgraph)
    if visibility_cache["key"] == cache_key and time.monotonic() - visibility_cache["time"] < 3.0:
        cached_names = set(visibility_cache["names"])
        return [obj for obj in candidates if obj.name in cached_names]

    global visibility_prepass_active
    original_engine = scene.render.engine
    original_tree = _scene_compositor_tree(scene)
    original_resolution = (scene.render.resolution_x, scene.render.resolution_y, scene.render.resolution_percentage)
    original_render_aa = getattr(scene.display, "render_aa", None)
    original_view_transform = scene.view_settings.view_transform
    original_colors = {obj.name: tuple(obj.color) for obj in candidates}
    original_shading = (
        scene.display.shading.light,
        scene.display.shading.color_type,
        scene.display.shading.background_type,
        tuple(scene.display.shading.background_color),
    )
    # Workbench still honors material transparency when filling the depth
    # buffer.  The Camera Visible Only option is intentionally a first-
    # opaque-surface test, so make every participating material opaque for
    # this short visibility prepass and restore it afterwards.
    material_states = {}
    for obj in candidates:
        for slot in obj.material_slots:
            material = slot.material
            if material is None or material.name in material_states:
                continue
            material_states[material.name] = (
                material,
                getattr(material, "blend_method", None),
                getattr(material, "show_transparent_back", None),
                getattr(material, "use_transparency_overlap", None),
            )
    temporary_tree = None
    visible_objects = None
    visibility_prepass_active = True
    try:
        colors = []
        for index, obj in enumerate(candidates):
            color = _visibility_mask_color(index)
            obj.color = color
            colors.append(color[:3])

        scene.render.engine = "BLENDER_WORKBENCH"
        scene.display.shading.light = "FLAT"
        scene.display.shading.color_type = "OBJECT"
        scene.display.shading.background_type = "VIEWPORT"
        scene.display.shading.background_color = (0.0, 0.0, 0.0)
        scene.view_settings.view_transform = "Raw"
        for material, _blend_method, _show_transparent_back, _transparency_overlap in material_states.values():
            try:
                material.blend_method = "OPAQUE"
            except (AttributeError, TypeError):
                pass
            try:
                material.show_transparent_back = False
            except (AttributeError, TypeError):
                pass
            try:
                material.use_transparency_overlap = False
            except (AttributeError, TypeError):
                pass
        if original_render_aa is not None:
            scene.display.render_aa = "OFF"
        scene.render.resolution_x = mask_width
        scene.render.resolution_y = mask_height
        scene.render.resolution_percentage = 100
        temporary_tree = bpy.data.node_groups.new("CryptoMatte Visibility Memory", "CompositorNodeTree")
        scene.compositing_node_group = temporary_tree
        render_layers = temporary_tree.nodes.new("CompositorNodeRLayers")
        viewer = temporary_tree.nodes.new("CompositorNodeViewer")
        render_layers.scene = scene
        render_layers.layer = view_layer.name
        temporary_tree.links.new(render_layers.outputs[0], viewer.inputs[0])
        bpy.ops.render.render()

        render_result = bpy.data.images.get("Render Result")
        if render_result is None or render_result.size[0] <= 0 or render_result.size[1] <= 0:
            render_result = bpy.data.images.get("Viewer Node")
        if render_result is None or render_result.size[0] <= 0 or render_result.size[1] <= 0:
            raise VisibilityPrepassError("Camera visibility prepass produced no readable render result.")
        pixels = np.empty(render_result.size[0] * render_result.size[1] * 4, dtype=np.float32)
        render_result.pixels.foreach_get(pixels)
        rgb = np.clip(np.rint(pixels.reshape((-1, 4))[:, :3] * 255.0), 0, 255).astype(np.uint32)
        pixel_keys = (rgb[:, 0] << 16) | (rgb[:, 1] << 8) | rgb[:, 2]
        present = np.zeros(1 << 24, dtype=np.bool_)
        present[pixel_keys] = True
        palette_keys = np.asarray([_visibility_color_key(color) for color in colors], dtype=np.uint32)
        visible_indices = set(np.flatnonzero(present[palette_keys]).tolist())
        if not visible_indices:
            raise VisibilityPrepassError("Camera visibility prepass could not identify any object colors.")
        visible_objects = [obj for index, obj in enumerate(candidates) if index in visible_indices]
    finally:
        for obj_name, color in original_colors.items():
            obj = bpy.data.objects.get(obj_name)
            if obj:
                obj.color = color
        for material, blend_method, show_transparent_back, transparency_overlap in material_states.values():
            if blend_method is not None:
                try:
                    material.blend_method = blend_method
                except (AttributeError, TypeError):
                    pass
            if show_transparent_back is not None:
                try:
                    material.show_transparent_back = show_transparent_back
                except (AttributeError, TypeError):
                    pass
            if transparency_overlap is not None:
                try:
                    material.use_transparency_overlap = transparency_overlap
                except (AttributeError, TypeError):
                    pass
        scene.render.engine = original_engine
        scene.render.resolution_x, scene.render.resolution_y, scene.render.resolution_percentage = original_resolution
        if original_render_aa is not None:
            scene.display.render_aa = original_render_aa
        scene.view_settings.view_transform = original_view_transform
        scene.display.shading.light, scene.display.shading.color_type, scene.display.shading.background_type, background_color = original_shading
        scene.display.shading.background_color = background_color
        scene.compositing_node_group = original_tree
        if temporary_tree:
            bpy.data.node_groups.remove(temporary_tree)
        visibility_prepass_active = False

    visibility_cache["key"] = cache_key
    visibility_cache["time"] = time.monotonic()
    visibility_cache["names"] = tuple(obj.name for obj in visible_objects)
    return visible_objects


def _visible_materials(context):
    materials = {}
    for obj in _camera_visible_renderable_objects(context) if getattr(context.scene, "cryptomatte_camera_visible_only", False) else _visible_renderable_objects(context):
        for slot in obj.material_slots:
            material = slot.material
            if material:
                materials[material.name] = material

    return [materials[name] for name in sorted(materials.keys(), key=str.lower)]


# --- Compositor group interface and scene-tree helpers ---

def _auto_color(index, total):
    if total <= 0:
        return (1.0, 1.0, 1.0, 1.0)

    red, green, blue = colorsys.hsv_to_rgb(index / total, 1.0, 1.0)
    return (red, green, blue, 1.0)


def _ensure_group_socket(group, name, in_out, socket_type="NodeSocketColor"):
    if hasattr(group, "interface"):
        return group.interface.new_socket(name=name, in_out=in_out, socket_type=socket_type)

    if in_out == "INPUT":
        return group.inputs.new(socket_type, name)

    return group.outputs.new(socket_type, name)


def _set_interface_default(group, socket_name, value):
    if not hasattr(group, "interface"):
        socket = group.inputs.get(socket_name)
        if socket and hasattr(socket, "default_value"):
            socket.default_value = value
        return

    for item in group.interface.items_tree:
        if item.item_type == "SOCKET" and item.name == socket_name:
            if hasattr(item, "default_value"):
                item.default_value = value
            return


def _scene_compositor_tree(scene):
    if hasattr(scene, "node_tree"):
        return scene.node_tree

    return getattr(scene, "compositing_node_group", None)


def _ensure_scene_compositor_tree(scene):
    if hasattr(scene, "node_tree"):
        scene.use_nodes = True
        return scene.node_tree

    tree = getattr(scene, "compositing_node_group", None)
    if tree:
        return tree

    tree = bpy.data.node_groups.new("Scene Compositing", "CompositorNodeTree")
    scene.compositing_node_group = tree
    scene.use_nodes = True
    return tree


def _remove_old_group(scene, group_name):
    tree = _scene_compositor_tree(scene)

    if tree:
        for node in list(tree.nodes):
            if node.bl_idname == "CompositorNodeGroup" and node.node_tree and node.node_tree.name == group_name:
                tree.nodes.remove(node)

    group = bpy.data.node_groups.get(group_name)
    if group:
        bpy.data.node_groups.remove(group, do_unlink=True)


def _configure_cryptomatte_node(node, scene, view_layer, matte_name, layer_name):
    node.label = matte_name

    for attr_name, attr_value in (
        ("scene", scene),
        ("source", "RENDER"),
        ("layer_name", layer_name),
        ("matte_id", matte_name),
        ("layer", view_layer.name),
    ):
        try:
            setattr(node, attr_name, attr_value)
        except Exception:
            pass


# --- EXR and PSD output-node setup ---

def _psd_temp_directory(scene, group_name):
    return os.path.join(_exr_output_directory(scene), ".cryptomatte_id_color_psd", group_name)


def _project_name():
    filepath = bpy.data.filepath
    if filepath:
        return os.path.splitext(os.path.basename(filepath))[0]
    return "Untitled"


def _exr_output_name(group_name):
    suffix = "Object" if group_name == OBJECT_GROUP_NAME else "Material"
    return f"{_project_name()}_{suffix}"


def _exr_output_directory(scene):
    path = getattr(scene, "cryptomatte_exr_output_path", "") or DEFAULT_EXR_OUTPUT_DIR
    return bpy.path.abspath(path)


def _remove_generated_output_nodes(group):
    for node in list(group.nodes):
        if node.bl_idname == "CompositorNodeOutputFile" and (
            node.get(EXR_OUTPUT_MARKER) or node.get(PSD_OUTPUT_MARKER)
        ):
            group.nodes.remove(node)


def _configure_exr_format(node):
    node.format.media_type = "MULTI_LAYER_IMAGE"
    node.format.file_format = "OPEN_EXR_MULTILAYER"
    node.format.color_depth = "16"
    node.format.exr_codec = "DWAA"
    node.format.quality = 90


def _file_output_item_socket(node, item_name):
    for socket in node.inputs:
        if socket.name == item_name and socket.identifier != "__extend__":
            return socket
    return None


def _sync_exr_output_for_group(context, group, group_name, layers):
    scene = context.scene
    if not getattr(scene, "cryptomatte_use_exr", False) or not layers:
        return None

    output_node = group.nodes.new("CompositorNodeOutputFile")
    output_node.name = f"{group_name} EXR Output"
    output_node.label = "EXR Output"
    output_node[EXR_OUTPUT_MARKER] = group_name
    output_node.location = (760, 80)
    output_node.directory = _exr_output_directory(scene)
    output_node.file_name = _exr_output_name(group_name)
    _configure_exr_format(output_node)

    for layer_name, _source_socket in layers:
        item = output_node.file_output_items.new(socket_type="RGBA", name=layer_name)
        item.save_as_render = True
    for layer_name, source_socket in layers:
        input_socket = _file_output_item_socket(output_node, layer_name)
        if source_socket and input_socket:
            group.links.new(source_socket, input_socket)

    return output_node


def _safe_filename(value, fallback):
    safe = "".join(char if char.isalnum() or char in "._-" else "_" for char in value).strip("._")
    return safe or fallback


def _sync_psd_output_for_group(context, group, group_name, layers):
    scene = context.scene
    if not getattr(scene, "cryptomatte_use_psd", False) or not layers:
        return []

    output_nodes = []
    for index, (layer_name, source_socket) in enumerate(layers, start=1):
        output_node = group.nodes.new("CompositorNodeOutputFile")
        output_node.name = f"PSD Source EXR {index:03d}"
        output_node.label = f"PSD EXR: {layer_name}"
        output_node[PSD_OUTPUT_MARKER] = group_name
        output_node[PSD_LAYER_NAME_MARKER] = layer_name
        output_node[PSD_LAYER_FILE_MARKER] = f"{index:03d}_{_safe_filename(layer_name, 'Layer')}"
        output_node.location = (760, -180 - index * 45)
        output_node.directory = _psd_temp_directory(scene, group_name)
        output_node.file_name = output_node[PSD_LAYER_FILE_MARKER]
        _configure_exr_format(output_node)
        item = output_node.file_output_items.new(socket_type="RGBA", name=layer_name)
        item.save_as_render = True
        input_socket = _file_output_item_socket(output_node, layer_name)
        if source_socket and input_socket:
            group.links.new(source_socket, input_socket)
        output_nodes.append(output_node)
    return output_nodes


def _collect_exr_layers(group):
    layers = []
    linked_nodes = {}
    for link in group.links:
        linked_nodes.setdefault(link.from_socket.as_pointer(), []).append(link.to_node)

    def linked_node(socket, node_type):
        if socket is None:
            return None
        return next(
            (node for node in linked_nodes.get(socket.as_pointer(), ()) if node.bl_idname == node_type),
            None,
        )

    crypto_nodes = sorted(
        (node for node in group.nodes if node.bl_idname == "CompositorNodeCryptomatteV2"),
        key=lambda item: item.location.y,
        reverse=True,
    )
    for crypto in crypto_nodes:
        matte_output = _socket_by_name(crypto.outputs, ["Matte"], 1)
        gamma = linked_node(matte_output, "ShaderNodeGamma")
        gamma_output = _socket_by_name(gamma.outputs, ["Image", "Color"], 0) if gamma else None
        set_alpha = linked_node(gamma_output, "CompositorNodeSetAlpha")
        set_alpha_output = _socket_by_name(set_alpha.outputs, ["Image"], 0) if set_alpha else None
        layer_name = getattr(crypto, "matte_id", "") or crypto.label or crypto.name
        if layer_name and set_alpha_output:
            layers.append((layer_name, set_alpha_output))
    return layers


def sync_exr_outputs(context):
    scene = context.scene if context else None
    if scene is None:
        return

    for group_name in (OBJECT_GROUP_NAME, MATERIAL_GROUP_NAME):
        group = bpy.data.node_groups.get(group_name)
        if group is not None:
            _remove_generated_output_nodes(group)

    if not (getattr(scene, "cryptomatte_use_exr", False) or getattr(scene, "cryptomatte_use_psd", False)):
        return

    group_node = _active_viewer_group_node(scene)
    group = group_node.node_tree if group_node else None
    if group is None or group.name not in {OBJECT_GROUP_NAME, MATERIAL_GROUP_NAME}:
        return

    layers = _collect_exr_layers(group)
    _sync_exr_output_for_group(context, group, group.name, layers)
    _sync_psd_output_for_group(context, group, group.name, layers)


def update_exr_output_settings(self, context):
    sync_exr_outputs(context)


# --- Embedded PSD/PSB writer ---

def fast_rle_encode_row(row_bytes):
    encoded = bytearray()
    index = 0
    while index < len(row_bytes):
        run_length = 1
        while index + run_length < len(row_bytes) and run_length < 128 and row_bytes[index] == row_bytes[index + run_length]:
            run_length += 1
        if run_length > 1:
            encoded.extend(((257 - run_length) & 0xFF, row_bytes[index]))
            index += run_length
            continue
        literal_start = index
        index += 1
        while index < len(row_bytes) and index - literal_start < 128:
            if index + 1 < len(row_bytes) and row_bytes[index] == row_bytes[index + 1]:
                break
            index += 1
        encoded.append(index - literal_start - 1)
        encoded.extend(row_bytes[literal_start:index])
    return bytes(encoded)


def process_channel_data(channel_bytes, row_bytes, height, compression, use_psb):
    if compression == "RAW":
        return struct.pack(">H", 0) + channel_bytes
    if compression == "ZIP":
        return struct.pack(">H", 2) + zlib.compress(channel_bytes, level=1)
    rows = [fast_rle_encode_row(channel_bytes[row * row_bytes:(row + 1) * row_bytes]) for row in range(height)]
    row_length_format = ">I" if use_psb else ">H"
    return struct.pack(">H", 1) + b"".join(struct.pack(row_length_format, len(row)) for row in rows) + b"".join(rows)


def parse_layer_dict(layer_dict):
    flat_layers = []
    for key, info in reversed(list(layer_dict.items())):
        name = info.get("name", key)
        if info.get("type") == "group":
            flat_layers.append({"name": "</Layer group>", "is_marker": True, "folder_type": 3, "hide": True, "opacity": 0.0, "blend": "PASS_THROUGH"})
            flat_layers.extend(parse_layer_dict(info.get("layers", {})))
            flat_layers.append({"name": name, "is_marker": True, "folder_type": 1, "hide": info.get("hide", False), "opacity": info.get("opacity", 1.0), "blend": info.get("blend", "PASS_THROUGH")})
        else:
            flat_layers.append({"name": name, "path": info.get("path", ""), "exr_path": info.get("exr_path", ""), "exr_layer": info.get("exr_layer", name), "rgba": info.get("rgba"), "mask": info.get("mask"), "color": info.get("color"), "color_space": info.get("color_space", ""), "is_marker": False, "folder_type": 0, "hide": info.get("hide", False), "opacity": info.get("opacity", 1.0), "blend": info.get("blend", "MIX")})
    return flat_layers


def _exr_channel_indices(channel_names, layer_name):
    channel_map = {name: index for index, name in enumerate(channel_names)}
    indices = []
    for channel in ("R", "G", "B", "A"):
        for candidate in (f"{layer_name}.{channel}", f"{layer_name}.{channel.lower()}"):
            if candidate in channel_map:
                indices.append(channel_map[candidate])
                break
        else:
            indices.append(None)
    if any(index is None for index in indices[:3]):
        raise RuntimeError(f"EXR layer channels not found: {layer_name}")
    return indices


def _psd_color_context(scene):
    config = ocio.GetCurrentConfig()
    transform = ocio.DisplayViewTransform()
    transform.setSrc("scene_linear")
    transform.setDisplay(scene.display_settings.display_device)
    transform.setView(scene.view_settings.view_transform)
    return {
        "config": config,
        "display_processor": config.getProcessor(transform).getDefaultCPUProcessor(),
        "source_processors": {},
        "exposure_scale": 2.0 ** scene.view_settings.exposure,
        "gamma": scene.view_settings.gamma,
    }


def _source_to_scene_linear_processor(color_context, source_color_space):
    if not source_color_space or source_color_space == "scene_linear":
        return None
    processors = color_context["source_processors"]
    if source_color_space not in processors:
        transform = ocio.ColorSpaceTransform()
        transform.setSrc(source_color_space)
        transform.setDst("scene_linear")
        processors[source_color_space] = color_context["config"].getProcessor(transform).getDefaultCPUProcessor()
    return processors[source_color_space]


def _encode_psd_rgba(rgba, bit_depth, color_context, source_color_space="scene_linear"):
    rgb = np.ascontiguousarray(np.clip(rgba[:, :, :3], 0.0, None), dtype=np.float32)
    source_processor = _source_to_scene_linear_processor(color_context, source_color_space)
    if source_processor:
        source_processor.applyRGB(rgb)
    rgb *= color_context["exposure_scale"]
    color_context["display_processor"].applyRGB(rgb)
    if color_context["gamma"] != 1.0:
        np.maximum(rgb, 0.0, out=rgb)
        np.power(rgb, 1.0 / color_context["gamma"], out=rgb)
    np.clip(rgb, 0.0, 1.0, out=rgb)
    scale = 65535.0 if bit_depth == 16 else 255.0
    dtype = ">u2" if bit_depth == 16 else np.uint8
    channels = [np.rint(rgb[:, :, channel] * scale).astype(dtype).tobytes() for channel in range(3)]
    alpha = np.clip(rgba[:, :, 3], 0.0, 1.0)
    channels.append(np.rint(alpha * scale).astype(dtype).tobytes())
    return channels


def _read_exr_layer_rgba(path, layer_name):
    image_input = oiio.ImageInput.open(path)
    if image_input is None:
        raise RuntimeError(f"Could not open EXR: {path}")
    try:
        subimage = 0
        while image_input.seek_subimage(subimage, 0):
            spec = image_input.spec()
            try:
                indices = _exr_channel_indices(spec.channelnames, layer_name)
            except RuntimeError:
                subimage += 1
                continue
            first_channel = min(index for index in indices if index is not None)
            last_channel = max(index for index in indices if index is not None) + 1
            pixels = np.asarray(image_input.read_image(first_channel, last_channel, oiio.FLOAT), dtype=np.float32)
            pixels = pixels.reshape((spec.height, spec.width, last_channel - first_channel))
            rgba = np.empty((spec.height, spec.width, 4), dtype=np.float32)
            for target_channel, source_channel in enumerate(indices):
                rgba[:, :, target_channel] = 1.0 if source_channel is None else pixels[:, :, source_channel - first_channel]
            return spec.width, spec.height, rgba
        raise RuntimeError(f"EXR layer channels not found: {layer_name}")
    finally:
        image_input.close()


def _read_exr_layer(path, layer_name, bit_depth, color_context):
    width, height, rgba = _read_exr_layer_rgba(path, layer_name)
    return width, height, _encode_psd_rgba(rgba, bit_depth, color_context)


def _read_local_image(path, bit_depth, color_context, source_color_space=""):
    image = oiio.ImageBuf(path)
    if image.has_error:
        raise RuntimeError(image.geterror())
    spec = image.spec()
    pixels = np.asarray(image.get_pixels(oiio.FLOAT), dtype=np.float32).reshape((spec.height, spec.width, spec.nchannels))
    if spec.nchannels == 1:
        pixels = np.repeat(pixels, 3, axis=2)
    if pixels.shape[2] == 3:
        pixels = np.dstack((pixels, np.ones((spec.height, spec.width), dtype=np.float32)))
    source_color_space = source_color_space or spec.get_string_attribute("oiio:ColorSpace") or "sRGB"
    try:
        channels = _encode_psd_rgba(pixels[:, :, :4], bit_depth, color_context, source_color_space)
    except Exception as error:
        raise RuntimeError(f"Could not convert {source_color_space} to scene_linear for {path}: {error}") from error
    return spec.width, spec.height, channels


def _icc_profile_bytes():
    global _icc_profile_bytes_cache
    if _icc_profile_bytes_cache is None:
        _icc_profile_bytes_cache = zlib.decompress(base64.b64decode(ICC_PROFILE_B64_SRGB_V4))
    return _icc_profile_bytes_cache


def _layer_extra_data(layer):
    ascii_name = b"Layer"
    pascal_name = bytes((len(ascii_name),)) + ascii_name
    pascal_name += b"\0" * ((4 - len(pascal_name) % 4) % 4)
    lsct = b""
    if layer["folder_type"] in (1, 2, 3):
        lsct = b"8BIMlsct" + struct.pack(">I", 4) + struct.pack(">I", layer["folder_type"])
    unicode_name = layer["name"].encode("utf-16-be")
    luni = b"8BIMluni" + struct.pack(">I", 4 + len(unicode_name)) + struct.pack(">I", len(layer["name"])) + unicode_name
    return struct.pack(">II", 0, 0) + pascal_name + lsct + luni


def _composite_psd_layer(composite, raw_channels, width, height, bit_depth, layer):
    if layer["hide"] or layer["opacity"] <= 0.0:
        return composite
    dtype = np.dtype(">u2") if bit_depth == 16 else np.dtype(np.uint8)
    scale = 65535.0 if bit_depth == 16 else 255.0
    rgb = np.stack(
        [np.frombuffer(channel, dtype=dtype).reshape((height, width)) for channel in raw_channels[:3]],
        axis=2,
    ).astype(np.float32)
    rgb /= scale
    alpha = np.frombuffer(raw_channels[3], dtype=dtype).reshape((height, width)).astype(np.float32)
    alpha *= max(0.0, min(1.0, layer["opacity"])) / scale

    if composite is None:
        composite_rgb = np.zeros((height, width, 3), dtype=np.float32)
        composite_alpha = np.zeros((height, width), dtype=np.float32)
    else:
        composite_rgb, composite_alpha = composite
    remaining = 1.0 - composite_alpha
    composite_rgb += rgb * (alpha * remaining)[:, :, None]
    composite_alpha += alpha * remaining
    return composite_rgb, composite_alpha


def _encode_psd_composite(composite, bit_depth):
    composite_rgb, composite_alpha = composite
    visible = composite_alpha > 0.0
    composite_rgb[visible] /= composite_alpha[visible, None]
    np.clip(composite_rgb, 0.0, 1.0, out=composite_rgb)
    np.clip(composite_alpha, 0.0, 1.0, out=composite_alpha)
    scale = 65535.0 if bit_depth == 16 else 255.0
    dtype = ">u2" if bit_depth == 16 else np.uint8
    channels = [np.rint(composite_rgb[:, :, channel] * scale).astype(dtype).tobytes() for channel in range(3)]
    channels.append(np.rint(composite_alpha * scale).astype(dtype).tobytes())
    return channels


def export_psd_from_blender(psd_data):
    """Write a layered PSD/PSB from local image paths or in-memory RGBA layers."""
    use_psb = bool(psd_data.get("use_psb", False))
    compression = psd_data.get("compression", "RLE" if psd_data.get("use_rle", True) else "RAW").upper()
    if compression not in {"RAW", "RLE", "ZIP"}:
        raise ValueError("PSD compression must be RAW, RLE, or ZIP")
    bit_depth = int(psd_data.get("bit_depth", 8))
    if bit_depth not in (8, 16):
        raise ValueError("PSD bit_depth must be 8 or 16")
    output_path = psd_data.get("output_path", "")
    if not output_path:
        raise ValueError("PSD output_path is required")
    output_path = os.path.splitext(output_path)[0] + (".psb" if use_psb else ".psd")
    flat_layers = parse_layer_dict(psd_data.get("layer_data", {}))
    color_context = _psd_color_context(bpy.context.scene)
    layers = []
    width = height = 0
    composite = None
    for layer in flat_layers:
        if layer["is_marker"]:
            layers.append((layer, [struct.pack(">H", 0)] * 4))
            continue
        if layer.get("mask") is not None:
            mask = np.asarray(layer["mask"], dtype=np.float32)
            if mask.ndim != 2:
                raise ValueError(f"PSD mask layer has invalid shape: {layer['name']}")
            layer_height, layer_width = mask.shape
            rgba = np.empty((layer_height, layer_width, 4), dtype=np.float32)
            rgba[:, :, :3] = layer.get("color") or (1.0, 1.0, 1.0)
            rgba[:, :, 3] = mask
            raw_channels = _encode_psd_rgba(rgba, bit_depth, color_context)
        elif layer.get("rgba") is not None:
            rgba = np.asarray(layer["rgba"], dtype=np.float32)
            if rgba.ndim != 3 or rgba.shape[2] < 4:
                raise ValueError(f"PSD RGBA layer has invalid shape: {layer['name']}")
            layer_height, layer_width = rgba.shape[:2]
            raw_channels = _encode_psd_rgba(rgba[:, :, :4], bit_depth, color_context)
        elif layer.get("exr_path"):
            layer_width, layer_height, raw_channels = _read_exr_layer(
                bpy.path.abspath(layer["exr_path"]), layer["exr_layer"], bit_depth, color_context
            )
        else:
            path = bpy.path.abspath(layer["path"])
            if not path or not os.path.isfile(path):
                print(f"CryptoMatte ID Color: PSD layer not found: {path}")
                continue
            layer_width, layer_height, raw_channels = _read_local_image(
                path, bit_depth, color_context, layer.get("color_space", "")
            )
        if not width:
            width, height = layer_width, layer_height
        if (layer_width, layer_height) != (width, height):
            print(f"CryptoMatte ID Color: PSD layer size mismatch: {layer['name']}")
            continue
        composite = _composite_psd_layer(composite, raw_channels, width, height, bit_depth, layer)
        row_bytes = width * (2 if bit_depth == 16 else 1)
        layers.append((layer, [process_channel_data(channel, row_bytes, height, compression, use_psb) for channel in raw_channels]))
    if not layers or not width or composite is None:
        return False

    length_format = ">Q" if use_psb else ">I"
    records = []
    channel_data_length = 0
    for layer, channels in layers:
        record = bytearray()
        record.extend(struct.pack(">IIII", 0, 0, 0 if layer["is_marker"] else height, 0 if layer["is_marker"] else width))
        record.extend(struct.pack(">H", 4))
        for channel_id, channel_data in zip((0, 1, 2, -1), channels):
            record.extend(struct.pack(">h", channel_id) + struct.pack(length_format, len(channel_data)))
            channel_data_length += len(channel_data)
        record.extend(b"8BIM" + BLENDER_TO_PS_BLEND.get(layer["blend"], b"norm"))
        opacity = round(max(0.0, min(1.0, layer["opacity"])) * 255)
        record.extend(bytes((opacity, 0, 10 if layer["hide"] else 8, 0)))
        extra = _layer_extra_data(layer)
        record.extend(struct.pack(">I", len(extra)))
        record.extend(extra)
        records.append(record)
    layer_info_length = 2 + sum(len(record) for record in records) + channel_data_length
    padded_layer_info_length = layer_info_length + layer_info_length % 2
    layer_mask_length = struct.calcsize(length_format) + padded_layer_info_length + 4
    composite_channels = _encode_psd_composite(composite, bit_depth)
    os.makedirs(os.path.dirname(output_path) or ".", exist_ok=True)
    dpi = float(psd_data.get("dpi", 72.0))
    resolution = int(dpi * 65536)
    resources = b"8BIM" + struct.pack(">H", 1005) + b"\0\0" + struct.pack(">I", 16) + struct.pack(">IHHIHH", resolution, 1, 1, resolution, 1, 1)
    try:
        icc = _icc_profile_bytes()
        resources += b"8BIM" + struct.pack(">H", 1039) + b"\0\0" + struct.pack(">I", len(icc)) + icc + (b"\0" if len(icc) % 2 else b"")
    except Exception as error:
        print(f"CryptoMatte ID Color: ICC profile skipped: {error}")
    with open(output_path, "wb") as file_handle:
        file_handle.write(struct.pack(">4sH6sHIIHH", b"8BPS", 2 if use_psb else 1, b"\0" * 6, 4, height, width, bit_depth, 3))
        file_handle.write(struct.pack(">I", 0))
        file_handle.write(struct.pack(">I", len(resources)) + resources)
        file_handle.write(struct.pack(length_format, layer_mask_length))
        file_handle.write(struct.pack(length_format, layer_info_length))
        file_handle.write(struct.pack(">h", -len(layers)))
        for record in records:
            file_handle.write(record)
        for _layer, channels in layers:
            for channel_data in channels:
                file_handle.write(channel_data)
        if layer_info_length % 2:
            file_handle.write(b"\0")
        file_handle.write(struct.pack(">I", 0))
        file_handle.write(struct.pack(">H", 0))
        for channel in composite_channels:
            file_handle.write(channel)
    return True


# --- PSD post-render integration ---


@persistent
def export_psd_after_render(scene):
    if visibility_prepass_active or not getattr(scene, "cryptomatte_use_psd", False):
        return
    group_node = _active_viewer_group_node(scene)
    group = group_node.node_tree if group_node else None
    if group is None:
        return
    psd_nodes = sorted((node for node in group.nodes if node.get(PSD_OUTPUT_MARKER)), key=lambda node: node.name)
    if not psd_nodes:
        return
    try:
        layer_data = {}
        for index, node in enumerate(psd_nodes):
            matches = sorted(glob.glob(os.path.join(node.directory, f"{node.file_name}*.exr")), key=os.path.getmtime, reverse=True)
            if matches:
                layer_name = node.get(PSD_LAYER_NAME_MARKER, node.label)
                layer_data[f"layer_{index:03d}"] = {"name": layer_name, "type": "layer", "exr_path": matches[0], "exr_layer": layer_name, "hide": False, "blend": "MIX", "opacity": 1.0}
        if layer_data:
            output_path = os.path.join(_exr_output_directory(scene), f"{_exr_output_name(group.name)}.psd")
            if export_psd_from_blender({
                "output_path": output_path,
                "layer_data": layer_data,
                "compression": "ZIP",
                "bit_depth": 8,
                "dpi": 300.0,
            }):
                print(f"CryptoMatte ID Color: PSD saved to {output_path}")
    finally:
        directories = set()
        for node in psd_nodes:
            directories.add(node.directory)
            for path in glob.glob(os.path.join(node.directory, f"{node.file_name}*.exr")):
                if os.path.isfile(path):
                    os.remove(path)
        for directory in sorted(directories, key=len, reverse=True):
            if os.path.isdir(directory) and not os.listdir(directory):
                os.rmdir(directory)
            parent = os.path.dirname(directory)
            if os.path.isdir(parent) and not os.listdir(parent):
                os.rmdir(parent)


# --- ID compositor graph construction ---

def _build_id_group(context, group_name, id_names, layer_name):
    scene = context.scene
    view_layer = context.view_layer
    group = bpy.data.node_groups.new(group_name, "CompositorNodeTree")
    total = len(id_names)

    _ensure_group_socket(group, ID_INPUT_NAME, "INPUT", "NodeSocketColor")
    for index, id_name in enumerate(id_names):
        _ensure_group_socket(group, id_name, "INPUT", "NodeSocketColor")
        _set_interface_default(group, id_name, _auto_color(index, total))
    _ensure_group_socket(group, OUTPUT_NAME, "OUTPUT", "NodeSocketColor")

    nodes = group.nodes
    links = group.links

    group_input = nodes.new("NodeGroupInput")
    group_input.location = (-850, 0)
    group_output = nodes.new("NodeGroupOutput")
    group_output.location = (520, 0)
    group_output.is_active_output = True

    id_output = _socket_by_name(group_input.outputs, [ID_INPUT_NAME], 0)
    final_image = None

    for index, id_name in enumerate(id_names):
        y = -index * CRYPTO_ROW_STEP

        crypto = nodes.new("CompositorNodeCryptomatteV2")
        crypto.location = (CRYPTO_X, y)
        _configure_cryptomatte_node(crypto, scene, view_layer, id_name, layer_name)

        set_alpha = nodes.new("CompositorNodeSetAlpha")
        set_alpha.location = (SET_ALPHA_X, y + SET_ALPHA_Y_OFFSET)

        gamma = nodes.new("ShaderNodeGamma")
        # The Cryptomatte Matte and Gamma Color sockets share one horizontal
        # line.  The Set Alpha image output and Alpha Over foreground input do
        # the same below, keeping every generated row easy to scan.
        gamma.location = (GAMMA_X, y + GAMMA_Y_OFFSET)

        crypto_image_input = _socket_by_name(crypto.inputs, ["Image"], 0)
        crypto_matte_output = _socket_by_name(crypto.outputs, ["Matte"], 1)
        gamma_image_input = _socket_by_name(gamma.inputs, ["Image", "Color"], 0)
        gamma_value_input = _socket_by_name(gamma.inputs, ["Gamma"], 1)
        gamma_image_output = _socket_by_name(gamma.outputs, ["Image", "Color"], 0)
        color_output = _socket_by_name(group_input.outputs, [id_name])
        set_alpha_image_input = _socket_by_name(set_alpha.inputs, ["Image"], 0)
        set_alpha_alpha_input = _socket_by_name(set_alpha.inputs, ["Alpha"], 1)
        set_alpha_image_output = _socket_by_name(set_alpha.outputs, ["Image"], 0)

        if gamma_value_input and hasattr(gamma_value_input, "default_value"):
            gamma_value_input.default_value = 0.0

        if id_output and crypto_image_input:
            links.new(id_output, crypto_image_input)
        if color_output and set_alpha_image_input:
            links.new(color_output, set_alpha_image_input)
        if crypto_matte_output and gamma_image_input:
            links.new(crypto_matte_output, gamma_image_input)
        if gamma_image_output and set_alpha_alpha_input:
            links.new(gamma_image_output, set_alpha_alpha_input)

        if not final_image:
            final_image = set_alpha_image_output
            continue

        alpha_over = nodes.new("CompositorNodeAlphaOver")
        alpha_over.location = (ALPHA_OVER_X, y + ALPHA_OVER_Y_OFFSET)
        alpha_over.inputs[3].default_value = 'Disjoint Over'
        background_input = _socket_by_name(alpha_over.inputs, ["Background"], 0)
        foreground_input = _socket_by_name(alpha_over.inputs, ["Foreground"], 1)
        factor_input = _socket_by_name(alpha_over.inputs, ["Factor", "Fac"], 2)

        if factor_input and hasattr(factor_input, "default_value"):
            factor_input.default_value = 1.0

        if final_image and background_input:
            links.new(final_image, background_input)
        if set_alpha_image_output and foreground_input:
            links.new(set_alpha_image_output, foreground_input)
        final_image = alpha_over.outputs[0]

    output_input = _socket_by_name(group_output.inputs, [OUTPUT_NAME], 0)
    if final_image and output_input:
        links.new(final_image, output_input)

    return group


# --- Scene compositor integration and active-group discovery ---

def _find_or_create_node(tree, bl_idname, label, location):
    for node in tree.nodes:
        if node.bl_idname == bl_idname:
            return node

    node = tree.nodes.new(bl_idname)
    node.label = label
    node.location = location
    return node


def _ensure_render_layer_node(context, tree):
    node = _find_or_create_node(tree, "CompositorNodeRLayers", "Render Layers", (-580, 160))
    node.scene = context.scene

    try:
        node.layer = context.view_layer.name
    except Exception:
        pass

    return node


def _crypto_socket(render_layer_node, socket_name):
    socket = _socket_by_name(render_layer_node.outputs, [socket_name])
    if socket:
        return socket

    prefix = socket_name[:-2]
    for candidate in render_layer_node.outputs:
        if candidate.name.startswith(prefix):
            return candidate

    return None


def _add_group_node_and_links(context, group, crypto_socket_name, location_y):
    tree = _ensure_scene_compositor_tree(context.scene)
    render_layer = _ensure_render_layer_node(context, tree)
    group_offset = (
        OBJECT_GROUP_OFFSET
        if group.name == OBJECT_GROUP_NAME
        else MATERIAL_GROUP_OFFSET
    )
    # Anchor both generated groups to Render Layers.  Their top positions stay
    # fixed even when one group has a much longer interface than the other.
    group_x = render_layer.location.x + group_offset[0]
    group_y = render_layer.location.y + group_offset[1]

    group_node = tree.nodes.new("CompositorNodeGroup")
    group_node.node_tree = group
    group_node.name = group.name
    group_node.label = group.name
    group_node.location = (group_x, group_y)

    crypto_socket = _crypto_socket(render_layer, crypto_socket_name)
    id_input = _socket_by_name(group_node.inputs, [ID_INPUT_NAME], 0)
    if crypto_socket and id_input:
        tree.links.new(crypto_socket, id_input)

    # The scene compositor is only a display route for this add-on.  Its
    # Group Output node serves no purpose and makes the generated layout look
    # like there is a second destination, so remove the legacy node we used
    # to create and connect only to Viewer.
    for node in list(tree.nodes):
        if node.bl_idname == "NodeGroupOutput" and node.label == "Group Output":
            tree.nodes.remove(node)

    viewer = _find_or_create_node(tree, "CompositorNodeViewer", "Viewer", (380, location_y))
    viewer.location = (380, location_y)

    group_output = _socket_by_name(group_node.outputs, [OUTPUT_NAME], 0)
    viewer_input = _socket_by_name(viewer.inputs, ["Image"], 0)

    if group_output and viewer_input:
        for link in list(tree.links):
            if link.to_socket == viewer_input:
                tree.links.remove(link)
        tree.links.new(group_output, viewer_input)

    return crypto_socket is not None


# --- ID color lookup and editing ---

def _set_group_node_input_color(group_node, input_name, color):
    socket = group_node.inputs.get(input_name)
    if not socket or not hasattr(socket, "default_value"):
        return False

    socket.default_value = color
    if group_node.node_tree:
        _set_interface_default(group_node.node_tree, input_name, color)

    return True


def _input_link(tree, input_socket):
    for link in tree.links:
        if link.to_socket == input_socket:
            return link
    return None


def _linked_group_node_from_input(tree, input_socket, visited=None):
    if visited is None:
        visited = set()

    link = _input_link(tree, input_socket)
    if not link:
        return None

    source_node = link.from_node
    source_key = source_node.as_pointer() if hasattr(source_node, "as_pointer") else source_node.name
    if source_key in visited:
        return None
    visited.add(source_key)

    if (
        source_node.bl_idname == "CompositorNodeGroup"
        and source_node.node_tree
        and source_node.node_tree.name in {OBJECT_GROUP_NAME, MATERIAL_GROUP_NAME}
    ):
        return source_node

    if source_node.bl_idname == "NodeReroute" and source_node.inputs:
        return _linked_group_node_from_input(tree, source_node.inputs[0], visited)

    return None


def _active_viewer_and_group(scene):
    tree = _scene_compositor_tree(scene)
    if not tree:
        return None, None

    viewers = [node for node in tree.nodes if node.bl_idname == "CompositorNodeViewer"]
    active_node = getattr(tree.nodes, "active", None)
    if active_node in viewers:
        viewers.remove(active_node)
        viewers.insert(0, active_node)

    for viewer in viewers:
        viewer_input = _socket_by_name(viewer.inputs, ["Image"], 0)
        if not viewer_input:
            continue

        group_node = _linked_group_node_from_input(tree, viewer_input)
        if group_node:
            return viewer, group_node

    return None, None


def _active_viewer_group_node(scene):
    return _active_viewer_and_group(scene)[1]


def _material_input_names_for_object(obj, group_node):
    names = []
    for slot in obj.material_slots:
        material = slot.material
        if material and group_node.inputs.get(material.name):
            names.append(material.name)

    return sorted(set(names), key=str.lower)


def _target_input_names_for_viewer_group(obj, group_node):
    group_name = group_node.node_tree.name
    if group_name == OBJECT_GROUP_NAME:
        return [obj.name] if group_node.inputs.get(obj.name) else []
    if group_name == MATERIAL_GROUP_NAME:
        return _material_input_names_for_object(obj, group_node)
    return []


def _input_color_from_group_node(group_node, input_names):
    for input_name in input_names:
        socket = group_node.inputs.get(input_name)
        if socket and hasattr(socket, "default_value"):
            return tuple(socket.default_value)

    return (1.0, 1.0, 1.0, 1.0)


def _color_inputs(node):
    return [
        socket
        for socket in node.inputs
        if socket.name != ID_INPUT_NAME and hasattr(socket, "default_value")
    ]


def _randomize_group_input_colors(scene, group_name):
    tree = _scene_compositor_tree(scene)
    changed = False

    if not tree:
        return False

    for node in tree.nodes:
        if node.bl_idname != "CompositorNodeGroup":
            continue
        if not node.node_tree or node.node_tree.name != group_name:
            continue

        sockets = _color_inputs(node)
        if len(sockets) < 2:
            continue

        colors = [tuple(socket.default_value) for socket in sockets]
        random.shuffle(colors)

        for socket, color in zip(sockets, colors):
            socket.default_value = color
            _set_interface_default(node.node_tree, socket.name, color)

        changed = True

    return changed


# --- Blender-native keymap integration ---

def unregister_keymaps():
    while addon_keymaps:
        keymap, keymap_item = addon_keymaps.pop()
        try:
            keymap.keymap_items.remove(keymap_item)
        except Exception:
            pass


def sync_keymaps():
    unregister_keymaps()
    window_manager = bpy.context.window_manager
    keyconfig = window_manager.keyconfigs.addon
    if keyconfig is None:
        return

    keymap = keyconfig.keymaps.new(name=SHORTCUT_KEYMAP_NAME, space_type=SHORTCUT_KEYMAP_SPACE_TYPE)
    for operator_idname, _label, key_type, modifiers in SHORTCUT_TARGETS:
        keymap_item = keymap.keymap_items.new(
            operator_idname,
            key_type,
            "PRESS",
            ctrl=modifiers.get("ctrl", False),
            shift=modifiers.get("shift", False),
            alt=modifiers.get("alt", False),
            oskey=modifiers.get("oskey", False),
        )
        addon_keymaps.append((keymap, keymap_item))


def keymap_item_for_operator(context, operator_idname):
    keyconfigs = getattr(context.window_manager, "keyconfigs", None) if context else None
    for keyconfig in (getattr(keyconfigs, "user", None), getattr(keyconfigs, "addon", None)):
        if keyconfig is None:
            continue
        keymap = keyconfig.keymaps.get(SHORTCUT_KEYMAP_NAME)
        if keymap is None:
            continue
        for keymap_item in keymap.keymap_items:
            if keymap_item.idname == operator_idname:
                return keyconfig, keymap, keymap_item
    return None, None, None


# --- Operators ---

class OBJECTID_OT_create(Operator):
    bl_idname = "object_id.create"
    bl_label = "Object ID"
    bl_description = "Create an ObjectID compositor node group."
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        scene = context.scene
        view_layer = context.view_layer

        view_layer.use_pass_cryptomatte_object = True
        view_layer.pass_cryptomatte_depth = 2

        try:
            objects = _camera_visible_renderable_objects(context) if scene.cryptomatte_camera_visible_only else _visible_renderable_objects(context)
        except VisibilityPrepassError as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        if not objects:
            self.report({"WARNING"}, "No visible renderable objects found in the current view layer.")
            return {"CANCELLED"}

        _ensure_scene_compositor_tree(scene)
        _remove_old_group(scene, OBJECT_GROUP_NAME)

        object_names = [obj.name for obj in objects]
        group = _build_id_group(context, OBJECT_GROUP_NAME, object_names, "ViewLayer.CryptoObject")
        has_crypto_socket = _add_group_node_and_links(context, group, "CryptoObject00", 160)
        sync_exr_outputs(context)

        tree = _scene_compositor_tree(scene)
        if tree:
            tree.update_tag()

        if not has_crypto_socket:
            self.report(
                {"WARNING"},
                "ObjectID was created, but CryptoObject00 was not found on the Render Layers node.",
            )
            return {"FINISHED"}

        self.report({"INFO"}, f"ObjectID created for {len(object_names)} visible objects.")
        return {"FINISHED"}


class OBJECTID_OT_create_material(Operator):
    bl_idname = "object_id.create_material"
    bl_label = "Material ID"
    bl_description = "Create a Material ID compositor node group."
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        scene = context.scene
        view_layer = context.view_layer

        view_layer.use_pass_cryptomatte_material = True
        view_layer.pass_cryptomatte_depth = 2

        try:
            materials = _visible_materials(context)
        except VisibilityPrepassError as error:
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        if not materials:
            self.report({"WARNING"}, "No materials found on visible renderable objects.")
            return {"CANCELLED"}

        _ensure_scene_compositor_tree(scene)
        _remove_old_group(scene, MATERIAL_GROUP_NAME)

        material_names = [material.name for material in materials]
        group = _build_id_group(context, MATERIAL_GROUP_NAME, material_names, "ViewLayer.CryptoMaterial")
        has_crypto_socket = _add_group_node_and_links(context, group, "CryptoMaterial00", -120)
        sync_exr_outputs(context)

        tree = _scene_compositor_tree(scene)
        if tree:
            tree.update_tag()

        if not has_crypto_socket:
            self.report(
                {"WARNING"},
                "Material ID was created, but CryptoMaterial00 was not found on the Render Layers node.",
            )
            return {"FINISHED"}

        self.report({"INFO"}, f"Material ID created for {len(material_names)} visible materials.")
        return {"FINISHED"}


class OBJECTID_OT_change(Operator):
    bl_idname = "object_id.change"
    bl_label = "Change ID"
    bl_description = "Change the selected object's ID color."
    bl_options = {"REGISTER", "UNDO"}

    color: FloatVectorProperty(
        name="RGB Color",
        subtype="COLOR",
        size=4,
        min=0.0,
        max=1.0,
        default=(1.0, 1.0, 1.0, 1.0),
    )

    object_name: StringProperty(options={"HIDDEN"})
    group_name: StringProperty(options={"HIDDEN"})

    @classmethod
    def poll(cls, context):
        return context.scene is not None

    def invoke(self, context, _event):
        selected = context.selected_objects
        if len(selected) != 1:
            self.report({"ERROR"}, "Please select exactly one object before using Change ID.")
            return {"CANCELLED"}

        obj = selected[0]
        group_node = _active_viewer_group_node(context.scene)
        if not group_node:
            self.report({"ERROR"}, "Connect ObjectID or Material ID to the Viewer before using Change ID.")
            return {"CANCELLED"}

        input_names = _target_input_names_for_viewer_group(obj, group_node)
        if not input_names:
            self.report(
                {"ERROR"},
                f"Selected object has no matching input in the active {group_node.node_tree.name} node group.",
            )
            return {"CANCELLED"}

        self.object_name = obj.name
        self.group_name = group_node.node_tree.name
        self.color = _input_color_from_group_node(group_node, input_names)
        return context.window_manager.invoke_props_popup(self, _event)

    def draw(self, _context):
        self.layout.prop(self, "color", text="Color")

    def execute(self, context):
        obj = bpy.data.objects.get(self.object_name)
        if not obj:
            self.report({"ERROR"}, "Selected object no longer exists.")
            return {"CANCELLED"}

        color = tuple(self.color)

        group_node = _active_viewer_group_node(context.scene)
        if not group_node or group_node.node_tree.name != self.group_name:
            self.report({"ERROR"}, "The active Viewer connection changed. Run Change ID again.")
            return {"CANCELLED"}

        input_names = _target_input_names_for_viewer_group(obj, group_node)
        if not input_names:
            self.report({"ERROR"}, f"No matching {self.group_name} input was found for the selected object.")
            return {"CANCELLED"}

        changed = False
        for input_name in input_names:
            changed |= _set_group_node_input_color(group_node, input_name, color)

        if not changed:
            self.report({"ERROR"}, f"No editable {self.group_name} input was found for the selected object.")
            return {"CANCELLED"}

        if self.group_name == OBJECT_GROUP_NAME:
            obj["object_id_color"] = color

        tree = _scene_compositor_tree(context.scene)
        if tree:
            tree.update_tag()

        return {"FINISHED"}


class OBJECTID_OT_random(Operator):
    bl_idname = "object_id.random"
    bl_label = "Random ID"
    bl_description = "Randomize existing ID colors."
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        changed_object = _randomize_group_input_colors(context.scene, OBJECT_GROUP_NAME)
        changed_material = _randomize_group_input_colors(context.scene, MATERIAL_GROUP_NAME)

        if not changed_object and not changed_material:
            self.report({"INFO"}, "No ObjectID or Material ID node group with enough colors was found.")
            return {"CANCELLED"}

        tree = _scene_compositor_tree(context.scene)
        if tree:
            tree.update_tag()

        self.report({"INFO"}, "Random ID colors were reordered.")
        return {"FINISHED"}


# --- Preferences and compositor sidebar UI ---

class CRYPTOMATTE_ID_COLOR_Preferences(AddonPreferences):
    bl_idname = ADDON_PACKAGE

    def draw_shortcut_cell(self, layout, context, operator_idname, label_text):
        _keyconfig, _keymap, keymap_item = keymap_item_for_operator(context, operator_idname)
        if keymap_item is None:
            sync_keymaps()
            _keyconfig, _keymap, keymap_item = keymap_item_for_operator(context, operator_idname)
        if keymap_item is None:
            layout.label(text=f"{label_text}: shortcut not found", icon="ERROR")
            return

        if keymap_item.map_type != "KEYBOARD":
            keymap_item.map_type = "KEYBOARD"

        split = layout.split(factor=0.47, align=True)
        label_row = split.row(align=True)
        label_row.prop(keymap_item, "active", text="", emboss=False)
        label_row.label(text=label_text)
        event_row = split.row(align=True)
        event_row.prop(keymap_item, "type", text="", full_event=True)

    def draw(self, context):
        layout = self.layout
        info_col = layout.column(align=True)
        info_col.scale_y = 1
        info_col.label(text="Panel position: Compositor > Tool.      Use shortcut to achieve functions faster.")
        info_col.label(text='Create channels with "Object ID" or "Material ID". ')
        info_col.label(text='Edit one color with "Change ID". Randomize colors with "Random ID".')
        layout.separator(factor=0.5)

        for index in range(0, len(SHORTCUT_TARGETS), 2):
            row = layout.row(align=True)
            split = row.split(factor=0.5, align=True)
            columns = (split.column(align=True), split.column(align=True))
            for target, column in zip(SHORTCUT_TARGETS[index : index + 2], columns):
                operator_idname, label_text, _key_type, _modifiers = target
                self.draw_shortcut_cell(column, context, operator_idname, label_text)


class CRYPTOMATTE_ID_COLOR_PT_tools(Panel):
    bl_idname = "CRYPTOMATTE_ID_COLOR_PT_tools"
    bl_label = "CryptoMatte ID Color"
    bl_space_type = "NODE_EDITOR"
    bl_region_type = "UI"
    bl_category = "Tool"

    @classmethod
    def poll(cls, context):
        space = context.space_data
        return space and space.type == "NODE_EDITOR" and space.tree_type == "CompositorNodeTree"

    def draw(self, context):
        layout = self.layout
        row = layout.row(align=True)
        split = row.split(factor=0.5, align=True)
        split.operator("object_id.create", text="Object ID", icon="OBJECT_DATA")
        split.operator("object_id.create_material", text="Material ID", icon="MATERIAL_DATA")

        row = layout.row(align=True)
        split = row.split(factor=0.5, align=True)
        split.operator("object_id.change", text="Change ID", icon="COLOR")
        split.operator("object_id.random", text="Random ID", icon="FILE_REFRESH")

        layout.prop(context.scene, "cryptomatte_camera_visible_only", text="Camera Visible Only")

        row = layout.row(align=True)
        split = row.split(factor=0.5, align=True)
        export_row = split.row(align=True)
        export_row.alignment = "RIGHT"
        export_row.prop(context.scene, "cryptomatte_use_exr", text="EXR")
        export_row.separator(factor=0.8)
        export_row.prop(context.scene, "cryptomatte_use_psd", text="PSD")
        path_row = split.row(align=True)
        path_row.enabled = context.scene.cryptomatte_use_exr or context.scene.cryptomatte_use_psd
        path_row.prop(context.scene, "cryptomatte_exr_output_path", text="")




# --- Registration ---

classes = (
    CRYPTOMATTE_ID_COLOR_Preferences,
    OBJECTID_OT_create,
    OBJECTID_OT_create_material,
    OBJECTID_OT_change,
    OBJECTID_OT_random,
    CRYPTOMATTE_ID_COLOR_PT_tools,
)


def register():
    for cls in classes:
        bpy.utils.register_class(cls)
    bpy.types.Scene.cryptomatte_use_exr = BoolProperty(
        name="EXR",
        description="Create a multilayer EXR output for the active Object ID or Material ID group",
        default=False,
        update=update_exr_output_settings,
    )
    bpy.types.Scene.cryptomatte_use_psd = BoolProperty(
        name="PSD",
        description="Write a layered PSD with embedded sRGB ICC profile after rendering",
        default=False,
        update=update_exr_output_settings,
    )
    bpy.types.Scene.cryptomatte_camera_visible_only = BoolProperty(
        name="Camera Visible Only",
        description="Create ID layers only for objects visible as the first opaque surface from the active camera",
        default=False,
    )
    bpy.types.Scene.cryptomatte_exr_output_path = StringProperty(
        name="EXR Output Path",
        description="Folder for generated multilayer EXR files",
        default=DEFAULT_EXR_OUTPUT_DIR,
        subtype="DIR_PATH",
        update=update_exr_output_settings,
    )
    if export_psd_after_render not in bpy.app.handlers.render_complete:
        bpy.app.handlers.render_complete.append(export_psd_after_render)
    if invalidate_visibility_cache not in bpy.app.handlers.depsgraph_update_post:
        bpy.app.handlers.depsgraph_update_post.append(invalidate_visibility_cache)
    sync_keymaps()


def unregister():
    unregister_keymaps()
    while export_psd_after_render in bpy.app.handlers.render_complete:
        bpy.app.handlers.render_complete.remove(export_psd_after_render)
    while invalidate_visibility_cache in bpy.app.handlers.depsgraph_update_post:
        bpy.app.handlers.depsgraph_update_post.remove(invalidate_visibility_cache)
    for prop_name in ("cryptomatte_use_exr", "cryptomatte_use_psd", "cryptomatte_camera_visible_only", "cryptomatte_exr_output_path"):
        if hasattr(bpy.types.Scene, prop_name):
            delattr(bpy.types.Scene, prop_name)

    for cls in reversed(classes):
        bpy.utils.unregister_class(cls)


if __name__ == "__main__":
    register()
