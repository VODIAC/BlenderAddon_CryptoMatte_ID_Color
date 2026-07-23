bl_info = {
    "name": "CryptoMatte ID Color",
    "author": "61+",
    "version": (1, 1, 1),
    "blender": (4, 5, 0),
    "location": "Compositor > Sidebar > Tool",
    "description": "Generate real-time ID color compositor nodes using Cryptomatte.",
    "category": "Compositing",
}

import base64
import colorsys
import gc
import glob
import json
import os
import random
import shutil
import struct
import tempfile
import time
import traceback
import zlib

import bpy
from bpy.app.handlers import persistent
from bpy.props import BoolProperty, FloatProperty, FloatVectorProperty, StringProperty
from bpy.types import AddonPreferences, Operator, Panel
from bpy_extras.object_utils import world_to_camera_view
from mathutils import Vector
import numpy as np
import OpenImageIO as oiio
import PyOpenColorIO as ocio

from .translation import TRANSLATIONS


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
OBJECT_ROUTE_OFFSETS = {
    "REROUTE": (250.008, -32.355),
    "VIEWER": (377.460, 1.353),
    "GROUP_OUTPUT": (377.460, 79.672),
}
MATERIAL_ROUTE_OFFSETS = {
    "REROUTE": (448.008, -32.197),
    "VIEWER": (575.460, 1.196),
    "GROUP_OUTPUT": (575.460, -74.200),
}
ROUTE_OWNER_MARKER = "cryptomatte_id_color_route_owner"
ROUTE_ROLE_MARKER = "cryptomatte_id_color_route_role"
ADDON_PACKAGE = __package__ or __name__
EXR_OUTPUT_MARKER = "cryptomatte_id_color_exr_output"
PSD_OUTPUT_MARKER = "cryptomatte_id_color_psd_output"
PSD_LAYER_NAME_MARKER = "cryptomatte_id_color_psd_layer_name"
PSD_LAYER_FILE_MARKER = "cryptomatte_id_color_psd_layer_file"
DEFAULT_EXR_OUTPUT_DIR = "/tmp\\"
REMEMBERED_SCENE_SETTINGS = (
    ("cryptomatte_use_exr", "remembered_use_exr", False),
    ("cryptomatte_use_psd", "remembered_use_psd", False),
    ("cryptomatte_camera_visible_only", "remembered_camera_visible_only", True),
    ("cryptomatte_low_memory", "remembered_low_memory", False),
    ("cryptomatte_exr_output_path", "remembered_output_path", DEFAULT_EXR_OUTPUT_DIR),
)

SHORTCUT_TARGETS = (
    ("object_id.create", "Object ID", "O", {"alt": True}),
    ("object_id.create_material", "Material ID", "M", {"alt": True}),
    ("object_id.change", "Change ID", "PERIOD", {"alt": True}),
    ("object_id.random", "Random ID", "COMMA", {"alt": True}),
    ("object_id.render_id_channel", "Render ID Channel", "F12", {"shift": True, "alt": True}),
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
low_memory_render_jobs = {}
render_id_restore_snapshots = {}
remembered_settings_loading = False
export_progress = {
    "active": False,
    "scene_name": "",
    "started_at": 0.0,
    "completed": 0.0,
    "total": 1.0,
    "phase": "",
    "history_key": None,
    "estimated_total": None,
    "work_size": 0.0,
    "workspace_names": (),
    "ui_installed": False,
}
export_duration_history = {}
export_progress_event_timers = {}
PROGRESS_RATE_PROPERTIES = {
    "PSD Export": "cryptomatte_psd_seconds_per_mp_layer",
    "Low Memory Export": "cryptomatte_low_memory_seconds_per_mp_layer",
}


def _iface(message):
    return bpy.app.translations.pgettext_iface(message)


def _tip(message):
    return bpy.app.translations.pgettext_tip(message)


BLENDER_TO_PS_BLEND = {
    "MIX": b"norm", "DARKEN": b"dark", "MULTIPLY": b"mul ", "BURN": b"idiv",
    "LIGHTEN": b"lite", "SCREEN": b"scrn", "DODGE": b"div ", "ADD": b"lddg",
    "OVERLAY": b"over", "SOFT_LIGHT": b"sLit", "HARD_LIGHT": b"hLit",
    "DIFFERENCE": b"diff", "EXCLUSION": b"smud", "SUBTRACT": b"fsub",
    "DIVIDE": b"fdiv", "HUE": b"hue ", "SATURATION": b"sat ",
    "COLOR": b"colr", "VALUE": b"lum ", "PASS_THROUGH": b"pass",
}


def _tag_statusbar_redraw():
    window_manager = getattr(bpy.context, "window_manager", None)
    if window_manager is None:
        return
    for window in window_manager.windows:
        screen = window.screen
        if screen is None:
            continue
        for area in screen.areas:
            if area.type == "STATUSBAR":
                area.tag_redraw()


def _sync_export_progress_event_timers(enabled):
    window_manager = getattr(bpy.context, "window_manager", None)
    if window_manager is None:
        if not enabled:
            export_progress_event_timers.clear()
        return

    live_windows = set()
    if enabled and not bpy.app.background:
        for window in tuple(window_manager.windows):
            window_key = window.as_pointer()
            live_windows.add(window_key)
            if window_key in export_progress_event_timers:
                continue
            try:
                export_progress_event_timers[window_key] = window_manager.event_timer_add(
                    0.25,
                    window=window,
                )
            except (RuntimeError, TypeError):
                continue

    for window_key, timer in tuple(export_progress_event_timers.items()):
        if enabled and window_key in live_windows:
            continue
        try:
            window_manager.event_timer_remove(timer)
        except (ReferenceError, RuntimeError):
            pass
        export_progress_event_timers.pop(window_key, None)


def _export_progress_key(scene, phase):
    return (
        phase,
        scene.name,
        scene.render.resolution_x,
        scene.render.resolution_y,
        scene.render.resolution_percentage,
        bool(getattr(scene, "cryptomatte_use_exr", False)),
        bool(getattr(scene, "cryptomatte_use_psd", False)),
    )


def _progress_work_size(scene, layer_count):
    width = max(1, round(scene.render.resolution_x * scene.render.resolution_percentage / 100.0))
    height = max(1, round(scene.render.resolution_y * scene.render.resolution_percentage / 100.0))
    return width * height * max(1, layer_count) / 1_000_000.0


def _progress_redraw_timer():
    if export_progress["active"]:
        if not export_progress["ui_installed"]:
            _set_export_status_draw(True)
            export_progress["ui_installed"] = True
        _sync_export_progress_event_timers(True)
        _tag_statusbar_redraw()
        return 0.25
    _sync_export_progress_event_timers(False)
    if export_progress["ui_installed"]:
        _set_export_status_draw(False)
        export_progress["ui_installed"] = False
        export_progress["workspace_names"] = ()
        _tag_statusbar_redraw()
    return None


def _set_export_status_draw(enabled):
    workspace_names = set()
    if enabled:
        window_manager = getattr(bpy.context, "window_manager", None)
        if window_manager is not None:
            workspace_names.update(
                window.workspace.name
                for window in window_manager.windows
                if window.workspace is not None
            )
        context_workspace = getattr(bpy.context, "workspace", None)
        if context_workspace is not None:
            workspace_names.add(context_workspace.name)
        export_progress["workspace_names"] = tuple(workspace_names)
    else:
        workspace_names.update(export_progress["workspace_names"])

    workspaces = getattr(bpy.data, "workspaces", None)
    if workspaces is None:
        return
    for workspace_name in workspace_names:
        workspace = workspaces.get(workspace_name)
        if workspace is not None:
            workspace.status_text_set(_draw_export_status if enabled else None)


def _begin_export_progress(scene, total=1, phase="Export", work_size=0.0):
    if export_progress["active"]:
        _end_export_progress()

    history_key = _export_progress_key(scene, phase)
    estimated_total = export_duration_history.get(history_key)
    rate_property = PROGRESS_RATE_PROPERTIES.get(phase)
    if estimated_total is None and rate_property and work_size > 0.0:
        learned_rate = max(0.0, float(getattr(scene, rate_property, 0.0)))
        if learned_rate > 0.0:
            estimated_total = learned_rate * work_size
    export_progress["started_at"] = time.perf_counter()
    export_progress.update({
        "active": True,
        "scene_name": scene.name,
        "completed": 0.0,
        "total": max(1.0, float(total)),
        "phase": phase,
        "history_key": history_key,
        "estimated_total": estimated_total,
        "work_size": max(0.0, float(work_size)),
    })
    if not bpy.app.timers.is_registered(_progress_redraw_timer):
        bpy.app.timers.register(_progress_redraw_timer, first_interval=0.1)


def _update_export_progress(completed, total=None):
    if not export_progress["active"]:
        return
    if total is not None:
        export_progress["total"] = max(1.0, float(total))
    export_progress["completed"] = max(0.0, float(completed))
    factor = min(1.0, export_progress["completed"] / export_progress["total"])
    if factor > 0.0:
        elapsed = max(0.001, time.perf_counter() - export_progress["started_at"])
        measured_total = elapsed / factor
        previous = export_progress["estimated_total"]
        export_progress["estimated_total"] = (
            measured_total
            if previous is None
            else previous * 0.65 + measured_total * 0.35
        )


def _end_export_progress():
    if not export_progress["active"]:
        return
    elapsed = max(0.0, time.perf_counter() - export_progress["started_at"])
    history_key = export_progress["history_key"]
    if history_key is not None and elapsed > 0.0:
        previous = export_duration_history.get(history_key)
        export_duration_history[history_key] = elapsed if previous is None else previous * 0.4 + elapsed * 0.6
    scene = getattr(getattr(bpy, "data", None), "scenes", {}).get(export_progress["scene_name"])
    rate_property = PROGRESS_RATE_PROPERTIES.get(export_progress["phase"])
    work_size = export_progress["work_size"]
    if scene is not None and rate_property and work_size > 0.0 and elapsed > 0.0:
        measured_rate = elapsed / work_size
        previous_rate = max(0.0, float(getattr(scene, rate_property, 0.0)))
        setattr(scene, rate_property, measured_rate if previous_rate <= 0.0 else previous_rate * 0.4 + measured_rate * 0.6)
    export_progress.update({
        "active": False,
        "scene_name": "",
        "started_at": 0.0,
        "completed": 0.0,
        "total": 1.0,
        "phase": "",
        "history_key": None,
        "estimated_total": None,
        "work_size": 0.0,
    })


def _draw_export_status(self, _context):
    if not export_progress["active"]:
        return
    elapsed = max(0.0, time.perf_counter() - export_progress["started_at"])
    completed = export_progress["completed"]
    total = export_progress["total"]
    factor = min(1.0, completed / total)
    estimated = export_progress["estimated_total"]
    elapsed_seconds = int(elapsed + 0.5)
    total_text = "--" if estimated is None else str(max(elapsed_seconds, int(estimated + 0.5)))
    percent = min(100, max(0, round(factor * 100.0)))

    layout = self.layout
    layout.template_input_status()
    layout.separator_spacer()
    row = layout.row(align=True)
    row.label(text="Exporting...", icon="RENDER_STILL")
    progress = row.row(align=True)
    progress.ui_units_x = 6
    progress.progress(factor=factor, type="BAR", text=f"{percent}%")
    row.label(text=f"{elapsed_seconds}s/{total_text}s", icon="TIME")
    layout.separator_spacer()
    layout.template_status_info()

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
    original_use_compositing = scene.render.use_compositing
    original_use_render_cache = scene.render.use_render_cache
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
        scene.render.use_compositing = True
        scene.render.use_render_cache = False
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
        scene.render.use_compositing = original_use_compositing
        scene.render.use_render_cache = original_use_render_cache
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


def _ensure_output_socket(tree, name, socket_type="NodeSocketColor"):
    if hasattr(tree, "interface"):
        for item in tree.interface.items_tree:
            if item.item_type == "SOCKET" and item.in_out == "OUTPUT" and item.name == name:
                return item
        return tree.interface.new_socket(name=name, in_out="OUTPUT", socket_type=socket_type)

    socket = tree.outputs.get(name)
    if socket:
        return socket

    return tree.outputs.new(socket_type, name)


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
        old_group_nodes = [
            node
            for node in tree.nodes
            if node.bl_idname == "CompositorNodeGroup"
            and node.node_tree
            and node.node_tree.name == group_name
        ]
        route_nodes = {
            node
            for node in tree.nodes
            if node.get(ROUTE_OWNER_MARKER) == group_name
        }
        frontier = list(old_group_nodes)
        while frontier:
            source = frontier.pop()
            for link in list(tree.links):
                target = link.to_node
                if link.from_node != source or target.bl_idname not in {
                    "NodeReroute",
                    "CompositorNodeViewer",
                    "NodeGroupOutput",
                }:
                    continue
                if target not in route_nodes:
                    route_nodes.add(target)
                    frontier.append(target)

        for node in route_nodes:
            tree.nodes.remove(node)
        for node in old_group_nodes:
            tree.nodes.remove(node)

    group = bpy.data.node_groups.get(group_name)
    if group:
        bpy.data.node_groups.remove(group, do_unlink=True)


def _remove_all_output_routes(tree):
    """Keep only one generated Viewer/Group Output route in the scene tree."""
    route_nodes = {
        node
        for node in tree.nodes
        if node.get(ROUTE_OWNER_MARKER) in {OBJECT_GROUP_NAME, MATERIAL_GROUP_NAME}
    }
    frontier = [
        node
        for node in tree.nodes
        if node.bl_idname == "CompositorNodeGroup"
        and node.node_tree
        and node.node_tree.name in {OBJECT_GROUP_NAME, MATERIAL_GROUP_NAME}
    ]
    while frontier:
        source = frontier.pop()
        for link in list(tree.links):
            target = link.to_node
            if link.from_node != source or target.bl_idname not in {
                "NodeReroute",
                "CompositorNodeViewer",
                "NodeGroupOutput",
            }:
                continue
            if target not in route_nodes:
                route_nodes.add(target)
                frontier.append(target)

    for node in route_nodes:
        tree.nodes.remove(node)


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
    suffix = "Object_IDchannel" if group_name == OBJECT_GROUP_NAME else "Material_IDchannel"
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


def _remove_all_generated_output_nodes():
    for group_name in (OBJECT_GROUP_NAME, MATERIAL_GROUP_NAME):
        group = bpy.data.node_groups.get(group_name)
        if group is not None:
            _remove_generated_output_nodes(group)


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
    if (
        getattr(scene, "cryptomatte_low_memory", False)
        or not getattr(scene, "cryptomatte_use_exr", False)
        or not layers
    ):
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
    if (
        getattr(scene, "cryptomatte_low_memory", False)
        or not getattr(scene, "cryptomatte_use_psd", False)
        or not layers
    ):
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
    scene = getattr(context, "scene", None) if context else None
    if scene is None:
        return

    _remove_all_generated_output_nodes()

    if not (getattr(scene, "cryptomatte_use_exr", False) or getattr(scene, "cryptomatte_use_psd", False)):
        return
    if getattr(scene, "cryptomatte_low_memory", False):
        return

    group_node = _active_viewer_group_node(scene)
    group = group_node.node_tree if group_node else None
    if group is None or group.name not in {OBJECT_GROUP_NAME, MATERIAL_GROUP_NAME}:
        return

    layers = _collect_exr_layers(group)
    _sync_exr_output_for_group(context, group, group.name, layers)
    _sync_psd_output_for_group(context, group, group.name, layers)


def _remember_scene_settings(scene, context):
    if remembered_settings_loading:
        return
    preferences = _addon_preferences(context)
    if preferences is None:
        return
    for scene_property, preference_property, default in REMEMBERED_SCENE_SETTINGS:
        setattr(
            preferences,
            preference_property,
            getattr(scene, scene_property, default),
        )
    preferences.remembered_settings_initialized = True


def _apply_remembered_scene_settings(scenes, context):
    global remembered_settings_loading
    preferences = _addon_preferences(context)
    if preferences is None or scenes is None:
        return

    if not preferences.remembered_settings_initialized:
        for _scene_property, preference_property, default in REMEMBERED_SCENE_SETTINGS:
            setattr(preferences, preference_property, default)
        preferences.remembered_settings_initialized = True

    remembered_settings_loading = True
    try:
        for scene in scenes:
            for scene_property, preference_property, _default in REMEMBERED_SCENE_SETTINGS:
                setattr(scene, scene_property, getattr(preferences, preference_property))
    finally:
        remembered_settings_loading = False


@persistent
def restore_remembered_scene_settings_after_load(_dummy):
    _apply_remembered_scene_settings(getattr(bpy.data, "scenes", None), bpy.context)


def _restore_remembered_scene_settings_timer():
    restore_remembered_scene_settings_after_load(None)
    return None


def update_remembered_scene_settings(self, context):
    _remember_scene_settings(self, context)


def update_exr_output_settings(self, context):
    _remember_scene_settings(self, context)
    sync_exr_outputs(context)


def _enable_low_memory_scene(scene):
    if not getattr(scene, "cryptomatte_low_memory_override_active", False):
        scene.cryptomatte_low_memory_previous_render_cache = scene.render.use_render_cache
        scene.cryptomatte_low_memory_override_active = True
    scene.render.use_render_cache = True
    _remove_all_generated_output_nodes()


def _disable_low_memory_scene(scene):
    if getattr(scene, "cryptomatte_low_memory_override_active", False):
        scene.render.use_render_cache = scene.cryptomatte_low_memory_previous_render_cache
        scene.cryptomatte_low_memory_override_active = False


def update_low_memory_settings(self, context):
    _remember_scene_settings(self, context)
    if getattr(self, "cryptomatte_low_memory", False):
        _enable_low_memory_scene(self)
    else:
        _disable_low_memory_scene(self)
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
    transform.setDisplay("sRGB")
    transform.setView("Standard")
    return {
        "config": config,
        "display_processor": config.getProcessor(transform).getDefaultCPUProcessor(),
        "source_processors": {},
        "exposure_scale": 1.0,
        "gamma": 1.0,
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


def export_psd_from_blender(psd_data, progress_callback=None):
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
    progress_total = len(flat_layers) * 6 + 1
    progress_completed = 0.0

    def notify_progress(units=1.0):
        nonlocal progress_completed
        progress_completed += units
        if progress_callback is not None:
            progress_callback(progress_completed, progress_total)

    for layer in flat_layers:
        if layer["is_marker"]:
            layers.append((layer, [struct.pack(">H", 0)] * 4))
            notify_progress(6)
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
                notify_progress(6)
                continue
            layer_width, layer_height, raw_channels = _read_local_image(
                path, bit_depth, color_context, layer.get("color_space", "")
            )
        notify_progress()
        if not width:
            width, height = layer_width, layer_height
        if (layer_width, layer_height) != (width, height):
            print(f"CryptoMatte ID Color: PSD layer size mismatch: {layer['name']}")
            notify_progress(5)
            continue
        composite = _composite_psd_layer(composite, raw_channels, width, height, bit_depth, layer)
        notify_progress()
        row_bytes = width * (2 if bit_depth == 16 else 1)
        compressed_channels = []
        for channel in raw_channels:
            compressed_channels.append(
                process_channel_data(channel, row_bytes, height, compression, use_psb)
            )
            notify_progress()
        layers.append((layer, compressed_channels))
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
    notify_progress()
    return True


# --- Serial low-memory export ---

def _render_cache_directory():
    configured = bpy.context.preferences.filepaths.render_cache_directory
    return bpy.path.abspath(configured) if configured else tempfile.gettempdir()


def _render_cache_snapshot():
    snapshot = {}
    for path in glob.glob(os.path.join(_render_cache_directory(), "cached_RR*.exr")):
        try:
            stat = os.stat(path)
            snapshot[path] = (stat.st_mtime_ns, stat.st_size)
        except OSError:
            pass
    return snapshot


def _cryptomatte_cache_info(path, group_name):
    image_input = oiio.ImageInput.open(path)
    if image_input is None:
        raise RuntimeError(f"Could not open Blender render cache: {path}")
    try:
        if not image_input.seek_subimage(0, 0):
            raise RuntimeError("The Blender render cache has no image data.")
        metadata = {attribute.name: attribute.value for attribute in image_input.spec().extra_attribs}
        pass_suffix = ".CryptoObject" if group_name == OBJECT_GROUP_NAME else ".CryptoMaterial"
        metadata_root = None
        pass_prefix = None
        for name, value in metadata.items():
            if name.endswith("/name") and str(value).endswith(pass_suffix):
                metadata_root = name.rsplit("/", 1)[0]
                pass_prefix = str(value)
                break
        if metadata_root is None:
            raise RuntimeError(f"{pass_suffix[1:]} was not found in Blender's render cache.")

        manifest_value = metadata.get(f"{metadata_root}/manifest", "{}")
        manifest = json.loads(str(manifest_value))
        parts = []
        width = height = 0
        subimage = 0
        while image_input.seek_subimage(subimage, 0):
            spec = image_input.spec()
            channel_map = {name.lower(): index for index, name in enumerate(spec.channelnames)}
            stems = {
                name.rsplit(".", 1)[0]
                for name in spec.channelnames
                if name.lower().startswith(pass_prefix.lower())
            }
            for stem in stems:
                suffix = stem[len(pass_prefix):]
                if not suffix.isdigit():
                    continue
                indices = [
                    channel_map.get(f"{stem}.{channel}".lower())
                    for channel in ("r", "g", "b", "a")
                ]
                if all(index is not None for index in indices):
                    parts.append((subimage, tuple(indices)))
                    width, height = spec.width, spec.height
            subimage += 1
        if not parts or width <= 0 or height <= 0:
            raise RuntimeError(f"No {pass_suffix[1:]} pixel channels were found in Blender's render cache.")
        return {
            "manifest": manifest,
            "parts": tuple(parts),
            "width": width,
            "height": height,
        }
    finally:
        image_input.close()


def _read_cryptomatte_mask(path, cache_info, target_id, progress_callback=None):
    height = cache_info["height"]
    width = cache_info["width"]
    if target_id is None:
        if progress_callback is not None:
            for _part in cache_info["parts"]:
                progress_callback()
        return np.zeros((height, width), dtype=np.bool_)

    image_input = oiio.ImageInput.open(path)
    if image_input is None:
        raise RuntimeError(f"Could not reopen Blender render cache: {path}")
    mask = np.zeros((height, width), dtype=np.bool_)
    try:
        for subimage, indices in cache_info["parts"]:
            if not image_input.seek_subimage(subimage, 0):
                raise RuntimeError(f"Could not read Cryptomatte cache part {subimage}.")
            spec = image_input.spec()
            pixels = np.asarray(
                image_input.read_image(oiio.FLOAT),
                dtype=np.float32,
            ).reshape((spec.height, spec.width, spec.nchannels))
            red, green, blue, alpha = indices
            mask |= pixels[:, :, red].view(np.uint32) == target_id
            mask |= pixels[:, :, blue].view(np.uint32) == target_id
            del pixels
            if progress_callback is not None:
                progress_callback()
        return mask
    finally:
        image_input.close()


class _LowMemoryEXRWriter:
    def __init__(self, output_path, width, height, layer_names):
        self.output_path = output_path
        self.temporary_path = output_path + ".lowmem.exr"
        self.specs = []
        for layer_name in layer_names:
            spec = oiio.ImageSpec(width, height, 4, oiio.HALF)
            spec.channelnames = [f"{layer_name}.{channel}" for channel in "RGBA"]
            spec.attribute("compression", "dwaa")
            spec.attribute("openexr:dwaCompressionLevel", 90.0)
            spec.attribute("oiio:ColorSpace", "scene_linear")
            spec.attribute("oiio:subimagename", layer_name)
            self.specs.append(spec)
        self.output = oiio.ImageOutput.create(self.temporary_path)
        if self.output is None or not self.output.open(self.temporary_path, tuple(self.specs)):
            raise RuntimeError(f"Could not create low-memory EXR: {self.temporary_path}")
        self.index = 0

    def write_layer(self, color, mask):
        if self.index > 0 and not self.output.open(
            self.temporary_path,
            self.specs[self.index],
            "AppendSubimage",
        ):
            raise RuntimeError(self.output.geterror())
        height, width = mask.shape
        pixels = np.empty((height, width, 4), dtype=np.float16)
        pixels[:, :, :3] = color
        pixels[:, :, 3] = mask
        if not self.output.write_image(pixels):
            raise RuntimeError(self.output.geterror())
        self.index += 1
        del pixels

    def finish(self):
        if self.output is not None:
            if not self.output.close():
                raise RuntimeError(self.output.geterror())
            self.output = None
        os.replace(self.temporary_path, self.output_path)

    def abort(self):
        if self.output is not None:
            self.output.close()
            self.output = None
        if os.path.isfile(self.temporary_path):
            os.remove(self.temporary_path)


class _LowMemoryPSDWriter:
    def __init__(self, scene, output_path, width, height):
        self.scene = scene
        self.output_path = output_path
        self.temporary_path = output_path + ".lowmem.psd"
        output_directory = os.path.dirname(output_path) or "."
        os.makedirs(output_directory, exist_ok=True)
        self.spool_directory = tempfile.mkdtemp(
            prefix=".cryptomatte_id_color_",
            dir=output_directory,
        )
        self.width = width
        self.height = height
        self.pixel_count = width * height
        self.color_context = _psd_color_context(scene)
        self.entries = []
        self.composite_rgb = np.zeros((height, width, 3), dtype=np.float32)
        self.composite_alpha = np.zeros((height, width), dtype=np.float32)

    def write_layer(self, layer_name, color, mask, progress_callback=None):
        sample = np.empty((1, 1, 4), dtype=np.float32)
        sample[0, 0, :3] = color
        sample[0, 0, 3] = 1.0
        encoded_sample = _encode_psd_rgba(sample, 8, self.color_context)
        rgb_values = [channel[0] for channel in encoded_sample[:3]]
        alpha_bytes = (np.asarray(mask, dtype=np.uint8) * 255).tobytes()
        if progress_callback is not None:
            progress_callback()
        spool_path = os.path.join(self.spool_directory, f"{len(self.entries):06d}.bin")
        channel_lengths = []
        with open(spool_path, "wb") as spool:
            for value in rgb_values:
                channel_data = process_channel_data(
                    bytes((value,)) * self.pixel_count,
                    self.width,
                    self.height,
                    "ZIP",
                    False,
                )
                channel_lengths.append(len(channel_data))
                spool.write(channel_data)
                del channel_data
                if progress_callback is not None:
                    progress_callback()
            alpha_data = process_channel_data(
                alpha_bytes,
                self.width,
                self.height,
                "ZIP",
                False,
            )
            channel_lengths.append(len(alpha_data))
            spool.write(alpha_data)
            del alpha_data
            if progress_callback is not None:
                progress_callback()

        display_color = np.asarray(rgb_values, dtype=np.float32) / 255.0
        self.composite_rgb[mask] = display_color
        self.composite_alpha[mask] = 1.0
        self.entries.append({
            "name": layer_name,
            "channel_lengths": tuple(channel_lengths),
            "spool_path": spool_path,
        })
        del sample, encoded_sample, alpha_bytes

    def finish(self):
        entries = list(reversed(self.entries))
        records = []
        channel_data_length = 0
        for entry in entries:
            layer = {
                "name": entry["name"],
                "folder_type": 0,
                "hide": False,
                "opacity": 1.0,
                "blend": "MIX",
            }
            record = bytearray()
            record.extend(struct.pack(">IIII", 0, 0, self.height, self.width))
            record.extend(struct.pack(">H", 4))
            for channel_id, length in zip((0, 1, 2, -1), entry["channel_lengths"]):
                record.extend(struct.pack(">hI", channel_id, length))
                channel_data_length += length
            record.extend(b"8BIM" + BLENDER_TO_PS_BLEND["MIX"])
            record.extend(bytes((255, 0, 8, 0)))
            extra = _layer_extra_data(layer)
            record.extend(struct.pack(">I", len(extra)))
            record.extend(extra)
            records.append(record)

        layer_info_length = 2 + sum(len(record) for record in records) + channel_data_length
        padded_layer_info_length = layer_info_length + layer_info_length % 2
        layer_mask_length = 4 + padded_layer_info_length + 4
        composite_channels = _encode_psd_composite(
            (self.composite_rgb, self.composite_alpha),
            8,
        )
        resolution = int(300.0 * 65536)
        resources = (
            b"8BIM"
            + struct.pack(">H", 1005)
            + b"\0\0"
            + struct.pack(">I", 16)
            + struct.pack(">IHHIHH", resolution, 1, 1, resolution, 1, 1)
        )
        try:
            icc = _icc_profile_bytes()
            resources += (
                b"8BIM"
                + struct.pack(">H", 1039)
                + b"\0\0"
                + struct.pack(">I", len(icc))
                + icc
                + (b"\0" if len(icc) % 2 else b"")
            )
        except Exception as error:
            print(f"CryptoMatte ID Color: ICC profile skipped: {error}")

        try:
            with open(self.temporary_path, "wb") as file_handle:
                file_handle.write(
                    struct.pack(
                        ">4sH6sHIIHH",
                        b"8BPS",
                        1,
                        b"\0" * 6,
                        4,
                        self.height,
                        self.width,
                        8,
                        3,
                    )
                )
                file_handle.write(struct.pack(">I", 0))
                file_handle.write(struct.pack(">I", len(resources)) + resources)
                file_handle.write(struct.pack(">I", layer_mask_length))
                file_handle.write(struct.pack(">I", layer_info_length))
                file_handle.write(struct.pack(">h", -len(entries)))
                for record in records:
                    file_handle.write(record)
                for entry in entries:
                    with open(entry["spool_path"], "rb") as spool:
                        shutil.copyfileobj(spool, file_handle, length=1024 * 1024)
                if layer_info_length % 2:
                    file_handle.write(b"\0")
                file_handle.write(struct.pack(">I", 0))
                file_handle.write(struct.pack(">H", 0))
                for channel in composite_channels:
                    file_handle.write(channel)
            os.replace(self.temporary_path, self.output_path)
        finally:
            shutil.rmtree(self.spool_directory, ignore_errors=True)

    def abort(self):
        shutil.rmtree(self.spool_directory, ignore_errors=True)
        if os.path.isfile(self.temporary_path):
            os.remove(self.temporary_path)


def _fail_low_memory_job(scene_name, error):
    state = low_memory_render_jobs.pop(scene_name, None)
    if state is None:
        return
    for writer_name in ("exr_writer", "psd_writer"):
        writer = state.get(writer_name)
        if writer is not None:
            writer.abort()
    _end_export_progress()
    print(f"CryptoMatte ID Color: Low-memory export failed: {error}")
    traceback.print_exc()


def _advance_low_memory_job(scene_name):
    state = low_memory_render_jobs.get(scene_name)
    scene = bpy.data.scenes.get(scene_name)
    if state is None or scene is None:
        return None

    def advance_work(units=1.0):
        state["work_completed"] += units
        _update_export_progress(state["work_completed"], state["work_total"])

    try:
        if state["phase"] == "WAIT_CACHE":
            candidates = []
            for path in glob.glob(os.path.join(_render_cache_directory(), "cached_RR*.exr")):
                try:
                    stat = os.stat(path)
                except OSError:
                    continue
                signature = (stat.st_mtime_ns, stat.st_size)
                if state["cache_snapshot"].get(path) != signature:
                    candidates.append((stat.st_mtime_ns, path, signature))
            if not candidates:
                if time.perf_counter() - state["started_at"] > 300.0:
                    raise RuntimeError("Blender's disk render cache was not created.")
                return 0.25

            _mtime, cache_path, signature = max(candidates)
            if state.get("cache_candidate") != (cache_path, signature):
                state["cache_candidate"] = (cache_path, signature)
                state["cache_stable_at"] = time.perf_counter()
                return 0.25
            if time.perf_counter() - state["cache_stable_at"] < 1.0:
                return 0.25

            cache_info = _cryptomatte_cache_info(cache_path, state["group_name"])
            state["cache_path"] = cache_path
            state["cache_info"] = cache_info
            output_directory = _exr_output_directory(scene)
            os.makedirs(output_directory, exist_ok=True)
            output_base = os.path.join(
                output_directory,
                _exr_output_name(state["group_name"]),
            )
            layer_names = [layer["name"] for layer in state["layers"]]
            if state["use_exr"]:
                state["exr_writer"] = _LowMemoryEXRWriter(
                    output_base + ".exr",
                    cache_info["width"],
                    cache_info["height"],
                    layer_names,
                )
            if state["use_psd"]:
                state["psd_writer"] = _LowMemoryPSDWriter(
                    scene,
                    output_base + ".psd",
                    cache_info["width"],
                    cache_info["height"],
                )
            units_per_layer = (
                len(cache_info["parts"])
                + (1 if state["use_exr"] else 0)
                + (5 if state["use_psd"] else 0)
            )
            state["work_total"] = 2 + len(state["layers"]) * units_per_layer
            state["phase"] = "LAYERS"
            advance_work()
            return 0.01

        index = state["layer_index"]
        if index < len(state["layers"]):
            layer = state["layers"][index]
            manifest_hex = state["cache_info"]["manifest"].get(layer["name"])
            target_id = int(manifest_hex, 16) if manifest_hex else None
            mask = _read_cryptomatte_mask(
                state["cache_path"],
                state["cache_info"],
                target_id,
                progress_callback=advance_work,
            )
            if state.get("exr_writer") is not None:
                state["exr_writer"].write_layer(layer["color"], mask)
                advance_work()
            if state.get("psd_writer") is not None:
                state["psd_writer"].write_layer(
                    layer["name"],
                    layer["color"],
                    mask,
                    progress_callback=advance_work,
                )
            state["layer_index"] += 1
            print(
                f"CryptoMatte ID Color: Low-memory layer "
                f"{state['layer_index']}/{len(state['layers'])}: {layer['name']}"
            )
            del mask
            gc.collect()
            return 0.01

        if state.get("exr_writer") is not None:
            state["exr_writer"].finish()
        if state.get("psd_writer") is not None:
            state["psd_writer"].finish()
        advance_work()
        _end_export_progress()
        low_memory_render_jobs.pop(scene_name, None)
        print("CryptoMatte ID Color: Low-memory serial export completed.")
        gc.collect()
        return None
    except Exception as error:
        _fail_low_memory_job(scene_name, error)
        return None


@persistent
def prepare_low_memory_render(scene):
    if (
        visibility_prepass_active
        or not getattr(scene, "cryptomatte_low_memory", False)
        or not (
            getattr(scene, "cryptomatte_use_exr", False)
            or getattr(scene, "cryptomatte_use_psd", False)
        )
    ):
        return
    group_node = _active_viewer_group_node(scene)
    group = group_node.node_tree if group_node else None
    if group is None or group.name not in {OBJECT_GROUP_NAME, MATERIAL_GROUP_NAME}:
        return

    layers = []
    for layer_name, _source_socket in _collect_exr_layers(group):
        color_socket = group_node.inputs.get(layer_name)
        color = tuple(color_socket.default_value[:3]) if color_socket else (1.0, 1.0, 1.0)
        layers.append({"name": layer_name, "color": color})
    if not layers:
        return

    scene.render.use_render_cache = True
    low_memory_render_jobs[scene.name] = {
        "phase": "RENDERING",
        "started_at": time.perf_counter(),
        "cache_snapshot": _render_cache_snapshot(),
        "group_name": group.name,
        "layers": layers,
        "layer_index": 0,
        "work_completed": 0.0,
        "work_total": (
            2
            + len(layers)
            * (
                1
                + (1 if scene.cryptomatte_use_exr else 0)
                + (5 if scene.cryptomatte_use_psd else 0)
            )
        ),
        "use_exr": bool(scene.cryptomatte_use_exr),
        "use_psd": bool(scene.cryptomatte_use_psd),
        "exr_writer": None,
        "psd_writer": None,
    }
    print(
        f"CryptoMatte ID Color: Low-memory mode will process "
        f"{len(layers)} layers serially from Blender's render cache."
    )


@persistent
def start_low_memory_export(scene):
    if visibility_prepass_active:
        return
    state = low_memory_render_jobs.get(scene.name)
    if state is None or state["phase"] != "RENDERING":
        return
    state["phase"] = "WAIT_CACHE"
    _begin_export_progress(
        scene,
        total=state["work_total"],
        phase="Low Memory Export",
        work_size=_progress_work_size(scene, len(state["layers"])),
    )
    existing_timer = state.get("timer")
    if existing_timer is None or not bpy.app.timers.is_registered(existing_timer):
        timer = lambda scene_name=scene.name: _advance_low_memory_job(scene_name)
        state["timer"] = timer
        bpy.app.timers.register(timer, first_interval=0.25)


@persistent
def cancel_low_memory_render(scene):
    if visibility_prepass_active:
        return
    low_memory_render_jobs.pop(scene.name, None)
    _end_export_progress()


# --- PSD post-render integration ---


@persistent
def export_psd_after_render(scene):
    if (
        visibility_prepass_active
        or getattr(scene, "cryptomatte_low_memory", False)
        or not getattr(scene, "cryptomatte_use_psd", False)
    ):
        return
    group_node = _active_viewer_group_node(scene)
    group = group_node.node_tree if group_node else None
    if group is None:
        _end_export_progress()
        return
    psd_nodes = sorted((node for node in group.nodes if node.get(PSD_OUTPUT_MARKER)), key=lambda node: node.name)
    if not psd_nodes:
        _end_export_progress()
        return
    _begin_export_progress(
        scene,
        total=len(psd_nodes) * 6 + 1,
        phase="PSD Export",
        work_size=_progress_work_size(scene, len(psd_nodes)),
    )
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
            }, progress_callback=_update_export_progress):
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
        _end_export_progress()


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

    _remove_all_output_routes(tree)
    route_offsets = (
        OBJECT_ROUTE_OFFSETS
        if group.name == OBJECT_GROUP_NAME
        else MATERIAL_ROUTE_OFFSETS
    )
    _ensure_output_socket(tree, OUTPUT_NAME)

    reroute = tree.nodes.new("NodeReroute")
    reroute.name = f"{group.name} Reroute"
    reroute[ROUTE_OWNER_MARKER] = group.name
    reroute[ROUTE_ROLE_MARKER] = "REROUTE"
    reroute.location = (
        group_x + route_offsets["REROUTE"][0],
        group_y + route_offsets["REROUTE"][1],
    )

    group_output_node = tree.nodes.new("NodeGroupOutput")
    group_output_node.name = f"{group.name} Group Output"
    group_output_node.label = "Group Output"
    group_output_node[ROUTE_OWNER_MARKER] = group.name
    group_output_node[ROUTE_ROLE_MARKER] = "GROUP_OUTPUT"
    group_output_node.location = (
        group_x + route_offsets["GROUP_OUTPUT"][0],
        group_y + route_offsets["GROUP_OUTPUT"][1],
    )
    try:
        group_output_node.is_active_output = True
    except (AttributeError, TypeError):
        pass

    viewer = tree.nodes.new("CompositorNodeViewer")
    viewer.name = f"{group.name} Viewer"
    viewer.label = "Viewer"
    viewer[ROUTE_OWNER_MARKER] = group.name
    viewer[ROUTE_ROLE_MARKER] = "VIEWER"
    viewer.location = (
        group_x + route_offsets["VIEWER"][0],
        group_y + route_offsets["VIEWER"][1],
    )
    for node in tree.nodes:
        if node.bl_idname == "CompositorNodeViewer":
            node.select = False
    viewer.select = True
    tree.nodes.active = viewer

    group_output = _socket_by_name(group_node.outputs, [OUTPUT_NAME], 0)
    reroute_input = _socket_by_name(reroute.inputs, ["Input"], 0)
    reroute_output = _socket_by_name(reroute.outputs, ["Output"], 0)
    output_input = _socket_by_name(group_output_node.inputs, [OUTPUT_NAME], 0)
    viewer_input = _socket_by_name(viewer.inputs, ["Image"], 0)

    if group_output and reroute_input:
        tree.links.new(group_output, reroute_input)
    if reroute_output and viewer_input:
        tree.links.new(reroute_output, viewer_input)
    if reroute_output and output_input:
        tree.links.new(reroute_output, output_input)

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


# --- Render ID settings ---

RENDER_SETTINGS_PROPERTIES = {
    "engine",
    "preview_pixel_size",
    "dither_intensity",
    "filter_size",
    "film_transparent",
    "use_freestyle",
    "threads",
    "threads_mode",
    "use_motion_blur",
    "motion_blur_shutter",
    "motion_blur_position",
    "hair_type",
    "hair_subdiv",
    "use_high_quality_normals",
    "anisotropic_filter",
    "use_compositing",
    "use_render_cache",
    "use_simplify",
    "simplify_subdivision",
    "simplify_child_particles",
    "simplify_subdivision_render",
    "simplify_child_particles_render",
    "simplify_volumes",
    "use_simplify_normals",
    "use_texture_cache",
    "use_auto_generate_texture_cache",
    "use_persistent_data",
    "compositor_device",
    "compositor_precision",
    "compositor_denoise_device",
    "compositor_denoise_preview_quality",
    "compositor_denoise_final_quality",
}


def _addon_preferences(context):
    preferences = getattr(context, "preferences", None) if context else None
    addons = getattr(preferences, "addons", None)
    addon = addons.get(ADDON_PACKAGE) if addons is not None else None
    return addon.preferences if addon is not None else None


def _snapshot_rna_values(data, allowed_properties=None):
    values = {}
    for prop in data.bl_rna.properties:
        identifier = prop.identifier
        if (
            identifier in {"rna_type", "name"}
            or identifier == "preview_pause"
            or identifier.startswith("debug_")
            or prop.is_readonly
            or prop.type in {"POINTER", "COLLECTION"}
            or (allowed_properties is not None and identifier not in allowed_properties)
        ):
            continue
        try:
            value = getattr(data, identifier)
            if prop.is_array:
                value = list(value)
            elif not isinstance(value, (bool, int, float, str)):
                continue
            json.dumps(value)
            values[identifier] = value
        except (AttributeError, TypeError, ValueError):
            continue
    return values


def _render_setting_targets(scene, view_layer):
    targets = {
        "scene.render": (scene.render, RENDER_SETTINGS_PROPERTIES),
        "scene.cycles": (getattr(scene, "cycles", None), None),
        "scene.view_settings": (scene.view_settings, None),
        "scene.display_settings": (scene.display_settings, None),
    }
    view_layer_cycles = getattr(view_layer, "cycles", None) if view_layer else None
    if view_layer_cycles is not None:
        targets["view_layer.cycles"] = (view_layer_cycles, None)
    return targets


def _capture_render_settings(scene, view_layer):
    snapshot = {"schema": 1, "settings": {}}
    for path, (target, allowed_properties) in _render_setting_targets(scene, view_layer).items():
        if target is not None:
            snapshot["settings"][path] = _snapshot_rna_values(target, allowed_properties)
    return snapshot


def _apply_rna_values(target, values, skip=()):
    applied = 0
    skipped = 0
    for identifier, value in values.items():
        if identifier in skip:
            continue
        try:
            setattr(target, identifier, value)
            applied += 1
        except (AttributeError, TypeError, ValueError):
            skipped += 1
    return applied, skipped


def _apply_render_settings(scene, view_layer, snapshot):
    settings = snapshot.get("settings", {}) if isinstance(snapshot, dict) else {}
    targets = _render_setting_targets(scene, view_layer)
    applied = 0
    skipped = 0

    render_values = settings.get("scene.render", {})
    engine = render_values.get("engine")
    if engine:
        try:
            scene.render.engine = engine
            applied += 1
        except (AttributeError, TypeError, ValueError):
            skipped += 1

    for path, values in settings.items():
        target_entry = targets.get(path)
        if target_entry is None or not isinstance(values, dict):
            skipped += len(values) if isinstance(values, dict) else 1
            continue
        target = target_entry[0]
        if target is None:
            skipped += len(values)
            continue
        result = _apply_rna_values(target, values, skip={"engine"} if path == "scene.render" else ())
        applied += result[0]
        skipped += result[1]
    return applied, skipped


def _apply_default_render_id_settings(scene):
    scene.render.engine = "CYCLES"
    scene.view_settings.gamma = 1.0
    scene.view_settings.exposure = 0.0
    scene.view_settings.look = "None"
    cycles = scene.cycles
    cycles.samples = 3
    cycles.use_denoising = False
    cycles.use_preview_denoising = False
    cycles.max_bounces = 1
    cycles.diffuse_bounces = 1
    cycles.glossy_bounces = 1
    cycles.transmission_bounces = 0
    cycles.volume_bounces = 0
    cycles.transparent_max_bounces = 1


def _load_saved_render_settings(preferences):
    if preferences is None or not preferences.render_id_settings_json:
        return None
    try:
        snapshot = json.loads(preferences.render_id_settings_json)
    except (TypeError, ValueError, json.JSONDecodeError):
        return None
    return snapshot if isinstance(snapshot, dict) and snapshot.get("schema") == 1 else None


def _render_setting_record_time(preferences):
    if preferences is None or preferences.render_id_recorded_at <= 0.0:
        return "Default setting"
    return time.strftime("%Y-%m-%d %H:%M", time.localtime(preferences.render_id_recorded_at))


def _restore_render_id_project_settings(scene):
    state = render_id_restore_snapshots.pop(scene.name, None)
    if state is None:
        return
    view_layer = scene.view_layers.get(state["view_layer_name"])
    _apply_render_settings(scene, view_layer, state["snapshot"])


@persistent
def restore_render_id_settings_after_render(scene):
    _restore_render_id_project_settings(scene)


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
            self.report({"ERROR"}, _iface(str(error)))
            return {"CANCELLED"}
        if not objects:
            self.report({"WARNING"}, _iface("No visible renderable objects found in the current view layer."))
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
                _iface("ObjectID was created, but CryptoObject00 was not found on the Render Layers node."),
            )
            return {"FINISHED"}

        self.report(
            {"INFO"},
            _iface("ObjectID created for {count} visible objects.").format(count=len(object_names)),
        )
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
            self.report({"ERROR"}, _iface(str(error)))
            return {"CANCELLED"}
        if not materials:
            self.report({"WARNING"}, _iface("No materials found on visible renderable objects."))
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
                _iface("Material ID was created, but CryptoMaterial00 was not found on the Render Layers node."),
            )
            return {"FINISHED"}

        self.report(
            {"INFO"},
            _iface("Material ID created for {count} visible materials.").format(count=len(material_names)),
        )
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
            self.report({"ERROR"}, _iface("Please select exactly one object before using Change ID."))
            return {"CANCELLED"}

        obj = selected[0]
        group_node = _active_viewer_group_node(context.scene)
        if not group_node:
            self.report(
                {"ERROR"},
                _iface("Connect ObjectID or Material ID to the Viewer before using Change ID."),
            )
            return {"CANCELLED"}

        input_names = _target_input_names_for_viewer_group(obj, group_node)
        if not input_names:
            self.report(
                {"ERROR"},
                _iface(
                    "Selected object has no matching input in the active {group_name} node group."
                ).format(group_name=group_node.node_tree.name),
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
            self.report({"ERROR"}, _iface("Selected object no longer exists."))
            return {"CANCELLED"}

        color = tuple(self.color)

        group_node = _active_viewer_group_node(context.scene)
        if not group_node or group_node.node_tree.name != self.group_name:
            self.report(
                {"ERROR"},
                _iface("The active Viewer connection changed. Run Change ID again."),
            )
            return {"CANCELLED"}

        input_names = _target_input_names_for_viewer_group(obj, group_node)
        if not input_names:
            self.report(
                {"ERROR"},
                _iface("No matching {group_name} input was found for the selected object.").format(
                    group_name=self.group_name
                ),
            )
            return {"CANCELLED"}

        changed = False
        for input_name in input_names:
            changed |= _set_group_node_input_color(group_node, input_name, color)

        if not changed:
            self.report(
                {"ERROR"},
                _iface("No editable {group_name} input was found for the selected object.").format(
                    group_name=self.group_name
                ),
            )
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
            self.report(
                {"INFO"},
                _iface("No ObjectID or Material ID node group with enough colors was found."),
            )
            return {"CANCELLED"}

        tree = _scene_compositor_tree(context.scene)
        if tree:
            tree.update_tag()

        self.report({"INFO"}, _iface("Random ID colors were reordered."))
        return {"FINISHED"}


class OBJECTID_OT_render_id_channel(Operator):
    bl_idname = "object_id.render_id_channel"
    bl_label = "Render ID Channel"
    bl_description = "Temporarily use low-cost parameter to render ID channels without changing project's settings."
    bl_options = {"REGISTER"}

    @classmethod
    def poll(cls, context):
        return context.scene is not None

    def execute(self, context):
        scene = context.scene
        if scene.name in render_id_restore_snapshots:
            self.report({"WARNING"}, _iface("A Render ID Channel render is already running."))
            return {"CANCELLED"}

        render_id_restore_snapshots[scene.name] = {
            "view_layer_name": context.view_layer.name,
            "snapshot": _capture_render_settings(scene, context.view_layer),
        }
        preferences = _addon_preferences(context)
        snapshot = _load_saved_render_settings(preferences)
        if snapshot is None:
            _apply_default_render_id_settings(scene)
        else:
            _applied, skipped = _apply_render_settings(scene, context.view_layer, snapshot)
            if skipped:
                self.report(
                    {"WARNING"},
                    _iface("{count} unavailable recorded render settings were skipped.").format(
                        count=skipped
                    ),
                )
        try:
            result = bpy.ops.render.render("INVOKE_DEFAULT")
        except RuntimeError as error:
            _restore_render_id_project_settings(scene)
            self.report({"ERROR"}, str(error))
            return {"CANCELLED"}
        if "CANCELLED" in result:
            _restore_render_id_project_settings(scene)
            return {"CANCELLED"}
        return {"FINISHED"}


class _OBJECTID_RenderSettingPopup:
    action = ""

    def invoke(self, context, _event):
        return context.window_manager.invoke_props_dialog(
            self,
            width=340,
            title=self.bl_label,
            confirm_text="Yes",
        )

    def draw(self, context):
        layout = self.layout
        if self.action == "RECORD":
            layout.label(text="Record the current Render Properties settings?")
            layout.label(text="This will replace the previously recorded settings.")
        else:
            preferences = _addon_preferences(context)
            if _load_saved_render_settings(preferences) is None:
                layout.label(text="Load the default low-cost Render ID settings?")
            else:
                layout.label(text="Load the last recorded Render Properties settings?")
            layout.label(text="This will change the current scene render settings.")

    def execute(self, context):
        preferences = _addon_preferences(context)
        if preferences is None:
            self.report({"ERROR"}, _iface("CryptoMatte ID Color preferences are unavailable."))
            return {"CANCELLED"}

        if self.action == "RECORD":
            snapshot = _capture_render_settings(context.scene, context.view_layer)
            preferences.render_id_settings_json = json.dumps(snapshot, separators=(",", ":"))
            preferences.render_id_recorded_at = time.time()
            self.report({"INFO"}, _iface("Render ID settings recorded."))
            return {"FINISHED"}

        snapshot = _load_saved_render_settings(preferences)
        if snapshot is None:
            _apply_default_render_id_settings(context.scene)
            self.report({"INFO"}, _iface("Default Render ID settings loaded."))
            return {"FINISHED"}

        applied, skipped = _apply_render_settings(context.scene, context.view_layer, snapshot)
        message = _iface("Loaded {count} recorded Render ID settings.").format(count=applied)
        if skipped:
            message += " " + _iface("{count} unavailable settings were skipped.").format(
                count=skipped
            )
        self.report({"INFO"}, message)
        return {"FINISHED"}


class OBJECTID_OT_load_render_setting(_OBJECTID_RenderSettingPopup, Operator):
    bl_idname = "object_id.load_render_setting"
    bl_label = "Load Render ID Setting"
    action = "LOAD"

    @classmethod
    def description(cls, context, _properties):
        record_time = _render_setting_record_time(_addon_preferences(context))
        if record_time == "Default setting":
            return _tip("Default setting")
        return _tip("Last recorded: {record_time}").format(record_time=record_time)


class OBJECTID_OT_record_render_setting(_OBJECTID_RenderSettingPopup, Operator):
    bl_idname = "object_id.record_render_setting"
    bl_label = "Record Render ID Setting"
    bl_description = "Record the current Render Properties settings for future Render ID Channel renders"
    action = "RECORD"


# --- Preferences and compositor sidebar UI ---

class CRYPTOMATTE_ID_COLOR_Preferences(AddonPreferences):
    bl_idname = ADDON_PACKAGE

    render_id_settings_json: StringProperty(default="", options={"HIDDEN"})
    render_id_recorded_at: FloatProperty(default=0.0, options={"HIDDEN"})
    remembered_settings_initialized: BoolProperty(default=False, options={"HIDDEN"})
    remembered_use_exr: BoolProperty(default=False, options={"HIDDEN"})
    remembered_use_psd: BoolProperty(default=False, options={"HIDDEN"})
    remembered_camera_visible_only: BoolProperty(default=True, options={"HIDDEN"})
    remembered_low_memory: BoolProperty(default=False, options={"HIDDEN"})
    remembered_output_path: StringProperty(
        default=DEFAULT_EXR_OUTPUT_DIR,
        subtype="DIR_PATH",
        options={"HIDDEN"},
    )

    def draw_shortcut_cell(self, layout, context, operator_idname, label_text):
        _keyconfig, _keymap, keymap_item = keymap_item_for_operator(context, operator_idname)
        if keymap_item is None:
            sync_keymaps()
            _keyconfig, _keymap, keymap_item = keymap_item_for_operator(context, operator_idname)
        if keymap_item is None:
            layout.label(
                text=_iface("{label}: shortcut not found").format(label=_iface(label_text)),
                icon="ERROR",
            )
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

        for index in range(0, 4, 2):
            row = layout.row(align=False)
            split = row.split(factor=0.5, align=False)
            columns = (split.column(align=True), split.column(align=True))
            for target, column in zip(SHORTCUT_TARGETS[index : index + 2], columns):
                operator_idname, label_text, _key_type, _modifiers = target
                self.draw_shortcut_cell(column, context, operator_idname, label_text)

        row = layout.row(align=True)
        split = row.split(factor=0.5, align=True)
        shortcut_column = split.column(align=True)
        operator_idname, label_text, _key_type, _modifiers = SHORTCUT_TARGETS[-1]
        self.draw_shortcut_cell(shortcut_column, context, operator_idname, label_text)
        button_split = split.split(factor=0.5, align=False)
        load_button = button_split.column(align=False)
        record_button = button_split.column(align=False)
        load_button.operator(
            "object_id.load_render_setting",
            text="Load Render ID Setting",
            emboss=True,
        )
        record_button.operator(
            "object_id.record_render_setting",
            text="Record Render ID Setting",
            emboss=True,
        )


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
        layout.prop(context.scene, "cryptomatte_low_memory", text="Reduce Memory Pressure")

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

        layout.operator("object_id.render_id_channel", text="Render ID Channel", icon="RENDER_STILL")



# --- Registration ---

classes = (
    CRYPTOMATTE_ID_COLOR_Preferences,
    OBJECTID_OT_create,
    OBJECTID_OT_create_material,
    OBJECTID_OT_change,
    OBJECTID_OT_random,
    OBJECTID_OT_render_id_channel,
    OBJECTID_OT_load_render_setting,
    OBJECTID_OT_record_render_setting,
    CRYPTOMATTE_ID_COLOR_PT_tools,
)


def register():
    bpy.app.translations.register(ADDON_PACKAGE, TRANSLATIONS)
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
        default=True,
        update=update_remembered_scene_settings,
    )
    bpy.types.Scene.cryptomatte_low_memory = BoolProperty(
        name="Reduce Memory Pressure",
        description="Process one ID layer at a time from Blender's disk render cache to reduce peak compositor memory use",
        default=False,
        update=update_low_memory_settings,
    )
    bpy.types.Scene.cryptomatte_low_memory_previous_compositing = BoolProperty(
        default=True,
        options={"HIDDEN"},
    )
    bpy.types.Scene.cryptomatte_low_memory_previous_render_cache = BoolProperty(
        default=False,
        options={"HIDDEN"},
    )
    bpy.types.Scene.cryptomatte_low_memory_override_active = BoolProperty(
        default=False,
        options={"HIDDEN"},
    )
    bpy.types.Scene.cryptomatte_psd_seconds_per_mp_layer = FloatProperty(
        default=0.0,
        min=0.0,
        options={"HIDDEN"},
    )
    bpy.types.Scene.cryptomatte_low_memory_seconds_per_mp_layer = FloatProperty(
        default=0.0,
        min=0.0,
        options={"HIDDEN"},
    )
    bpy.types.Scene.cryptomatte_exr_output_path = StringProperty(
        name="EXR Output Path",
        description="Folder for generated multilayer EXR files",
        default=DEFAULT_EXR_OUTPUT_DIR,
        subtype="DIR_PATH",
        update=update_exr_output_settings,
    )
    if prepare_low_memory_render not in bpy.app.handlers.render_pre:
        bpy.app.handlers.render_pre.append(prepare_low_memory_render)
    if start_low_memory_export not in bpy.app.handlers.render_complete:
        bpy.app.handlers.render_complete.append(start_low_memory_export)
    if export_psd_after_render not in bpy.app.handlers.render_complete:
        bpy.app.handlers.render_complete.append(export_psd_after_render)
    if restore_render_id_settings_after_render not in bpy.app.handlers.render_complete:
        bpy.app.handlers.render_complete.append(restore_render_id_settings_after_render)
    if cancel_low_memory_render not in bpy.app.handlers.render_cancel:
        bpy.app.handlers.render_cancel.append(cancel_low_memory_render)
    if restore_render_id_settings_after_render not in bpy.app.handlers.render_cancel:
        bpy.app.handlers.render_cancel.append(restore_render_id_settings_after_render)
    if invalidate_visibility_cache not in bpy.app.handlers.depsgraph_update_post:
        bpy.app.handlers.depsgraph_update_post.append(invalidate_visibility_cache)
    if restore_remembered_scene_settings_after_load not in bpy.app.handlers.load_post:
        bpy.app.handlers.load_post.append(restore_remembered_scene_settings_after_load)
    if not bpy.app.timers.is_registered(_restore_remembered_scene_settings_timer):
        bpy.app.timers.register(_restore_remembered_scene_settings_timer, first_interval=0.0)
    scenes = getattr(bpy.data, "scenes", None)
    if scenes is not None:
        for scene in scenes:
            if getattr(scene, "cryptomatte_low_memory", False):
                if getattr(scene, "cryptomatte_low_memory_override_active", False):
                    scene.render.use_compositing = scene.cryptomatte_low_memory_previous_compositing
                    scene.render.use_render_cache = scene.cryptomatte_low_memory_previous_render_cache
                    scene.cryptomatte_low_memory_override_active = False
                _enable_low_memory_scene(scene)
        sync_exr_outputs(bpy.context)
    sync_keymaps()


def unregister():
    unregister_keymaps()
    if bpy.app.timers.is_registered(_restore_remembered_scene_settings_timer):
        bpy.app.timers.unregister(_restore_remembered_scene_settings_timer)
    _end_export_progress()
    _sync_export_progress_event_timers(False)
    if bpy.app.timers.is_registered(_progress_redraw_timer):
        bpy.app.timers.unregister(_progress_redraw_timer)
    if export_progress["ui_installed"]:
        _set_export_status_draw(False)
        export_progress["ui_installed"] = False
        export_progress["workspace_names"] = ()
    scenes = getattr(bpy.data, "scenes", None)
    for scene_name, state in list(low_memory_render_jobs.items()):
        timer = state.get("timer")
        if timer is not None and bpy.app.timers.is_registered(timer):
            bpy.app.timers.unregister(timer)
        for writer_name in ("exr_writer", "psd_writer"):
            writer = state.get(writer_name)
            if writer is not None:
                writer.abort()
    low_memory_render_jobs.clear()
    if scenes is not None:
        for scene in scenes:
            _restore_render_id_project_settings(scene)
        for scene in scenes:
            _disable_low_memory_scene(scene)
    render_id_restore_snapshots.clear()
    while prepare_low_memory_render in bpy.app.handlers.render_pre:
        bpy.app.handlers.render_pre.remove(prepare_low_memory_render)
    while start_low_memory_export in bpy.app.handlers.render_complete:
        bpy.app.handlers.render_complete.remove(start_low_memory_export)
    while export_psd_after_render in bpy.app.handlers.render_complete:
        bpy.app.handlers.render_complete.remove(export_psd_after_render)
    while restore_render_id_settings_after_render in bpy.app.handlers.render_complete:
        bpy.app.handlers.render_complete.remove(restore_render_id_settings_after_render)
    while cancel_low_memory_render in bpy.app.handlers.render_cancel:
        bpy.app.handlers.render_cancel.remove(cancel_low_memory_render)
    while restore_render_id_settings_after_render in bpy.app.handlers.render_cancel:
        bpy.app.handlers.render_cancel.remove(restore_render_id_settings_after_render)
    while invalidate_visibility_cache in bpy.app.handlers.depsgraph_update_post:
        bpy.app.handlers.depsgraph_update_post.remove(invalidate_visibility_cache)
    while restore_remembered_scene_settings_after_load in bpy.app.handlers.load_post:
        bpy.app.handlers.load_post.remove(restore_remembered_scene_settings_after_load)
    for prop_name in (
        "cryptomatte_use_exr",
        "cryptomatte_use_psd",
        "cryptomatte_camera_visible_only",
        "cryptomatte_low_memory",
        "cryptomatte_low_memory_previous_compositing",
        "cryptomatte_low_memory_previous_render_cache",
        "cryptomatte_low_memory_override_active",
        "cryptomatte_psd_seconds_per_mp_layer",
        "cryptomatte_low_memory_seconds_per_mp_layer",
        "cryptomatte_exr_output_path",
    ):
        if hasattr(bpy.types.Scene, prop_name):
            delattr(bpy.types.Scene, prop_name)

    for cls in reversed(classes):
        bpy.utils.unregister_class(cls)
    bpy.app.translations.unregister(ADDON_PACKAGE)


if __name__ == "__main__":
    register()
