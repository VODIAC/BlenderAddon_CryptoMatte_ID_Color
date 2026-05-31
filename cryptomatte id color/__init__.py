bl_info = {
    "name": "CryptoMatte ID Color",
    "author": "61+",
    "version": (1, 0, 4),
    "blender": (4, 5, 0),
    "location": "Compositor > Sidebar > Tool",
    "description": "Generate real-time ID color compositor nodes using Cryptomatte.",
    "category": "Compositing",
}

import colorsys
import os
import random

import bpy
from bpy.props import BoolProperty, FloatVectorProperty, StringProperty
from bpy.types import AddonPreferences, Operator, Panel


OBJECT_GROUP_NAME = "ObjectID"
MATERIAL_GROUP_NAME = "Material ID"
ID_INPUT_NAME = "ID input"
OUTPUT_NAME = "Image"
ADDON_PACKAGE = __package__ or __name__
EXR_OUTPUT_MARKER = "cryptomatte_id_color_exr_output"
DEFAULT_EXR_OUTPUT_DIR = "/tmp\\"

SHORTCUT_TARGETS = (
    ("object_id.create", "Object ID", "O", {"alt": True}),
    ("object_id.create_material", "Material ID", "M", {"alt": True}),
    ("object_id.change", "Change ID", "PERIOD", {"alt": True}),
    ("object_id.random", "Random ID", "COMMA", {"alt": True}),
)

SHORTCUT_KEYMAP_NAME = "Window"
SHORTCUT_KEYMAP_SPACE_TYPE = "EMPTY"

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


def _visible_materials(context):
    materials = {}
    for obj in _visible_renderable_objects(context):
        for slot in obj.material_slots:
            material = slot.material
            if material:
                materials[material.name] = material

    return [materials[name] for name in sorted(materials.keys(), key=str.lower)]


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


def _remove_exr_output_nodes(group):
    for node in list(group.nodes):
        if node.bl_idname == "CompositorNodeOutputFile" and node.get(EXR_OUTPUT_MARKER):
            group.nodes.remove(node)


def _configure_exr_format(node):
    node.format.media_type = "MULTI_LAYER_IMAGE"
    node.format.file_format = "OPEN_EXR_MULTILAYER"
    node.format.color_depth = "16"
    node.format.exr_codec = "DWAA"
    node.format.quality = 90


def _sync_exr_output_for_group(context, group, group_name, layers):
    _remove_exr_output_nodes(group)
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

    for layer_name, source_socket in layers:
        item = output_node.file_output_items.new(socket_type="RGBA", name=layer_name)
        item.save_as_render = True
        input_socket = output_node.inputs.get(item.name)
        if source_socket and input_socket:
            group.links.new(source_socket, input_socket)

    return output_node


def _linked_node_from_socket(group, socket, node_type=None):
    for link in group.links:
        if link.from_socket == socket:
            if node_type is None or link.to_node.bl_idname == node_type:
                return link.to_node
    return None


def _collect_exr_layers(group):
    layers = []
    crypto_nodes = sorted(
        (node for node in group.nodes if node.bl_idname == "CompositorNodeCryptomatteV2"),
        key=lambda item: item.location.y,
        reverse=True,
    )
    for crypto in crypto_nodes:
        matte_output = _socket_by_name(crypto.outputs, ["Matte"], 1)
        gamma = _linked_node_from_socket(group, matte_output, "ShaderNodeGamma") if matte_output else None
        gamma_output = _socket_by_name(gamma.outputs, ["Image", "Color"], 0) if gamma else None
        set_alpha = _linked_node_from_socket(group, gamma_output, "CompositorNodeSetAlpha") if gamma_output else None
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
            _remove_exr_output_nodes(group)

    if not getattr(scene, "cryptomatte_use_exr", False):
        return

    group_node = _active_viewer_group_node(scene)
    group = group_node.node_tree if group_node else None
    if group is None or group.name not in {OBJECT_GROUP_NAME, MATERIAL_GROUP_NAME}:
        return

    _sync_exr_output_for_group(context, group, group.name, _collect_exr_layers(group))


def update_exr_output_settings(self, context):
    sync_exr_outputs(context)


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
        y = -index * 210

        crypto = nodes.new("CompositorNodeCryptomatteV2")
        crypto.location = (-540, y)
        _configure_cryptomatte_node(crypto, scene, view_layer, id_name, layer_name)

        set_alpha = nodes.new("CompositorNodeSetAlpha")
        set_alpha.location = (-180, y)

        gamma = nodes.new("ShaderNodeGamma")
        gamma.location = (-360, y - 40)

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
        alpha_over.location = (150, y + 105)
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

    group_node = tree.nodes.new("CompositorNodeGroup")
    group_node.node_tree = group
    group_node.name = group.name
    group_node.label = group.name
    group_node.location = (-60, location_y)

    crypto_socket = _crypto_socket(render_layer, crypto_socket_name)
    id_input = _socket_by_name(group_node.inputs, [ID_INPUT_NAME], 0)
    if crypto_socket and id_input:
        tree.links.new(crypto_socket, id_input)

    _ensure_output_socket(tree, OUTPUT_NAME)
    group_output_node = _find_or_create_node(tree, "NodeGroupOutput", "Group Output", (380, 210))
    viewer = _find_or_create_node(tree, "CompositorNodeViewer", "Viewer", (380, 0))

    group_output = _socket_by_name(group_node.outputs, [OUTPUT_NAME], 0)
    output_input = _socket_by_name(group_output_node.inputs, [OUTPUT_NAME], 0)
    viewer_input = _socket_by_name(viewer.inputs, ["Image"], 0)

    if group_output and output_input:
        tree.links.new(group_output, output_input)
    if group_output and viewer_input:
        for link in list(tree.links):
            if link.to_socket == viewer_input:
                tree.links.remove(link)
        tree.links.new(group_output, viewer_input)

    return crypto_socket is not None


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


def _active_viewer_group_node(scene):
    tree = _scene_compositor_tree(scene)
    if not tree:
        return None

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
            return group_node

    return None


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


def get_addon_preferences(context):
    addon = context.preferences.addons.get(ADDON_PACKAGE)
    return addon.preferences if addon else None


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

        objects = _visible_renderable_objects(context)
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

        materials = _visible_materials(context)
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
        row.operator("object_id.create", text="Object ID", icon="OBJECT_DATA")
        row.operator("object_id.create_material", text="Material ID", icon="MATERIAL_DATA")

        row = layout.row(align=True)
        row.operator("object_id.change", text="Change ID", icon="COLOR")
        row.operator("object_id.random", text="Random ID", icon="FILE_REFRESH")

        row = layout.row(align=True)
        row.prop(context.scene, "cryptomatte_use_exr", text="Use EXR")
        path_row = row.row(align=True)
        path_row.enabled = context.scene.cryptomatte_use_exr
        path_row.prop(context.scene, "cryptomatte_exr_output_path", text="")


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
        name="Use EXR",
        description="Create a multilayer EXR output for the active Object ID or Material ID group",
        default=False,
        update=update_exr_output_settings,
    )
    bpy.types.Scene.cryptomatte_exr_output_path = StringProperty(
        name="EXR Output Path",
        description="Folder for generated multilayer EXR files",
        default=DEFAULT_EXR_OUTPUT_DIR,
        subtype="DIR_PATH",
        update=update_exr_output_settings,
    )
    sync_keymaps()


def unregister():
    unregister_keymaps()
    for prop_name in ("cryptomatte_use_exr", "cryptomatte_exr_output_path"):
        if hasattr(bpy.types.Scene, prop_name):
            delattr(bpy.types.Scene, prop_name)

    for cls in reversed(classes):
        bpy.utils.unregister_class(cls)


if __name__ == "__main__":
    register()
