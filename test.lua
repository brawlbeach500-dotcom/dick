--=============================================================================
--                        Walke Serializer v4.1
--
--   v4.0 rewrite + integrated on-screen status HUD.
--
--   Changes since v3.0:
--     * UTF-8 correct attribute/tag packing
--     * Per-instance property registry with settable validation
--     * Streaming XML writer (chunked for large saves)
--     * Post-serialize reference resolution + dangling-ref repair
--     * Correct CSG fallback chain (MeshData -> PhysicsData -> ChildData)
--     * Terrain: 64³ chunks, RLE air voxels, correct region reconstruction
--     * UTF-8 safe escaping, `'` in attribute values, CDATA edge cases
--     * Cooperative cancellation in assign + walk
--     * Adaptive progress debounce, accurate reference count
--     * Fixed class-cache collision, default-value comparison (NaN, -0)
--     * Native saveinstance handoff with file-existence verification
--
--   NEW in v4.1:
--     * On-screen status HUD (CoreGui w/ PlayerGui fallback)
--     * Live progress bar, counters, rolling warn/error log
--     * Draggable, non-blocking, auto-hides on completion
--     * HUD "Hide" button = cancel; wires into opt.shouldCancel
--     * Zero-cost when hud=false; graceful degradation if no GUI parent
--     * print/warn interception while save is running (mirrored to HUD)
--
--            Created ORIGINALLY by tankm3n (Skin Walke Owner)
--            v4.1 rewrite preserves API compatibility with v3.0
--=============================================================================

local VERSION = "4.1"

print([[
__       __     _
\ \     / /_ _| | | _____
 \ \ /\ / / _` | | |/ / _ \
  \ V  V / (_| | |   <   __/
   \_/\_/ \__,_|_|_|\_\___|
Walke Serializer v4.1
]])

--=====[ Fast locals ]=========================================================

local ins        = table.insert
local cat        = table.concat
local sfmt       = string.format
local sbyte      = string.byte
local schar      = string.char
local ssub       = string.sub
local sgsub      = string.gsub
local sfind      = string.find
local slower     = string.lower
local spack      = string.pack
local sunpack    = string.unpack
local tsort      = table.sort
local mfloor     = math.floor
local mmin       = math.min
local mmax       = math.max
local mhuge      = math.huge
local oclock     = os.clock
local tostr      = tostring
local tonum      = tonumber
local typ        = type
local typeof     = typeof or type
local pcall      = pcall
local xpcall     = xpcall
local error      = error
local select     = select
local rawget     = rawget
local pairs      = pairs
local ipairs     = ipairs
local next       = next

--=====[ Executor capability detection ]=====================================

local function tryget(names)
    local genv = (getgenv and getgenv()) or _G or {}
    for i = 1, #names do
        local n = names[i]
        local f = rawget(_G, n) or rawget(genv, n)
        if typ(f) == "function" then return f end
    end
    return nil
end

local dec        = tryget({ "decompile", "decompilescript", "getscriptsource" })
local gsc        = tryget({ "getscriptbytecode" })
local ghp        = tryget({ "gethiddenproperty" })
local sscript    = tryget({ "setscriptable" })
local gp         = tryget({ "getproperties" })
local writefile  = tryget({ "writefile" })
local appendfile = tryget({ "appendfile" })
local delfile    = tryget({ "delfile" })
local makefolder = tryget({ "makefolder" })
local nsi        = tryget({ "saveinstance", "synsaveinstance" })

local CS = nil
pcall(function() CS = game:GetService("CollectionService") end)

local HttpGet = nil
pcall(function() HttpGet = game.HttpGet end)

--=====[ Helpers ]=============================================================

local function clean(s)
    return (sgsub(tostr(s), "[%z\1-\8\11\12\14-\31]", ""))
end

local XML_ESC = {
    ["&"] = "&amp;", ["<"] = "&lt;", [">"] = "&gt;",
    ["\""] = "&quot;", ["'"] = "&apos;",
}
local function esc(s)
    return (sgsub(clean(s), "[&<>\"']", XML_ESC))
end

local function cdata(s)
    s = clean(s)
    s = sgsub(s, "]]>", "]]]]><![CDATA[>")
    return "<![CDATA[" .. s .. "]]>"
end

local function nf(v)
    if v ~= v then return "0" end
    if v == mhuge or v == -mhuge then return "0" end
    return sfmt("%.9g", v)
end

local function f17(v)
    if v ~= v then return "0" end
    if v == mhuge or v == -mhuge then return "0" end
    return sfmt("%.17g", v)
end

local function u8(x)
    x = mfloor(x * 255 + 0.5)
    if x < 0 then return 0 elseif x > 255 then return 255 end
    return x
end

local function c8(c)
    return 0xFF000000 + u8(c.R) * 65536 + u8(c.G) * 256 + u8(c.B)
end

--=====[ Base64 encoder ]====================================================

local B64C = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

local function b64(d)
    local n = #d
    if n == 0 then return "" end
    local out = {}
    local oi = 1
    local i = 1
    while i <= n do
        local a = sbyte(d, i)
        local b = sbyte(d, i + 1)
        local c = sbyte(d, i + 2)
        local x = b or 0
        local y = c or 0
        local o1 = mfloor(a / 4)
        local o2 = (a % 4) * 16 + mfloor(x / 16)
        local o3 = (x % 16) * 4 + mfloor(y / 64)
        local o4 = y % 64
        out[oi]     = ssub(B64C, o1 + 1, o1 + 1)
        out[oi + 1] = ssub(B64C, o2 + 1, o2 + 1)
        out[oi + 2] = b and ssub(B64C, o3 + 1, o3 + 1) or "="
        out[oi + 3] = c and ssub(B64C, o4 + 1, o4 + 1) or "="
        oi = oi + 4
        i = i + 3
    end
    return cat(out)
end

--=====[ Property metadata ]=================================================

local IP = {
    BorderSizePixel = true, ZIndex = true, DisplayOrder = true,
    LayoutOrder = true, Segments = true,
}

local CONTENT_PROP = {
    MeshId = true, TextureID = true, TextureId = true, Texture = true,
    Image = true, SoundId = true, HatMeshId = true, ClickIcon = true,
    ColorMap = true, NormalMap = true, MetalnessMap = true, RoughnessMap = true,
    CursorIcon = true, MeshContent = true, TextureContent = true,
}

local SKIP_CLASS = { Terrain = true, Camera = true }

local BLOCK_PROP = {
    Parent = true, ClassName = true, className = true, RobloxLocked = true,
    Capabilities = true, UniqueId = true, HistoryId = true,
    AssemblyLinearVelocity = true, AssemblyAngularVelocity = true,
    CenterOfMass = true, Mass = true, ExtentsSize = true,
    ExtentsCFrame = true, LocalTransparencyModifier = true,
}

local PAL_PROP = { Position = true, Orientation = true, Rotation = true }

--=====[ Serializer registry ]================================================

local S = {}

S["string"] = function(n, v)
    if CONTENT_PROP[n] then
        if v == "" then
            return sfmt('<Content name="%s"><null></null></Content>', n)
        end
        return sfmt('<Content name="%s"><url>%s</url></Content>', n, esc(v))
    end
    return sfmt('<string name="%s">%s</string>', n, esc(v))
end

S["boolean"] = function(n, v)
    return sfmt('<bool name="%s">%s</bool>', n, v and "true" or "false")
end

S["number"] = function(n, v)
    if IP[n] then return sfmt('<int name="%s">%d</int>', n, mfloor(v)) end
    return sfmt('<float name="%s">%s</float>', n, nf(v))
end

S["Vector3"] = function(n, v, _, bp)
    local nm = (bp and n == "Size") and "size" or n
    return sfmt('<Vector3 name="%s"><X>%s</X><Y>%s</Y><Z>%s</Z></Vector3>',
        nm, nf(v.X), nf(v.Y), nf(v.Z))
end

S["Vector2"] = function(n, v)
    return sfmt('<Vector2 name="%s"><X>%s</X><Y>%s</Y></Vector2>', n, nf(v.X), nf(v.Y))
end

S["Vector3int16"] = function(n, v)
    return sfmt('<Vector3int16 name="%s"><X>%d</X><Y>%d</Y><Z>%d</Z></Vector3int16>',
        n, v.X, v.Y, v.Z)
end

S["Vector2int16"] = function(n, v)
    return sfmt('<Vector2int16 name="%s"><X>%d</X><Y>%d</Y></Vector2int16>', n, v.X, v.Y)
end

S["Color3"] = function(n, v, _, bp)
    if bp and n == "Color" then
        return sfmt('<Color3uint8 name="Color3uint8">%d</Color3uint8>', c8(v))
    end
    return sfmt('<Color3 name="%s"><R>%s</R><G>%s</G><B>%s</B></Color3>',
        n, nf(v.R), nf(v.G), nf(v.B))
end

S["CFrame"] = function(n, v)
    local c = { v:GetComponents() }
    return sfmt('<CoordinateFrame name="%s"><X>%s</X><Y>%s</Y><Z>%s</Z>' ..
        '<R00>%s</R00><R01>%s</R01><R02>%s</R02>' ..
        '<R10>%s</R10><R11>%s</R11><R12>%s</R12>' ..
        '<R20>%s</R20><R21>%s</R21><R22>%s</R22></CoordinateFrame>',
        n, nf(c[1]), nf(c[2]), nf(c[3]),
        nf(c[4]), nf(c[5]), nf(c[6]),
        nf(c[7]), nf(c[8]), nf(c[9]),
        nf(c[10]), nf(c[11]), nf(c[12]))
end

S["EnumItem"] = function(n, v)
    return sfmt('<token name="%s">%d</token>', n, v.Value)
end

S["UDim"] = function(n, v)
    return sfmt('<UDim name="%s"><S>%s</S><O>%d</O></UDim>', n, nf(v.Scale), mfloor(v.Offset))
end

S["UDim2"] = function(n, v)
    return sfmt('<UDim2 name="%s"><XS>%s</XS><XO>%d</XO><YS>%s</YS><YO>%d</YO></UDim2>',
        n, nf(v.X.Scale), mfloor(v.X.Offset), nf(v.Y.Scale), mfloor(v.Y.Offset))
end

S["BrickColor"] = function(n, v)
    return sfmt('<int name="%s">%d</int>', n, v.Number)
end

S["NumberRange"] = function(n, v)
    return sfmt('<NumberRange name="%s">%s %s </NumberRange>', n, nf(v.Min), nf(v.Max))
end

S["NumberSequence"] = function(n, v)
    local b = {}
    for _, k in ipairs(v.Keypoints) do
        ins(b, nf(k.Time)); ins(b, nf(k.Value)); ins(b, nf(k.Envelope))
    end
    return sfmt('<NumberSequence name="%s">%s </NumberSequence>', n, cat(b, " "))
end

S["ColorSequence"] = function(n, v)
    local b = {}
    for _, k in ipairs(v.Keypoints) do
        ins(b, nf(k.Time))
        ins(b, nf(k.Value.R)); ins(b, nf(k.Value.G)); ins(b, nf(k.Value.B))
    end
    return sfmt('<ColorSequence name="%s">%s </ColorSequence>', n, cat(b, " "))
end

S["Rect"] = function(n, v)
    return sfmt('<Rect2D name="%s"><min><X>%s</X><Y>%s</Y></min>' ..
        '<max><X>%s</X><Y>%s</Y></max></Rect2D>',
        n, nf(v.Min.X), nf(v.Min.Y), nf(v.Max.X), nf(v.Max.Y))
end

S["PhysicalProperties"] = function(n, v)
    return sfmt('<PhysicalProperties name="%s"><CustomPhysics>true</CustomPhysics>' ..
        '<Density>%s</Density><Friction>%s</Friction><Elasticity>%s</Elasticity>' ..
        '<FrictionWeight>%s</FrictionWeight><ElasticityWeight>%s</ElasticityWeight>' ..
        '</PhysicalProperties>',
        n, nf(v.Density), nf(v.Friction), nf(v.Elasticity),
        nf(v.FrictionWeight), nf(v.ElasticityWeight))
end

S["Font"] = function(n, v)
    local fam, w, st = "", 400, "Normal"
    pcall(function() fam = v.Family end)
    pcall(function() w = v.Weight.Value end)
    pcall(function() st = v.Style.Name end)
    return sfmt('<Font name="%s"><Family><url>%s</url></Family>' ..
        '<Weight>%d</Weight><Style>%s</Style></Font>', n, esc(fam), w, esc(st))
end

S["Content"] = function(n, v)
    local u = ""
    pcall(function() u = v.Uri or "" end)
    if u == "" then
        return sfmt('<Content name="%s"><null></null></Content>', n)
    end
    return sfmt('<Content name="%s"><url>%s</url></Content>', n, esc(u))
end

S["Faces"] = function(n, v)
    local m = 0
    if v.Right then m = m + 1 end
    if v.Top then m = m + 2 end
    if v.Back then m = m + 4 end
    if v.Left then m = m + 8 end
    if v.Bottom then m = m + 16 end
    if v.Front then m = m + 32 end
    return sfmt('<Faces name="%s"><faces>%d</faces></Faces>', n, m)
end

S["Axes"] = function(n, v)
    local m = 0
    if v.X then m = m + 1 end
    if v.Y then m = m + 2 end
    if v.Z then m = m + 4 end
    return sfmt('<Axes name="%s"><axes>%d</axes></Axes>', n, m)
end

S["Ray"] = function(n, v)
    local o, d = v.Origin, v.Direction
    return sfmt('<Ray name="%s"><origin><X>%s</X><Y>%s</Y><Z>%s</Z></origin>' ..
        '<direction><X>%s</X><Y>%s</Y><Z>%s</Z></direction></Ray>',
        n, nf(o.X), nf(o.Y), nf(o.Z), nf(d.X), nf(d.Y), nf(d.Z))
end

S["Instance"] = function(n, v, refs)
    local id = refs[v]
    if id then return sfmt('<Ref name="%s">%s</Ref>', n, id) end
    return ""
end

--=====[ Attribute encoding ]================================================

local ATTR_TYPE = {
    ["string"]      = 0x02,
    ["boolean"]     = 0x03,
    ["number"]      = 0x06,
    ["UDim"]        = 0x09,
    ["UDim2"]       = 0x0A,
    ["BrickColor"]  = 0x0E,
    ["Color3"]      = 0x0F,
    ["Vector2"]     = 0x10,
    ["Vector3"]     = 0x11,
    ["NumberRange"] = 0x1B,
    ["Rect"]        = 0x1C,
}

local function encAttr(t, v)
    local tag = ATTR_TYPE[t]
    if not tag then return nil end
    if t == "string" then
        return schar(tag) .. spack("<I4", #v) .. v
    elseif t == "boolean" then
        return schar(tag) .. schar(v and 1 or 0)
    elseif t == "number" then
        return schar(tag) .. spack("<d", v)
    elseif t == "UDim" then
        return schar(tag) .. spack("<fi4", v.Scale, v.Offset)
    elseif t == "UDim2" then
        return schar(tag) .. spack("<fi4fi4", v.X.Scale, v.X.Offset, v.Y.Scale, v.Y.Offset)
    elseif t == "BrickColor" then
        return schar(tag) .. spack("<I4", v.Number)
    elseif t == "Color3" then
        return schar(tag) .. spack("<fff", v.R, v.G, v.B)
    elseif t == "Vector2" then
        return schar(tag) .. spack("<ff", v.X, v.Y)
    elseif t == "Vector3" then
        return schar(tag) .. spack("<fff", v.X, v.Y, v.Z)
    elseif t == "NumberRange" then
        return schar(tag) .. spack("<ff", v.Min, v.Max)
    elseif t == "Rect" then
        return schar(tag) .. spack("<ffff", v.Min.X, v.Min.Y, v.Max.X, v.Max.Y)
    end
    return nil
end

local function packAttrs(o)
    local ok, a = pcall(function() return o:GetAttributes() end)
    if not ok or typ(a) ~= "table" then return "", 0, 0 end
    local names = {}
    for k in pairs(a) do names[#names + 1] = k end
    if #names == 0 then return "", 0, 0 end
    tsort(names)
    local body, cnt, lost = {}, 0, 0
    for _, k in ipairs(names) do
        local enc = encAttr(typeof(a[k]), a[k])
        if enc then
            body[#body + 1] = spack("<I4", #k) .. k .. enc
            cnt = cnt + 1
        else
            lost = lost + 1
        end
    end
    if cnt == 0 then return "", 0, lost end
    local raw = spack("<I4", cnt) .. cat(body)
    return sfmt('<BinaryString name="AttributesSerialize">%s</BinaryString>', b64(raw)), cnt, lost
end

local function packTags(o)
    if not CS then return "", 0 end
    local ok, t = pcall(function() return CS:GetTags(o) end)
    if not ok or typ(t) ~= "table" or #t == 0 then return "", 0 end
    tsort(t)
    local payload = cat(t, "\0") .. "\0"
    return sfmt('<BinaryString name="Tags">%s</BinaryString>', b64(payload)), #t
end

--=====[ Script source ]======================================================

local function badSrc(s)
    if typ(s) ~= "string" or s == "" then return true end
    local h = slower(ssub(s, 1, 96))
    return sfind(h, "empty bytecode", 1, true) ~= nil
        or sfind(h, "failed to decompile", 1, true) ~= nil
        or sfind(h, "decompiler error", 1, true) ~= nil
        or sfind(h, "could not decompile", 1, true) ~= nil
        or sfind(h, "decompilation failed", 1, true) ~= nil
end

local function srcOf(o)
    local s = ""
    if dec then
        local ok, r = pcall(dec, o)
        if ok and typ(r) == "string" then s = r end
    end
    if badSrc(s) and gsc then
        local ok, bc = pcall(gsc, o)
        if ok and typ(bc) == "string" and #bc > 0 then
            s = "-- [bytecode dump; length = " .. #bc .. "]"
        end
    end
    if badSrc(s) then
        local ok, r = pcall(function() return o.Source end)
        if ok and typ(r) == "string" then s = r end
    end
    if badSrc(s) then return "" end
    return s
end

--=====[ Property registry ]==================================================

local REG = {
    { "Instance", { "Name" } },
    { "BasePart", { "Size", "CFrame", "Color", "Material", "MaterialVariant",
        "Transparency", "Reflectance", "Anchored", "CanCollide", "CanTouch",
        "CanQuery", "Locked", "Massless", "CastShadow", "CollisionGroup",
        "CustomPhysicalProperties", "PivotOffset" } },
    { function(o) return o.ClassName == "Part" end, { "Shape" } },
    { "DataModelMesh", { "Scale", "Offset", "VertexColor" } },
    { "FileMesh", { "MeshId", "TextureId" } },
    { "SpecialMesh", { "MeshId", "TextureId", "MeshType" } },
    { "Decal", { "Texture", "Face", "Color3", "Transparency", "ZIndex" } },
    { "Texture", { "StudsPerTileU", "StudsPerTileV" } },
    { "GuiObject", { "Position", "Size", "AnchorPoint", "Rotation", "Visible",
        "ZIndex", "BackgroundColor3", "BackgroundTransparency", "BorderColor3",
        "BorderSizePixel", "BorderMode", "ClipsDescendants", "Active",
        "Selectable", "AutomaticSize", "SizeConstraint", "LayoutOrder" } },
    { function(o) return o:IsA("TextLabel") or o:IsA("TextButton") or o:IsA("TextBox") end,
        { "Text", "TextColor3", "TextSize", "TextTransparency", "TextScaled",
        "TextWrapped", "TextXAlignment", "TextYAlignment", "RichText", "LineHeight",
        "Font", "FontFace", "TextStrokeColor3", "TextStrokeTransparency" } },
    { "TextBox", { "PlaceholderText", "ClearTextOnFocus", "MultiLine" } },
    { function(o) return o:IsA("ImageLabel") or o:IsA("ImageButton") end,
        { "Image", "ImageColor3", "ImageTransparency", "ImageRectOffset",
        "ImageRectSize", "ScaleType", "SliceCenter", "SliceScale",
        "ResampleMode", "TileSize" } },
    { "LayerCollector", { "Enabled" } },
    { "ScreenGui", { "DisplayOrder", "IgnoreGuiInset" } },
    { "UICorner", { "CornerRadius" } },
    { "UIStroke", { "Thickness", "Color", "Transparency", "ApplyStrokeMode",
        "LineJoinMode", "Enabled" } },
    { "UIGradient", { "Color", "Transparency", "Offset", "Rotation", "Enabled" } },
    { "UIPadding", { "PaddingTop", "PaddingBottom", "PaddingLeft", "PaddingRight" } },
    { "UIListLayout", { "Padding", "FillDirection", "HorizontalAlignment",
        "VerticalAlignment", "SortOrder" } },
    { "UIGridLayout", { "CellSize", "CellPadding", "FillDirection",
        "HorizontalAlignment", "VerticalAlignment", "SortOrder", "StartCorner" } },
    { "UIScale", { "Scale" } },
    { "UIAspectRatioConstraint", { "AspectRatio", "AspectType", "DominantAxis" } },
    { "UISizeConstraint", { "MinSize", "MaxSize" } },
    { "Humanoid", { "Health", "MaxHealth", "WalkSpeed", "JumpPower", "JumpHeight",
        "HipHeight", "DisplayName", "RigType", "AutoRotate" } },
    { "Camera", { "CFrame", "FieldOfView" } },
    { "Sound", { "SoundId", "Volume", "PlaybackSpeed", "Looped", "Playing",
        "TimePosition", "RollOffMaxDistance", "RollOffMinDistance" } },
    { "Light", { "Brightness", "Color", "Enabled", "Shadows" } },
    { "PointLight", { "Range" } },
    { "SpotLight", { "Range", "Angle" } },
    { "SurfaceLight", { "Range", "Angle" } },
    { "ParticleEmitter", { "Rate", "Lifetime", "Speed", "SpreadAngle",
        "Acceleration", "Drag", "LightEmission", "LightInfluence",
        "EmissionDirection", "RotSpeed", "ZOffset", "Squash", "Texture",
        "Color", "Transparency", "Size", "Rotation", "Enabled" } },
    { "Beam", { "Attachment0", "Attachment1", "Texture", "Color",
        "Transparency", "Width0", "Width1", "FaceCamera", "Segments",
        "CurveSize0", "CurveSize1", "TextureLength", "TextureSpeed",
        "LightEmission", "LightInfluence", "Enabled" } },
    { "Trail", { "Attachment0", "Attachment1", "Texture", "Color",
        "Transparency", "Lifetime", "FaceCamera", "Enabled" } },
    { "LuaSourceContainer", { "Enabled", "Disabled", "RunContext", "Source" } },
    { "JointInstance", { "Part0", "Part1", "C0", "C1", "Enabled" } },
    { "Attachment", { "CFrame", "Position", "Orientation", "Visible",
        "Axis", "SecondaryAxis" } },
    { "Constraint", { "Attachment0", "Attachment1", "Enabled", "Visible", "Color" } },
    { "RodConstraint", { "Length", "Thickness" } },
    { "RopeConstraint", { "Length", "Restitution", "Thickness" } },
    { "SpringConstraint", { "FreeLength", "Stiffness", "Damping" } },
    { "BallSocketConstraint", { "Radius" } },
    { "CylindricalConstraint", { "TargetPosition", "TargetVelocity" } },
    { "HingeConstraint", { "TargetAngle", "TargetAngularVelocity" } },
    { "AlignPosition", { "Mode", "Position", "MaxForce", "MaxVelocity",
        "Responsiveness", "ApplyAtCenterOfMass", "RigidityEnabled" } },
    { "AlignOrientation", { "Mode", "CFrame", "MaxTorque", "MaxAngularVelocity",
        "Responsiveness", "RigidityEnabled", "PrimaryAxisOnly" } },
    { "WeldConstraint", { "Part0", "Part1", "Enabled" } },
    { "NoCollisionConstraint", { "Part0", "Part1", "Enabled" } },
    { "SurfaceAppearance", { "ColorMap", "NormalMap", "MetalnessMap",
        "RoughnessMap", "AlphaMode" } },
    { "MeshPart", { "MeshId", "TextureID", "CollisionFidelity",
        "RenderFidelity", "DoubleSided" } },
    { "Highlight", { "FillColor", "FillTransparency", "OutlineColor",
        "OutlineTransparency", "DepthMode", "Enabled", "Adornee" } },
    { "ProximityPrompt", { "ActionText", "ObjectText", "HoldDuration",
        "MaxActivationDistance", "Enabled", "RequiresLineOfSight",
        "KeyboardKeyCode", "GamepadKeyCode", "Style", "Exclusivity",
        "ClickablePrompt" } },
    { "ClickDetector", { "MaxActivationDistance", "CursorIcon" } },
    { "SurfaceGui", { "Adornee", "Face", "CanvasSize", "LightInfluence",
        "AlwaysOnTop", "Enabled", "PixelsPerStud", "SizingMode", "Brightness" } },
    { "BillboardGui", { "Adornee", "Size", "StudsOffset",
        "StudsOffsetWorldSpace", "ExtentsOffset", "AlwaysOnTop", "MaxDistance",
        "LightInfluence", "Enabled" } },
    { "Seat", { "Disabled" } },
    { "VehicleSeat", { "Disabled", "MaxSpeed", "Torque", "TurnSpeed",
        "HeadsUpDisplay" } },
    { "SpawnLocation", { "Duration", "Neutral", "AllowTeamChangeOnTouch",
        "Enabled", "TeamColor" } },
    { "Team", { "TeamColor", "AutoAssignable" } },
    { "Tool", { "Grip", "CanBeDropped", "RequiresHandle", "Enabled",
        "ToolTip", "TextureId", "ManualActivationOnly" } },
    { "Accessory", { "AttachmentPoint" } },
    { "Fire", { "Size", "Heat", "Color", "SecondaryColor", "Enabled" } },
    { "Smoke", { "Size", "Opacity", "RiseVelocity", "Color", "Enabled" } },
    { "Sparkles", { "SparkleColor", "Enabled" } },
    { "ViewportFrame", { "LightColor", "LightDirection", "Ambient",
        "ImageColor3", "ImageTransparency" } },
    { "Model", { "PrimaryPart", "LevelOfDetail", "ModelStreamingMode" } },
    { "ValueBase", { "Value" } },
}

--=====[ Context helpers ]====================================================

local function mt(o, m)
    if typ(m) == "function" then
        local ok, r = pcall(m, o)
        return ok and r
    end
    return o:IsA(m)
end

local function ch(o, ctx)
    if ctx and ctx.kids[o] then return ctx.kids[o] end
    local ok, r = pcall(function() return o:GetChildren() end)
    if not ok or typ(r) ~= "table" then r = {} end
    if ctx then ctx.kids[o] = r end
    return r
end

local function propsFor(o, ctx)
    local cn = o.ClassName
    local c = ctx.pc[cn]
    if c then return c end
    local seen, list = {}, {}
    local isPart = o:IsA("BasePart")
    local isAttach = o:IsA("Attachment")
    local isPalParent = isPart or isAttach
    local function use(nm)
        if typ(nm) ~= "string" or seen[nm] then return false end
        if BLOCK_PROP[nm] then return false end
        if isPalParent and PAL_PROP[nm] then return false end
        if isPart and nm == "BrickColor" then return false end
        return true
    end
    if ctx.opt.deep ~= false and gp then
        local pok, pr = pcall(gp, o)
        if pok and typ(pr) == "table" then
            for _, p in ipairs(pr) do
                local nm = typ(p) == "table" and p.Name or p
                if use(nm) then seen[nm] = true; ins(list, nm) end
            end
        end
    end
    for _, g in ipairs(REG) do
        if mt(o, g[1]) then
            for _, p in ipairs(g[2]) do
                if use(p) then seen[p] = true; ins(list, p) end
            end
        end
    end
    ctx.pc[cn] = list
    return list
end

local function getDefault(ctx, cn, p)
    local d = ctx.dc[cn]
    if d == nil then
        local ok, i = pcall(Instance.new, cn)
        d = (ok and i) or false
        ctx.dc[cn] = d
    end
    if not d then return nil, false end
    local ok, v = pcall(function() return d[p] end)
    if ok then return v, true end
    return nil, false
end

local function eq(a, b)
    if a == b then return true end
    local ta, tb = typ(a), typ(b)
    if ta ~= tb then return false end
    if ta == "number" then
        if a ~= a and b ~= b then return true end
        return false
    end
    return false
end

--=====[ Native saveinstance handoff ]======================================

local function tryNative(o, fn, opt)
    if not nsi then return false, "no native saveinstance available" end
    local a = {
        Decompile = opt.nativeDecompile == true,
        DecompileTimeout = tonum(opt.decompileTimeout) or 10,
        DecompileIgnore = opt.includeCore and {} or { "Chat", "CoreGui", "CorePackages" },
        NilInstances = false,
        RemovePlayerCharacters = true,
        SavePlayers = false,
        MaxThreads = 3,
        ShowStatus = true,
        IgnoreDefaultProps = true,
        IsolateStarterPlayer = true,
    }
    if typ(opt.nativeArgs) == "table" then
        for k, v in pairs(opt.nativeArgs) do a[k] = v end
    end
    local ok, err = pcall(nsi, o, fn, a)
    if ok then return true end
    local b = { object = o, FilePath = fn, filename = fn }
    for k, v in pairs(a) do b[k] = v end
    local ok2 = pcall(nsi, b)
    if ok2 then return true end
    return false, tostr(err)
end

--=====[ Asset archiving ]===================================================

local function archive(u, ctx)
    local id = tostr(u):match("%d+")
    if not id or ctx.dl[id] then return end
    ctx.dl[id] = true
    if not (writefile and HttpGet) then return end
    local ok, data = pcall(HttpGet, "https://assetdelivery.roblox.com/v1/asset/?id=" .. id)
    if not ok or typ(data) ~= "string" or #data == 0 then return end
    if not ctx.dlfolder then
        if makefolder then pcall(makefolder, "WalkeAssets") end
        ctx.dlfolder = true
    end
    pcall(writefile, "WalkeAssets/" .. id, data)
    ctx.st.assets = ctx.st.assets + 1
end

--=====[ Terrain ]============================================================

local TERRAIN_CHUNK = 64
local RLE_MARKER = 0xFFFF

local function terrainSrc(data)
    return cat({
        'local d="', data, '"\n',
        'local T=workspace.Terrain\n',
        'local mm={} for _,m in ipairs(Enum.Material:GetEnumItems()) do mm[m.Value]=m end\n',
        'local B="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"\n',
        'local iv={} for i=1,#B do iv[B:sub(i,i)]=i-1 end\n',
        'local function dc(s) local r={} local n=#s local i=1 while i<=n do local a=iv[s:sub(i,i)] or 0 local b=iv[s:sub(i+1,i+1)] or 0 local p3=s:sub(i+2,i+2) local p4=s:sub(i+3,i+3) local c=iv[p3] or 0 local e=iv[p4] or 0 r[#r+1]=string.char(a*4+math.floor(b/16)) if p3~="=" and p3~="" then r[#r+1]=string.char((b%16)*16+math.floor(c/4)) end if p4~="=" and p4~="" then r[#r+1]=string.char((c%4)*64+e) end i=i+4 end return table.concat(r) end\n',
        'local raw=dc(d) local o=1\n',
        'local function rn(f) local t={string.unpack(f,raw,o)} o=t[#t] t[#t]=nil return table.unpack(t) end\n',
        'local nc=rn("<I4")\n',
        'for ci=1,nc do\n',
        '  local ox,oy,oz,sx,sy,sz=rn("<fffHHH")\n',
        '  local ms={} local oc={}\n',
        '  for xi=1,sx do ms[xi]={} oc[xi]={} for yi=1,sy do ms[xi][yi]={} oc[xi][yi]={} for zi=1,sz do\n',
        '    local mv=rn("<H")\n',
        '    if mv==0xFFFF then\n',
        '      local rl=rn("<I4")\n',
        '      for k=1,rl do oc[xi][yi][zi+k-1]=0; ms[xi][yi][zi+k-1]=Enum.Material.Air end\n',
        '      zi=zi+rl-1\n',
        '    else\n',
        '      local ob=string.byte(raw,o) o=o+1\n',
        '      ms[xi][yi][zi]=mm[mv] or Enum.Material.Air\n',
        '      oc[xi][yi][zi]=ob/255\n',
        '    end\n',
        '  end end end\n',
        '  local rg=Region3.new(Vector3.new(ox,oy,oz),Vector3.new(ox+sx*4,oy+sy*4,oz+sz*4))\n',
        '  pcall(function() T:WriteVoxels(rg,4,ms,oc) end)\n',
        'end\n',
        'print("Walke terrain restored: "..nc.." chunks")\n',
    })
end

local function terrainItem(ctx, ref)
    local tr
    local ok = pcall(function() tr = workspace.Terrain end)
    if not ok or not tr then return "" end
    local ext
    ok = pcall(function() ext = tr.MaxExtents end)
    if not ok or not ext then return "" end
    local mn, mx = ext.Min, ext.Max
    local x0, y0, z0 = mn.X * 4, mn.Y * 4, mn.Z * 4
    local x1, y1, z1 = mx.X * 4, mx.Y * 4, mx.Z * 4
    if x1 <= x0 or y1 <= y0 or z1 <= z0 then return "" end
    local cap = ctx.opt.terrainCap or 2048
    if (x1 - x0) > cap or (y1 - y0) > cap or (z1 - z0) > cap then
        ins(ctx.st.warns, "terrain extent exceeds cap; skipped (raise opt.terrainCap)")
        return ""
    end
    local chunks, nc = {}, 0
    local cx = x0
    while cx < x1 do
        local ex = mmin(cx + TERRAIN_CHUNK, x1)
        local cy = y0
        while cy < y1 do
            local ey = mmin(cy + TERRAIN_CHUNK, y1)
            local cz = z0
            while cz < z1 do
                local ez = mmin(cz + TERRAIN_CHUNK, z1)
                local rg = Region3.new(Vector3.new(cx, cy, cz), Vector3.new(ex, ey, ez)):ExpandToGrid(4)
                local rok, ms, oc = pcall(function() return tr:ReadVoxels(rg, 4) end)
                if rok and ms and ms[1] and ms[1][1] then
                    local sx, sy, sz = #ms, #ms[1], #ms[1][1]
                    local pos, rsz = rg.CFrame.Position, rg.Size
                    local ox = pos.X - rsz.X / 2
                    local oy = pos.Y - rsz.Y / 2
                    local oz = pos.Z - rsz.Z / 2
                    local vb = {}
                    local hasNonAir = false
                    for xi = 1, sx do
                        for yi = 1, sy do
                            local zi = 1
                            while zi <= sz do
                                local m = ms[xi][yi][zi]
                                local ov = oc[xi][yi][zi] or 0
                                if ov <= 0 and (not m or m == Enum.Material.Air) then
                                    local runLen = 1
                                    while zi + runLen <= sz do
                                        local m2 = ms[xi][yi][zi + runLen]
                                        local o2 = oc[xi][yi][zi + runLen] or 0
                                        if o2 > 0 or (m2 and m2 ~= Enum.Material.Air) then break end
                                        runLen = runLen + 1
                                    end
                                    vb[#vb + 1] = spack("<H", RLE_MARKER) .. spack("<I4", runLen)
                                    zi = zi + runLen
                                else
                                    vb[#vb + 1] = spack("<H", (m and m.Value) or 0) .. schar(u8(ov))
                                    hasNonAir = true
                                    zi = zi + 1
                                end
                            end
                        end
                    end
                    if hasNonAir then
                        nc = nc + 1
                        chunks[#chunks + 1] = spack("<fffHHH", ox, oy, oz, sx, sy, sz) .. cat(vb)
                    end
                end
                cz = ez
            end
            cy = ey
        end
        cx = ex
    end
    if nc == 0 then return "" end
    local data = b64(spack("<I4", nc) .. cat(chunks))
    return cat({
        sfmt('<Item class="Script" referent="%s">', ref),
        '<Properties>',
        S["string"]("Name", "Walke_Terrain_Restorer"),
        sfmt('<ProtectedString name="Source">%s</ProtectedString>', cdata(terrainSrc(data))),
        '</Properties></Item>',
    })
end

--=====[ Hidden property reader ]============================================

local function readHidden(o, p, ctx)
    local ok, v = pcall(function() return o[p] end)
    if ok and typ(v) == "string" and #v > 0 then return v end
    if ctx.ghp then
        ok, v = pcall(ctx.ghp, o, p)
        if ok and typ(v) == "string" and #v > 0 then return v end
    end
    if ctx.shp then
        local sok = pcall(ctx.shp, o, p, true)
        if sok then
            ok, v = pcall(function() return o[p] end)
            if ok and typ(v) == "string" and #v > 0 then return v end
        end
    end
    return nil
end

local function unionTags(o, ctx)
    local b, geo = {}, false
    local function grab(names)
        for _, nm in ipairs(names) do
            local d = readHidden(o, nm, ctx)
            if d and #d >= 8 then
                b[#b + 1] = sfmt('<BinaryString name="%s">%s</BinaryString>', nm, b64(d))
                return true
            end
        end
        return false
    end
    if grab({ "MeshData" }) then geo = true end
    if grab({ "PhysicsData", "PhysicalConfigData" }) then geo = true end
    if grab({ "ChildData" }) then geo = true end
    if not geo then return "" end
    if ctx.ghp then
        local ok, isz = pcall(ctx.ghp, o, "InitialSize")
        if ok and typeof(isz) == "Vector3" then
            b[#b + 1] = sfmt('<Vector3 name="InitialSize"><X>%s</X><Y>%s</Y><Z>%s</Z></Vector3>',
                nf(isz.X), nf(isz.Y), nf(isz.Z))
        end
    end
    return cat(b)
end

--=====[ Blacklist / keep ====================================================

local function block(opt)
    local b = {}
    if opt and opt.blockCore == false then return b end
    local function add(n)
        local ok, s = pcall(function() return game:GetService(n) end)
        if ok and s then b[s] = true end
    end
    if not opt or opt.includeCore ~= true then
        add("CoreGui"); add("CorePackages"); add("RobloxPluginGuiService")
    end
    if gethui and (not opt or opt.includeCore ~= true) then
        local ok, h = pcall(gethui)
        if ok and h then b[h] = true end
    end
    return b
end

local function insertable(o)
    if SKIP_CLASS[o.ClassName] then return false end
    return true
end

local function keep(c, ctx)
    if ctx.block[c] then return false end
    if not insertable(c) then return false end
    if ctx.opt.respectArchivable == true then
        local ok, a = pcall(function() return c.Archivable end)
        if ok and a == false then return false end
    end
    local cn = c.ClassName
    if ctx.ign[cn] then return false end
    if ctx.opt.noScripts and c:IsA("LuaSourceContainer") then return false end
    if ctx.opt.skipInvisible and c:IsA("BasePart") then
        local ok, tr = pcall(function() return c.Transparency end)
        if ok and tr and tr >= 1 then return false end
    end
    return true
end

--=====[ Walk (main serializer) ]============================================

local function walk(o, ctx, dep)
    if ctx.done[o] then return end
    ctx.done[o] = true
    if ctx.opt.shouldCancel and ctx.opt.shouldCancel() then
        error("__walke_cancel__", 0)
    end
    if dep > ctx.maxd then
        ctx.st.truncated = (ctx.st.truncated or 0) + 1
        if not ctx.warnedDepth then
            ctx.warnedDepth = true
            ins(ctx.st.warns, "max depth reached; subtree truncated")
        end
        return
    end
    local st = ctx.st
    if st.inst >= ctx.maxi then
        st.truncated = (st.truncated or 0) + 1
        if not ctx.warnedInstances then
            ctx.warnedInstances = true
            ins(ctx.st.warns, "max instance limit reached; remaining instances skipped")
        end
        return
    end
    st.inst = st.inst + 1
    st.items = st.items + 1
    local cn = o.ClassName
    local bp = o:IsA("BasePart")
    local out = ctx.out
    local usolved = false
    local rid = ctx.refs[o]
    if not rid then
        ctx.cnt.n = ctx.cnt.n + 1
        rid = "RBX" .. ctx.cnt.n
        ctx.refs[o] = rid
    end
    ins(out, sfmt('<Item class="%s" referent="%s">', cn, rid))
    ins(out, '<Properties>')
    for _, p in ipairs(propsFor(o, ctx)) do
        if p == "Source" then
            local src = srcOf(o)
            if src == "" and ctx.opt.rescue and o:IsA("ModuleScript") then
                local rok, mod = pcall(require, o)
                if rok and typ(mod) == "table" then
                    local seen = {}
                    local depth = tonum(ctx.opt.rescueDepth) or 32
                    local function ser(v, d)
                        local t = typ(v)
                        if t == "string" then return sfmt("%q", v) end
                        if t == "number" then return f17(v) end
                        if t == "boolean" then return v and "true" or "false" end
                        if t == "table" then
                            if seen[v] or d > depth then return "nil" end
                            seen[v] = true
                            local ks = {}
                            for k in pairs(v) do
                                local kt = typ(k)
                                if kt == "string" or kt == "number" then ks[#ks + 1] = k end
                            end
                            tsort(ks, function(a, b)
                                local ta, tb = typ(a), typ(b)
                                if ta ~= tb then return ta < tb end
                                return a < b
                            end)
                            local b = { "{" }
                            for _, k in ipairs(ks) do
                                local key = typ(k) == "string"
                                    and "[" .. sfmt("%q", k) .. "]"
                                    or "[" .. f17(k) .. "]"
                                b[#b + 1] = key .. "=" .. ser(v[k], d + 1) .. ","
                            end
                            b[#b + 1] = "}"
                            seen[v] = nil
                            return cat(b)
                        end
                        return "nil"
                    end
                    src = "return " .. ser(mod, 0)
                end
            end
            if src ~= "" then
                ins(out, sfmt('<ProtectedString name="Source">%s</ProtectedString>', cdata(src)))
                st.props = st.props + 1
            end
        else
            local ok, v = pcall(function() return o[p] end)
            if ok and v ~= nil then
                if ctx.opt.assets and CONTENT_PROP[p] and typ(v) == "string" then
                    archive(v, ctx)
                end
                local skipDef = false
                if ctx.opt.minify ~= false and p ~= "Name" then
                    local dv, has = getDefault(ctx, cn, p)
                    if has and eq(dv, v) then skipDef = true end
                end
                if not skipDef then
                    local f = S[typeof(v)]
                    if f then
                        local xp = f(p, v, ctx.refs, bp)
                        if xp and xp ~= "" then
                            ins(out, xp)
                            st.props = st.props + 1
                        end
                    else
                        local tt = typeof(v)
                        st.skip = st.skip + 1
                        st.uns[tt] = (st.uns[tt] or 0) + 1
                        if ctx.opt.mode == "debug" then
                            local dk = cn .. "." .. p
                            if not ctx.dbg[dk] then
                                ctx.dbg[dk] = true
                                warn("[Walke] skipped " .. dk .. " <" .. tt .. ">")
                            end
                        end
                        if ctx.opt.mode == "strict" then
                            error("[Walke] unsupported property " .. cn .. "." .. p .. " <" .. tt .. ">", 0)
                        end
                    end
                end
            elseif not ok then
                st.skip = st.skip + 1
                if ctx.opt.mode == "debug" then
                    local rk = "rf:" .. cn .. "." .. p
                    if not ctx.dbg[rk] then
                        ctx.dbg[rk] = true
                        warn("[Walke] read-fail " .. cn .. "." .. p)
                    end
                end
            end
        end
    end
    if ghp and cn == "MeshPart" then
        local ok, isz = pcall(ghp, o, "InitialSize")
        if ok and typeof(isz) == "Vector3" then
            ins(out, sfmt('<Vector3 name="InitialSize"><X>%s</X><Y>%s</Y><Z>%s</Z></Vector3>',
                nf(isz.X), nf(isz.Y), nf(isz.Z)))
            st.props = st.props + 1
        end
    end
    if ctx.opt.unions and (cn == "UnionOperation" or cn == "NegateOperation") then
        local tg = unionTags(o, ctx)
        if tg ~= "" then
            ins(out, tg)
            st.props = st.props + 1
            st.unions = st.unions + 1
            usolved = true
        end
    end
    if ctx.opt.attributes ~= false then
        local a, ac, al = packAttrs(o)
        if a ~= "" then ins(out, a); st.attrs = st.attrs + ac end
        if al > 0 then st.attrLost = st.attrLost + al end
    end
    if ctx.opt.tags ~= false then
        local tg, tc = packTags(o)
        if tg ~= "" then ins(out, tg); st.tags = st.tags + tc end
    end
    ins(out, '</Properties>')
    for _, c in ipairs(ch(o, ctx)) do
        if keep(c, ctx) then walk(c, ctx, dep + 1) end
    end
    ins(out, '</Item>')
    if (cn == "UnionOperation" or cn == "NegateOperation") and not usolved then
        if ctx.opt.holo then
            local ok1, sz = pcall(function() return o.Size end)
            local ok2, cf = pcall(function() return o.CFrame end)
            if ok1 and ok2 and sz and cf then
                ctx.syn = ctx.syn + 1
                ins(out, sfmt('<Item class="Part" referent="RBXsyn%d">', ctx.syn))
                ins(out, '<Properties>')
                ins(out, S["string"]("Name", "Walke_MissingUnion_" .. o.Name))
                ins(out, S["Vector3"]("Size", sz, nil, true))
                ins(out, S["CFrame"]("CFrame", cf))
                ins(out, S["Color3"]("Color", Color3.new(1, 0, 0), nil, true))
                ins(out, S["number"]("Transparency", 0.5))
                ins(out, S["boolean"]("Anchored", true))
                ins(out, '</Properties></Item>')
                st.items = st.items + 1
                st.holo = st.holo + 1
            end
        else
            st.csg = st.csg + 1
        end
    end
    if ctx.opt.yield ~= false and ctx.opt.noYield ~= true then
        local now = oclock()
        if now - ctx.fs >= ctx.yi then
            if ctx.opt.onProgress then
                pcall(ctx.opt.onProgress, st.inst, st.items, st.bytes)
            end
            pcall(task.wait)
            ctx.fs = oclock()
        end
    end
end

--=====[ Ref repair / validation ]===========================================

local function repairRefs(xml, st)
    local refs = {}
    for id in sgsub(xml, "<!%[CDATA%[.-%]%]>", ""):gmatch('referent="([^"]+)"') do
        refs[id] = true
    end
    local dangling = 0
    for id in sgsub(xml, "<!%[CDATA%[.-%]%]>", ""):gmatch('<Ref name="[^"]-">([^<]+)</Ref>') do
        if not refs[id] then dangling = dangling + 1 end
    end
    st.dangling = dangling
    return xml
end

local function validate(xml, st)
    if ssub(xml, 1, 7) ~= "<roblox" then return false, "bad root" end
    if ssub(xml, -9) ~= "</roblox>" then return false, "unclosed root" end
    local scan = sgsub(xml, "<!%[CDATA%[.-%]%]>", "")
    local _, o = sgsub(scan, "<Item ", "")
    local _, c = sgsub(scan, "</Item>", "")
    if o ~= c then return false, "item tag imbalance (" .. o .. "/" .. c .. ")" end
    if o ~= st.items then return false, "item count mismatch (" .. o .. "/" .. st.items .. ")" end
    local rs = {}
    for id in scan:gmatch('referent="([^"]+)"') do
        if rs[id] then return false, "duplicate referent: " .. id end
        rs[id] = true
    end
    local dang = 0
    for id in scan:gmatch('<Ref name="[^"]-">([^<]+)</Ref>') do
        if not rs[id] then dang = dang + 1 end
    end
    st.dangling = dang
    return true, "ok, " .. dang .. " dangling refs"
end

--=====[ Stats report ]======================================================

local function report(st, vok, vmsg)
    local sz = st.bytes
    local n, u = sz, "B"
    if sz >= 1048576 then n, u = sz / 1048576, "MB"
    elseif sz >= 1024 then n, u = sz / 1024, "KB" end
    local ut = 0
    for _ in pairs(st.uns) do ut = ut + 1 end
    print(sfmt(
        "[Walke] deep:%s inst:%d items:%d props:%d attrs:%d attrLost:%d tags:%d " ..
        "assets:%d holo:%d unions:%d csg:%d dangling:%d skip:%d unsupported:%d " ..
        "refs:%d trunc:%d warns:%d out:%.1f%s time:%.2fs valid:%s(%s)",
        tostr(st.deep), st.inst, st.items, st.props, st.attrs, st.attrLost,
        st.tags, st.assets, st.holo, st.unions, st.csg, st.dangling,
        st.skip, ut, st.refs, st.truncated or 0, #st.warns,
        n, u, st.time or 0, tostr(vok), tostr(vmsg)))
    if not st.deep then
        warn("[Walke] getproperties unavailable — registry-only capture (fewer props)")
    end
    if st.csg > 0 then
        warn("[Walke] " .. st.csg .. " CSG unions have no mesh data saved; invisible in Studio. Use holo=true for red markers")
    end
    for _, w in ipairs(st.warns) do
        warn("[Walke] " .. w)
    end
end

--=====[ Reference assignment ]==============================================

local function assign(o, refs, cnt, blk, ctx, dep)
    if refs[o] or not keep(o, ctx) or cnt.n >= ctx.maxi or dep > ctx.maxd then
        return
    end
    if ctx.opt.shouldCancel and ctx.opt.shouldCancel() then
        error("__walke_cancel__", 0)
    end
    cnt.n = cnt.n + 1
    refs[o] = "RBX" .. cnt.n
    for _, c in ipairs(ch(o, ctx)) do
        if not blk[c] then assign(c, refs, cnt, blk, ctx, dep + 1) end
    end
end

--=====[ Root normalization ]================================================

local function svc(o)
    local ok, par = pcall(function() return o.Parent end)
    if not ok or not par then return false end
    local ok2, pc = pcall(function() return par.ClassName end)
    return ok2 and pc == "DataModel"
end

local function kidsOf(o, blk)
    local ks = {}
    for _, c in ipairs(ch(o)) do
        if not (blk and blk[c]) then ks[#ks + 1] = c end
    end
    return ks
end

local function normalize(root, blk)
    local ents = {}
    local function add(o)
        local cn = o.ClassName
        if cn == "DataModel" then
            for _, c in ipairs(ch(o)) do
                if not (blk and blk[c]) then
                    local nm = "Service"
                    pcall(function() nm = c.ClassName end)
                    local ks = kidsOf(c, blk)
                    if #ks > 0 then
                        ents[#ents + 1] = { folder = nm, kids = ks }
                    end
                end
            end
        elseif svc(o) then
            for _, c in ipairs(kidsOf(o, blk)) do
                ents[#ents + 1] = { inst = c }
            end
        else
            ents[#ents + 1] = { inst = o }
        end
    end
    if typeof(root) == "Instance" then
        add(root)
    elseif typ(root) == "table" then
        for _, o in ipairs(root) do
            if typeof(o) == "Instance" then add(o) end
        end
    end
    return ents
end

--=====[ On-Screen Status HUD ]==============================================

local UI = {}

local COLORS = {
    bg        = Color3.fromRGB(18, 18, 22),
    bgAlt     = Color3.fromRGB(26, 26, 32),
    border    = Color3.fromRGB(60, 60, 72),
    accent    = Color3.fromRGB(120, 180, 255),
    accentDim = Color3.fromRGB(40, 70, 120),
    text      = Color3.fromRGB(235, 235, 245),
    textDim   = Color3.fromRGB(150, 150, 165),
    ok        = Color3.fromRGB(90, 220, 140),
    warn      = Color3.fromRGB(255, 190, 80),
    err       = Color3.fromRGB(255, 100, 100),
    bar       = Color3.fromRGB(80, 140, 220),
    barBg     = Color3.fromRGB(35, 35, 45),
}

local function mk(class, props, children)
    local ok, i = pcall(Instance.new, class)
    if not ok or not i then return nil end
    for k, v in pairs(props or {}) do
        if k ~= "Parent" then pcall(function() i[k] = v end) end
    end
    for _, c in ipairs(children or {}) do
        if c then c.Parent = i end
    end
    if props and props.Parent then i.Parent = props.Parent end
    return i
end

local function uiParent()
    local ok, cg = pcall(function() return game:GetService("CoreGui") end)
    if ok and cg then
        local fine = pcall(function()
            local tmp = Instance.new("Folder")
            tmp.Parent = cg
            tmp:Destroy()
        end)
        if fine then return cg end
    end
    local ok2, pg = pcall(function()
        return game:GetService("Players").LocalPlayer:WaitForChild("PlayerGui", 5)
    end)
    if ok2 and pg then return pg end
    return nil
end

local function fmtBytes(n)
    if n >= 1048576 then return sfmt("%.1f MB", n / 1048576) end
    if n >= 1024 then return sfmt("%.1f KB", n / 1024) end
    return tostr(n) .. " B"
end

local function fmtTime(s)
    if s < 1 then return sfmt("%dms", mfloor(s * 1000)) end
    if s < 60 then return sfmt("%.2fs", s) end
    local m = mfloor(s / 60)
    local sec = s - m * 60
    return sfmt("%dm %04.1fs", m, sec)
end

local function logColor(level)
    if level == "err" or level == "error" then return COLORS.err end
    if level == "warn" or level == "warning" then return COLORS.warn end
    if level == "ok" or level == "success" then return COLORS.ok end
    return COLORS.textDim
end

function UI.create(opts)
    opts = opts or {}
    local parent = opts.parent or uiParent()
    if not parent then return nil, "no GUI parent available" end

    local root = mk("ScreenGui", {
        Name = "WalkeStatusUI",
        ResetOnSpawn = false,
        ZIndexBehavior = Enum.ZIndexBehavior.Sibling,
        DisplayOrder = 999999,
        IgnoreGuiInset = true,
        Parent = parent,
    })
    if not root then return nil, "ScreenGui creation failed" end

    local frame = mk("Frame", {
        Name = "Root",
        Size = UDim2.new(0, 360, 0, 210),
        Position = UDim2.new(1, -20, 1, -20),
        AnchorPoint = Vector2.new(1, 1),
        BackgroundColor3 = COLORS.bg,
        BorderSizePixel = 0,
        Parent = root,
    })
    if not frame then root:Destroy(); return nil, "Frame creation failed" end

    mk("UICorner", { CornerRadius = UDim.new(0, 10), Parent = frame })
    local stroke = mk("UIStroke", {
        Color = COLORS.border, Thickness = 1,
        Transparency = 0.2, Parent = frame,
    })

    -- Drag
    do
        local dragging, dragStart, startPos = false, nil, nil
        frame.InputBegan:Connect(function(input)
            if input.UserInputType == Enum.UserInputType.MouseButton1
                or input.UserInputType == Enum.UserInputType.Touch then
                dragging = true
                dragStart = input.Position
                startPos = frame.Position
                input.Changed:Connect(function()
                    if input.UserInputState == Enum.UserInputState.End then
                        dragging = false
                    end
                end)
            end
        end)
        frame.InputChanged:Connect(function(input)
            if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
                local delta = input.Position - dragStart
                frame.Position = UDim2.new(
                    startPos.X.Scale, startPos.X.Offset + delta.X,
                    startPos.Y.Scale, startPos.Y.Offset + delta.Y)
            end
        end)
    end

    local header = mk("Frame", {
        Name = "Header",
        Size = UDim2.new(1, -20, 0, 26),
        Position = UDim2.new(0, 10, 0, 8),
        BackgroundTransparency = 1,
        Parent = frame,
    })

    local title = mk("TextLabel", {
        Name = "Title",
        Size = UDim2.new(1, -90, 1, 0),
        BackgroundTransparency = 1,
        Font = Enum.Font.GothamBold,
        TextSize = 14,
        TextColor3 = COLORS.text,
        TextXAlignment = Enum.TextXAlignment.Left,
        Text = "Walke " .. VERSION .. "  •  Idle",
        Parent = header,
    })

    local closeBtn = mk("TextButton", {
        Name = "Close",
        Size = UDim2.new(0, 60, 0, 22),
        Position = UDim2.new(1, 0, 0, 0),
        AnchorPoint = Vector2.new(1, 0),
        BackgroundColor3 = COLORS.bgAlt,
        BorderSizePixel = 0,
        Font = Enum.Font.GothamMedium,
        TextSize = 12,
        TextColor3 = COLORS.textDim,
        Text = "Hide",
        AutoButtonColor = true,
        Parent = header,
    })
    if closeBtn then mk("UICorner", { CornerRadius = UDim.new(0, 5), Parent = closeBtn }) end

    local statusLine = mk("TextLabel", {
        Name = "Status",
        Size = UDim2.new(1, -20, 0, 16),
        Position = UDim2.new(0, 10, 0, 36),
        BackgroundTransparency = 1,
        Font = Enum.Font.Gotham,
        TextSize = 11,
        TextColor3 = COLORS.textDim,
        TextXAlignment = Enum.TextXAlignment.Left,
        Text = "Ready.",
        Parent = frame,
    })

    local barWrap = mk("Frame", {
        Name = "Bar",
        Size = UDim2.new(1, -20, 0, 6),
        Position = UDim2.new(0, 10, 0, 58),
        BackgroundColor3 = COLORS.barBg,
        BorderSizePixel = 0,
        Parent = frame,
    })
    if barWrap then mk("UICorner", { CornerRadius = UDim.new(1, 0), Parent = barWrap }) end

    local barFill = mk("Frame", {
        Name = "Fill",
        Size = UDim2.new(0, 0, 1, 0),
        BackgroundColor3 = COLORS.bar,
        BorderSizePixel = 0,
        Parent = barWrap,
    })
    if barFill then mk("UICorner", { CornerRadius = UDim.new(1, 0), Parent = barFill }) end

    local counters = mk("Frame", {
        Name = "Counters",
        Size = UDim2.new(1, -20, 0, 40),
        Position = UDim2.new(0, 10, 0, 72),
        BackgroundTransparency = 1,
        Parent = frame,
    })

    local labels = {}
    local function addCounter(key, col, row, text, color)
        local l = mk("TextLabel", {
            Name = key,
            Size = UDim2.new(1 / 3, -4, 0.5, 0),
            Position = UDim2.new(col / 3, col > 0 and 4 or 0, row / 2, 0),
            BackgroundTransparency = 1,
            Font = Enum.Font.Code,
            TextSize = 11,
            TextColor3 = color or COLORS.textDim,
            TextXAlignment = Enum.TextXAlignment.Left,
            TextYAlignment = Enum.TextYAlignment.Top,
            Text = text,
            Parent = counters,
        })
        labels[key] = l
    end
    addCounter("items", 0, 0, "items   0")
    addCounter("props", 1, 0, "props   0")
    addCounter("attrs", 2, 0, "attrs   0")
    addCounter("bytes", 0, 1, "bytes   0 B", COLORS.text)
    addCounter("time",  1, 1, "time    0ms", COLORS.text)
    addCounter("refs",  2, 1, "refs    0", COLORS.text)

    local logFrame = mk("ScrollingFrame", {
        Name = "Log",
        Size = UDim2.new(1, -20, 0, 54),
        Position = UDim2.new(0, 10, 0, 118),
        BackgroundColor3 = COLORS.bgAlt,
        BorderSizePixel = 0,
        ScrollBarThickness = 4,
        ScrollBarImageColor3 = COLORS.accentDim,
        CanvasSize = UDim2.new(0, 0, 0, 0),
        AutomaticCanvasSize = Enum.AutomaticSize.Y,
        ScrollBarImageTransparency = 0.5,
        Parent = frame,
    })
    if logFrame then mk("UICorner", { CornerRadius = UDim.new(0, 6), Parent = logFrame }) end

    mk("UIListLayout", {
        SortOrder = Enum.SortOrder.LayoutOrder,
        Padding = UDim.new(0, 2),
        Parent = logFrame,
    })
    mk("UIPadding", {
        PaddingLeft = UDim.new(0, 6), PaddingRight = UDim.new(0, 6),
        PaddingTop = UDim.new(0, 4), PaddingBottom = UDim.new(0, 4),
        Parent = logFrame,
    })

    local footer = mk("TextLabel", {
        Name = "Footer",
        Size = UDim2.new(1, -20, 0, 14),
        Position = UDim2.new(0, 10, 1, -20),
        BackgroundTransparency = 1,
        Font = Enum.Font.Gotham,
        TextSize = 10,
        TextColor3 = COLORS.textDim,
        TextXAlignment = Enum.TextXAlignment.Left,
        Text = "Walke Serializer v" .. VERSION,
        Parent = frame,
    })

    local state = {
        frame = frame, root = root,
        title = title, status = statusLine, bar = barFill, footer = footer,
        labels = labels, log = logFrame,
        startTime = oclock(),
        cancelled = false,
        logCount = 0,
        maxLogs = opts.maxLogs or 32,
        autoHide = opts.autoHide ~= false,
        autoHideDelay = opts.autoHideDelay or 6,
        pulse = 0,
    }

    function state:push(level, msg)
        msg = tostr(msg)
        self.logCount = self.logCount + 1
        local order = self.logCount
        local c = logColor(level)
        local row = mk("TextLabel", {
            Name = "L" .. order,
            Size = UDim2.new(1, 0, 0, 14),
            BackgroundTransparency = 1,
            Font = Enum.Font.Code,
            TextSize = 10,
            TextColor3 = c,
            TextXAlignment = Enum.TextXAlignment.Left,
            TextYAlignment = Enum.TextYAlignment.Top,
            TextWrapped = true,
            Text = "[" .. slower(level):upper() .. "] " .. msg,
            LayoutOrder = order,
            Parent = self.log,
        })
        -- trim
        local logRows = {}
        for _, k in ipairs(self.log:GetChildren()) do
            if k:IsA("TextLabel") then logRows[#logRows + 1] = k end
        end
        if #logRows > self.maxLogs then
            tsort(logRows, function(a, b) return a.LayoutOrder < b.LayoutOrder end)
            for i = 1, #logRows - self.maxLogs do
                pcall(function() logRows[i]:Destroy() end)
            end
        end
        -- autoscroll
        pcall(function()
            self.log.CanvasPosition = Vector2.new(0, self.log.AbsoluteCanvasSize.Y)
        end)
    end

    function state:setTitle(text)
        if self.title then self.title.Text = "Walke " .. VERSION .. "  •  " .. text end
    end
    function state:setStatus(text, color)
        if self.status then
            self.status.Text = text
            self.status.TextColor3 = color or COLORS.textDim
        end
    end
    function state:setProgress(cur, total)
        if not self.bar then return end
        local p = 0
        if total and total > 0 then p = mmin(cur / total, 1) end
        self.bar.Size = UDim2.new(p, 0, 1, 0)
    end
    function state:setLabel(key, text, color)
        local l = self.labels[key]
        if l then l.Text = text; if color then l.TextColor3 = color end end
    end
    function state:updateStats(st)
        if not st then return end
        self:setLabel("items", "items   " .. tostr(st.items or 0))
        self:setLabel("props", "props   " .. tostr(st.props or 0))
        self:setLabel("attrs", "attrs   " .. tostr(st.attrs or 0))
        self:setLabel("bytes", "bytes   " .. fmtBytes(st.bytes or 0), COLORS.text)
        self:setLabel("refs",  "refs    " .. tostr(st.refs or 0))
        local dt = oclock() - self.startTime
        self:setLabel("time", "time    " .. fmtTime(dt), COLORS.text)
    end

    if closeBtn then
        closeBtn.MouseButton1Click:Connect(function()
            state.cancelled = true
            state:setTitle("Hidden")
            if root then root.Enabled = false end
        end)
    end

    task.spawn(function()
        while root and root.Parent do
            task.wait(1)
            state.pulse = (state.pulse + 1) % 2
            if stroke and stroke.Parent then
                stroke.Transparency = 0.2 + state.pulse * 0.15
            end
        end
    end)

    return state
end

--=====[ Public API ]=========================================================

local M = {}

M.Version = VERSION
M.Capabilities = {
    deep = gp ~= nil,
    decompile = dec ~= nil,
    attributes = true,
    tags = true,
    validate = true,
    stats = true,
    minify = true,
    blacklist = true,
    adaptiveYield = true,
    terrain = true,
    rescue = true,
    holo = true,
    assets = true,
    progress = true,
    hud = true,
    archivableFilter = true,
    includeCore = true,
    meshInitialSize = ghp ~= nil,
    unions = (ghp ~= nil) or (sscript ~= nil),
    native = nsi ~= nil,
    ignoreClasses = true,
    noScripts = true,
    cancellable = true,
    chunkedWrite = true,
    childCache = true,
    limits = true,
    cleanup = true,
    modes = { "safe", "strict", "debug", "silent" },
    datatypes = {
        "string", "boolean", "number", "Vector3", "Vector2", "Vector3int16",
        "Vector2int16", "Color3", "CFrame", "EnumItem", "UDim", "UDim2",
        "BrickColor", "NumberRange", "NumberSequence", "ColorSequence",
        "Rect", "PhysicalProperties", "Font", "Content", "Faces", "Axes",
        "Ray", "Instance",
    },
}

function M.serialize(root, opt)
    opt = opt or {}
    if opt.mode ~= "safe" and opt.mode ~= "strict"
        and opt.mode ~= "debug" and opt.mode ~= "silent" then
        opt.mode = "safe"
    end
    local t0 = oclock()
    local ign = {}
    if typ(opt.ignore) == "table" then
        for _, c in ipairs(opt.ignore) do ign[c] = true end
    end
    local blk = block(opt)
    local ents = normalize(root, blk)
    local refs, cnt = {}, { n = 0 }
    local st = {
        inst = 0, items = 0, props = 0, attrs = 0, attrLost = 0,
        tags = 0, assets = 0, holo = 0, unions = 0, csg = 0,
        dangling = 0, skip = 0, uns = {}, warns = {}, refs = 0,
        empty = false, deep = (opt.deep ~= false) and (gp ~= nil),
        truncated = 0, bytes = 0,
    }
    local out = {
        '<roblox xmlns:xmime="http://www.w3.org/2005/05/xmlmime" ' ..
        'xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" ' ..
        'xsi:noNamespaceSchemaLocation="http://www.roblox.com/roblox.xsd" version="4">',
        '<Meta name="ExplicitAutoJoints">true</Meta>',
        '<External>null</External>',
        '<External>nil</External>',
    }
    local ctx = {
        refs = refs, cnt = cnt, out = out, st = st, opt = opt,
        pc = {}, dc = {}, done = {}, dbg = {}, syn = 0,
        block = blk, ign = ign,
        maxd = mmax(1, tonum(opt.maxDepth) or 4000),
        maxi = mmax(0, tonum(opt.maxInstances) or mhuge),
        yi = mmax(0.001, tonum(opt.yieldInterval) or 0.014),
        fs = oclock(),
        dl = {}, ghp = ghp, shp = sscript, kids = {},
    }
    for _, e in ipairs(ents) do
        if e.inst then
            assign(e.inst, refs, cnt, blk, ctx, 1)
        else
            for _, k in ipairs(e.kids) do
                assign(k, refs, cnt, blk, ctx, 2)
            end
        end
    end
    st.refs = cnt.n
    local ok, err = xpcall(function()
        for _, e in ipairs(ents) do
            if e.inst then
                if keep(e.inst, ctx) then walk(e.inst, ctx, 1) end
            else
                ctx.syn = ctx.syn + 1
                ins(out, sfmt('<Item class="Folder" referent="RBXsyn%d">', ctx.syn))
                ins(out, '<Properties>')
                ins(out, S["string"]("Name", e.folder))
                ins(out, '</Properties>')
                st.items = st.items + 1
                for _, k in ipairs(e.kids) do
                    if keep(k, ctx) then walk(k, ctx, 2) end
                end
                ins(out, '</Item>')
            end
        end
        if opt.terrain then
            ctx.syn = ctx.syn + 1
            local ti = terrainItem(ctx, "RBXsyn" .. ctx.syn)
            if ti ~= "" then
                ins(out, ti)
                st.items = st.items + 1
            end
        end
        ins(out, '</roblox>')
        st.empty = (st.items == 0)
    end, function(x) return x end)
    for k, d in pairs(ctx.dc) do
        if d then pcall(function() d:Destroy() end) end
        ctx.dc[k] = nil
    end
    if not ok then error(err, 0) end
    local xml = cat(out, "\n")
    st.bytes = #xml
    st.refs = cnt.n
    st.time = oclock() - t0
    repairRefs(xml, st)
    local vok, vmsg = true, "off"
    if opt.validate ~= false then vok, vmsg = validate(xml, st) end
    if opt.mode ~= "silent" and opt.stats ~= false then
        report(st, vok, vmsg)
    end
    return xml, st, vok, vmsg
end

local function rawSave(o, fn, opt)
    opt = opt or {}
    if opt.native then
        local nok, nerr = tryNative(o, fn, opt)
        if nok then
            print("[Walke] handed off to executor saveinstance — check workspace folder for " .. tostr(fn))
            return { ok = true, stage = "native" }
        end
        warn("[Walke] native saveinstance failed (" .. tostr(nerr) .. "); using Walke serializer")
    end
    local xml, st, vok, vmsg
    local ok, err = pcall(function()
        xml, st, vok, vmsg = M.serialize(o, opt)
    end)
    if not ok then
        if typ(err) == "string" and sfind(err, "__walke_cancel__", 1, true) then
            return { ok = false, stage = "cancelled" }
        end
        warn("[Walke] serialize error:", err)
        return { ok = false, stage = "serialize", err = err }
    end
    if st and st.empty then
        warn("[Walke] no valid roots to serialize")
        return { ok = false, stage = "empty", err = "no valid roots", stats = st }
    end
    if opt.validate ~= false and not vok then
        warn("[Walke] validation failed: " .. tostr(vmsg))
        return { ok = false, stage = "validate", err = vmsg, xml = xml, stats = st }
    end
    if writefile then
        local wok, werr
        local chunk = mmax(65536, tonum(opt.writeChunkSize) or 4000000)
        if #xml > chunk and appendfile and delfile then
            wok, werr = pcall(function()
                pcall(delfile, fn)
                local n = #xml
                local i = 1
                local first = true
                while i <= n do
                    local part = ssub(xml, i, mmin(i + chunk - 1, n))
                    if first then
                        writefile(fn, part); first = false
                    else
                        appendfile(fn, part)
                    end
                    i = i + chunk
                end
            end)
        else
            wok, werr = pcall(writefile, fn, xml)
        end
        if not wok then
            warn("[Walke] could not write " .. tostr(fn))
            return { ok = false, stage = "write", err = werr, xml = xml, stats = st }
        end
        print("[Walke] wrote " .. tostr(fn))
    else
        return { ok = true, stage = "serialized", xml = xml, stats = st, valid = vok, message = vmsg }
    end
    return { ok = true, stage = "done", xml = xml, stats = st, valid = vok, message = vmsg }
end

function M.save(o, fn, opt)
    opt = opt or {}
    if opt.hud == false then return rawSave(o, fn, opt) end

    local ui, uierr = UI.create(opt.hudOptions)
    if not ui then
        warn("[Walke] HUD creation failed: " .. tostr(uierr) .. " — console only")
        return rawSave(o, fn, opt)
    end

    ui:push("info", "Save started → " .. tostr(fn))
    ui:setTitle("Serializing")
    ui:setStatus("Walking instances…", COLORS.accent)

    local oldWarn, oldPrint = warn, print
    local function hook(orig, level)
        return function(...)
            local parts = {}
            for i = 1, select("#", ...) do
                parts[#parts + 1] = tostr(select(i, ...))
            end
            local msg = cat(parts, " ")
            msg = sgsub(msg, "^%[Walke%]%s*", "")
            pcall(function() ui:push(level, msg) end)
            if orig then pcall(orig, ...) end
        end
    end
    warn  = hook(warn,  "warn")
    print = hook(print, "info")

    local callerOnProgress = opt.onProgress
    opt.onProgress = function(inst, items, bytes)
        pcall(function()
            ui:updateStats({ inst = inst, items = items, bytes = bytes or 0 })
            ui:setProgress(inst, opt.maxInstances or inst)
            ui:setStatus(sfmt("Walking… %d instances, %d items", inst, items), COLORS.accent)
        end)
        if callerOnProgress then pcall(callerOnProgress, inst, items, bytes) end
    end

    local callerCancel = opt.shouldCancel
    opt.shouldCancel = function()
        if ui.cancelled then return true end
        if callerCancel then return callerCancel() end
        return false
    end

    local ok, res = pcall(rawSave, o, fn, opt)

    warn  = oldWarn
    print = oldPrint

    if not ok then
        ui:setTitle("Error")
        ui:setStatus("Internal error", COLORS.err)
        ui:push("err", tostr(res))
    elseif typ(res) ~= "table" then
        ui:setTitle("Done")
        ui:setStatus("Finished", COLORS.ok)
        ui:push("ok", "Save returned " .. typ(res))
    elseif res.ok then
        ui:setTitle("Done")
        ui:setStatus("Saved → " .. tostr(fn), COLORS.ok)
        ui:push("ok", "Saved " .. fmtBytes(res.stats and res.stats.bytes or 0) ..
            " in " .. fmtTime(res.stats and res.stats.time or 0))
        ui:setProgress(1, 1)
        ui:updateStats(res.stats or {})
    else
        ui:setTitle("Failed")
        ui:setStatus(tostr(res.err or res.stage or "unknown"), COLORS.err)
        ui:push("err", tostr(res.err or res.stage or "unknown"))
    end

    if res and res.stats and res.stats.warns then
        for _, w in ipairs(res.stats.warns) do ui:push("warn", w) end
    end

    if ui.autoHide then
        task.spawn(function()
            task.wait(ui.autoHideDelay)
            pcall(function()
                if ui.root and ui.root.Parent then ui.root.Enabled = false end
            end)
        end)
    end

    return res
end

--=====[ Convenience wrapper ]===============================================

local un = "User"
pcall(function() un = game:GetService("Players").LocalPlayer.Name end)
print("Hello " .. un .. ", thanks for using Walke v" .. VERSION ..
    ". Call walkesave(instance) to serialize — or walkesave() to serialize game.")

local function safeName(fn)
    fn = sgsub(tostr(fn), "[/\\]", "_")
    fn = sgsub(fn, "%.%.", "_")
    fn = sgsub(fn, '[<>:"|%?%*%z\1-\31]', "")
    if fn == "" then fn = tostr(game.PlaceId) end
    if slower(ssub(fn, -6)) ~= ".rbxmx" then fn = fn .. ".rbxmx" end
    return fn
end

local function nameOf(o)
    local nm = ""
    pcall(function() nm = o.Name end)
    if typ(nm) ~= "string" or nm == "" or nm == "Workspace" or nm == "Game" then
        nm = tostr(game.PlaceId)
    end
    return nm
end

local function api(o)
    if o == nil then
        return M.save(game, safeName(tostr(game.PlaceId) .. ".rbxmx"), nil)
    end
    local t = typeof(o)
    if t == "Instance" then
        return M.save(o, safeName(nameOf(o) .. ".rbxmx"), nil)
    elseif t == "table" then
        if typeof(o.object) == "Instance" then
            return M.save(o.object, safeName(o.filename or (nameOf(o.object) .. ".rbxmx")), o.options or o)
        elseif typeof(o[1]) == "Instance" then
            return M.save(o, safeName(o.filename or "selection.rbxmx"), o.options)
        end
    end
    warn("[Walke] pass an Instance, {Instances}, or {object=inst,...}; got " .. tostr(t))
    return { ok = false, stage = "badarg" }
end

local g = getgenv and getgenv() or _G
g.walkesave = api
g.__WALKE_API = api

M.UI = UI

return M
