walkesave(workspace, "workspace.rbxmx", {
    safeMode = true,        -- default; caps at 50k / 5000
    maxInstances = 20000,   -- be more conservative for whole game
    maxDepth = 2000,
    yieldInterval = 0.012,  -- default
})
