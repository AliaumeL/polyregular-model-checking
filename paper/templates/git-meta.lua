-- This is a pandoc lua filter
-- that reads information from the current
-- git repository and adds it to the metadata
-- of the document (if it exists).
--
-- The following fields are added:
-- git-meta:
--  - branch: the current branch
--  - commit: the current commit
--  - date: the date of the current commit
--  - origin: the origin of the current repository

function branch()
    -- call git to get the current branch
    local handle = io.popen("git rev-parse --abbrev-ref HEAD")
    local result = handle:read("*a")
    handle:close()
    return result
end

function commit()
    -- call git to get the current commit
    local handle = io.popen("git rev-parse HEAD")
    local result = handle:read("*a")
    handle:close()
    return result
end

function date()
    -- call git to get the date of the current commit
    local handle = io.popen("git show -s --format=%ci HEAD")
    local result = handle:read("*a")
    handle:close()
    return result
end

function origin()
    -- call git to get the origin of the current repository
    local handle = io.popen("git config --get remote.origin.url")
    local result = handle:read("*a")
    handle:close()
    return result
end

function Meta(meta) 
    meta["git-meta"] = {
        branch = branch(),
        commit = commit(),
        date = date(),
        origin = origin()
    }

    return meta
end

return { 
    { Meta = Meta }
}
