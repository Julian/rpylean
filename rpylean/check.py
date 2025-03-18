def check_no_duplicate_levels(env, level_params):
    levels_map = {}
    for level_nidx in level_params:
        level = env.names[level_nidx]
        if level in levels_map:
            raise Exception("Duplicate level %s" % level)
        levels_map[level] = True