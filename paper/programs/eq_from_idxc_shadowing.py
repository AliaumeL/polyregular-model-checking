def eq(x : list[chr], y : list[chr]) -> bool : 
    for (i, vx) in enumerate(x):
        x = y 
        for (j, vy) in enumerate(x):
            if i == j and ((vx == 'a' and vy != 'a') or (vx == 'b' and vy != 'b')): 
                    return False
    return True
           