def first_or_second(x : bool, l1 : list[chr], l2 : list[chr]) -> list[chr]:
    if x:
        return l1
    else:
        return l2

def eq(x : list[chr], y : list[chr]) -> bool : 
    b = False
    for (i, vx) in enumerate(first_or_second(b, x, y)):
        b = True
        for (j, vy) in enumerate(first_or_second(b, x, y)):
            if i == j and ((vx == 'a' and vy != 'a') or (vx == 'b' and vy != 'b')): 
                    return False
    return True
           