def asToBs(w): 
    for (i, c) in enumerate(w):
        if c == "a": 
            yield "b"
        else:
            yield c
