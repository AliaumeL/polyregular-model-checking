def top(x : list(list[Char])) -> list[Char]:
    for elem in x: 
        if elem == "one":
            yield "a"
            yield "b"
        elif elem == "two":
            yield "a"
        elif elem == "three":
            yield "b"
            yield "a"

def bottom(x : list[list[chr]]) -> list[chr]:
    for elem in x: 
        if elem == "one": 
            yield "a"
        elif elem == "two":
            yield "a"
            yield "a"
        elif elem == "three":
            yield "b"

def f(x : list[list[str]]) -> bool :
    return list(top(x)) == list(bottom(x))