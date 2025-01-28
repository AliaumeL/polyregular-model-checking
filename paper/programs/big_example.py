def getBetween(l, i, j):
    """ Get elements between i and j """
    for (k, c) in enumerate(l):
        if i <= k and k <= j:
            yield c

def containsAB(w):
    """ Contains "ab" as a subsequence """
    seen_a = False
    for (x, c) in enumerate(w):
        if c == "a":
            seen_a = True
        elif seen_a and c == "b":
            return True
    return False

def subwordsWithAB(word):
    """ Get subwords that contain "ab" """
    for (i,c) in enumerate(word):
        for (j,d) in rev(enumerate(word)):
            if i < j:
                s = getBetween(word, i, j)
                if containsAB(s):
                    yield s
