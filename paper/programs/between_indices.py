def getBetweenIndicesBeforeStop(l, i, j):
    seen_stop = False
    for (k, w) in enumerate(l):
        if i <= k and k <= j:
            if w == "stop":
                seen_stop = True
            if not seen_stop:
                yield w
