def pairs( words ):
    """
    pairs(["slim", "shy", "stop", "dog", "cat"])
    =
    [["slim", "cat"], ["slim", "dog"], ["shy", "cat"], ["shy", "dog"]]
    """
    seen_stop_w1 = False
    for (i, w1) in enumerate(words):
        seen_stop_w2 = False
        if w1 == "stop":
            seen_stop_w1 = True
        if not seen_stop_w1:
            for (j, w2) in reversed(enumerate(words)):
                if w2 == "stop":
                    seen_stop_w2 = True
                if not seen_stop_w2:
                    yield [w1, w2]
