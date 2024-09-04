#!/usr/bin/env python3
#
# bibauthors.py
#
# This function transforms a list of authors in a BibTeX file into a
# list of authors that distinguishes the last name from the other name(s).
#
# Example:
#  "John Doe and Jane Smith" -> "Doe, John and Smith, Jane"
#
# The function should satisfy the following requirements
#
# 1. The function should always produce valid author lists:
#    (name, name and)* name, name
# 2. If the input is not a valid author list, the function should
#    output "error"

def output_slice(w, slice):
    """ Prints a part of the word w in the specified range.
        Out of bound values are rounded to the bounds of the word.
    """
    start = max(0, slice[0] if slice[0] != None else 0)
    end = min(len(w), slice[1] if slice[1] != None else len(w))
    print(w[start:end], end="")

def output_string(s):
    """ Prints a string s.
    """
    print(s, end="")


def backwards(w,slice=(None,None)):
    """ Iterates over the word w backwards in the specified range 
        where None signifies the start (resp end) of the word.
        Out of bound values are rounded to the bounds of the word.
    """
    start = max(0, slice[0] if slice[0] != None else 0)
    end = min(len(w), slice[1] if slice[1] != None else len(w))
    for i in reversed(range(start,end)):
        yield i

def forward(w,slice=(None,None)):
    """ Iterates over the word w backwards in the specified range 
        where None signifies the start (resp end) of the word.
        Out of bound values are rounded to the bounds of the word.
    """
    start = max(0, slice[0] if slice[0] != None else 0)
    end = min(len(w), slice[1] if slice[1] != None else len(w))
    for i in range(start,end):
        yield i

def equals(w, slice=(None,None), s=""):
    """ Returns True if the word w in the specified range is equal to s.
        Out of bound values are rounded to the bounds of the word.
    """
    start = max(0, slice[0] if slice[0] != None else 0)
    end = min(len(w), slice[1] if slice[1] != None else len(w))
    return w[start:end] == s

def letter(w, i, l):
    """ Returns True if the character at index i in the word w is l.
        Out of bound values are rounded to the bounds of the word.
    """
    pos = max(0, min(len(w)-1, i))
    return w[pos] == l

def bibauthors(w, slice=(None,None)):
    """ Transforms a list of authors in a BibTeX file into a
        list of authors that distinguishes the last name from the other name(s).
    """
    # we split the word into a list of words separated by "and"
    # and we reverse the name in each case
    foundSomeAnd = False
    for i in forward(w, slice):
        # if we see an "and"
        if equals(w, (i,i+5), " and "):
            foundSomeAnd = True
            # we search for the last "and" before the current one
            # (or the beginning of the word)
            foundLastAnd = False
            for j in backwards(w, (0,i-1)):
                if not foundLastAnd:
                    if equals(w, (j,j+5), " and "):
                        reverse_name(w, (j+5,i))
                        foundLastAnd = True
                    elif j == 0:
                        reverse_name(w, (j,i))
                        foundLastAnd = True
            output_string(" and ")
    # we are lacking the last part of the list that does not end with "and"
    foundLastAnd = False
    for i in backwards(w, slice):
        # find the first "and" before the current position or
        # the beginning of the word
        if not foundLastAnd:
            if equals(w, (i,i+5), " and "):
                reverse_name(w, (i+5,slice[1]))
                foundLastAnd = True
            elif i == 0:
                reverse_name(w, slice)
                foundLastAnd = True

def reverse_name(w, slice=(None,None)):
    """ Reverses the name in the specified range
        effectively transforming "John Doe" into "Doe, John".
    """
    # first we find the last space in the slice
    b = False
    for i in backwards(w, slice):
        if b is False and letter(w, i, ' '):
            b = True
            # then we print the slice from the space to the end
            output_slice(w, (i+1, slice[1]))
            # and print the comma
            output_string(", ")
            # then we print whatever was before the space
            output_slice(w, (slice[0], i))
    if b is False:
        # there was no space in the slice, then we print the slice as is
        output_slice(w, slice)


###
# Testing the functions with examples
###
def test_reverse_name(capsys):
    test_cases = [
        ("John Doe", "Doe, John"),
        ("Jane Smith", "Smith, Jane"),
        ("John", "John"),
        ("John Doe and Jane Smith", "Doe, John and Smith, Jane"),
        ("John Doe and Jane", "Doe, John and Jane"),
        ("John H. Doe", "Doe, John H."),
    ]
    expected_out = ""
    for (input, expected) in test_cases:
        reverse_name(input)
        expected_out += expected
    out, err = capsys.readouterr()
    assert out == expected_out


if __name__ == '__main__':
    import sys
    import argparse

    # either we give the --interactive/-i flag to read from stdin
    # or we give a string as an argument for the list of authors to reverse
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--interactive", action="store_true")
    parser.add_argument("authors", nargs='?', type=str)
    args = parser.parse_args()

    if args.interactive:
        while True:
            word = input("Enter a list of authors: ")
            bibauthors(word)
            b = input("\nDo you want to continue? [y/n] ")
            if b != 'y' and b != 'Y':
                break
    elif args.authors is not None:
        bibauthors(args.authors)
    else:
        print("Please provide a list of authors to reverse.")




