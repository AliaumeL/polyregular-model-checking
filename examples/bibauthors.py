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

def backwards(w):
    for i in reversed(range(len(w))):
        yield i

def forward(w):
    for i in range(len(w)):
        yield i

def bibauthors(w):
    for i in forward(w):
        if w[i:i+3] == 'and':
            b = False
            for j,_ in backwards(w[:i]):
                if b == False:
                    if w[j:j+3] == 'and':
                        reverse_name(w[j+3:i])
                        b = True
                    elif j == 0:
                        reverse_name(w[j:i])
                        b = True

def reverse_name(w):
    for i in backwards(w):
        if w[i] == ' ':
            return 


