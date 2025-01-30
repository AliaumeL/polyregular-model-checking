#The program reverses all space-separated words in the input string.
# e.g "hello world" -> "olleh dlrow"

seen_space_top = False
# first we handle all words except of the final one 
for x in input:
    seen_space = False
    if label(x) == " ":
        for y in reversed(input):
            if y < x: 
                if label(y) == " ": 
                    seen_space = True 
                if not seen_space: 
                    print(label(y))
        print(" ")

# then we handle the final word
for y in reversed(input):
    if label(y) == " ": 
        seen_space_top = True 
    if not seen_space_top: 
        print(label(y))