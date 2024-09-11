#Our basic type is an enumerated list (we don't use strings at all)
#The enumerated list stores the following tuples: (mem_id of the list, list index, list letter).

class EnumeratedListElement: 
    def __init__(self, mem_id, index, value): 
        if type(value) == EnumeratedListElement:
            raise ValueError("Enumerated list element cannot store another enumerated list element.")
        self.mem_id = mem_id
        self.index = index
        self.value = value
    # We define the comparison operators x < y iff x and y are in the same list, and x.index < y.index.
    def __lt__(self, other): 
        return self.mem_id == other.mem_id and self.index < other.index
    def __le__(self, other): 
        return self.mem_id == other.mem_id and self.index <= other.index
    def __gt__(self, other): 
        return self.mem_id == other.mem_id and self.index > other.index
    def __ge__(self, other): 
        return self.mem_id == other.mem_id and self.index >= other.index
    def __eq__(self, other):
        return self.mem_id == other.mem_id and self.index == other.index
    def __str__(self): 
        return str(self.value)

class EnumeratedList: 
    def __init__(self):
        self.l = []
    def __iter__(self): 
        return iter(self.l)
    def __getitem__(self, i): 
        return self.l[i]
    def __len__(self): 
        return len(self.l)
    def __str__(self): 
        return "[" + ", ".join(str(x) for x in self.l) + "]"
    def __repr__(self): 
        return repr(self.l)
    def append(self, x):
        #We check that x is not an enumerated list element.
        #If it is, we cast it to its value
        if type(x) == EnumeratedListElement:
            x = x.value
        #If it is still an enumerated list element, we raise an error.
        if type(x) == EnumeratedListElement:
            raise ValueError("Something went wrong, trying to append a nested enumerated list element -- this should not be possible.")
        new_element = EnumeratedListElement(id(self), len(self.l), x)
        self.l.append(new_element)
    #The equality is only defined for an enumerated list and a string (literal).
    def __eq__(self, other):
        if type(other) == str: 
            if len(self.l) != len(other): 
                return False
            for i in range(len(self)):
                if self.l[i].value != other[i]: 
                    return False
            return True
        else: 
            return False
    def last(self):
        return self.l[-1]
    def first(self):
        return self.l[0]
    def output(self): 
        #First, we verify that all elements of the list are one letter strings.
        for x in self.l:
            if type(x.value) != str or len(x.value) != 1:
                raise ValueError("Can only output a list of one letter strings.")
        return "".join(x.value for x in self.l)

def toEnumeratedList(l):
    ans = EnumeratedList()
    for x in l: 
        ans.append(x)
    return ans

#### FROM HERE ON EVERYTHING IS DEFINABLE IN TERMS OF FOR PROGRAMS ####

# We define split_on which inputs an enumerated list, and outputs a list of words separated by the separator c.
# Here l has to be a literal. (How to enforce this? Maybe we don't have to -- see the implementation of __eq__ on enumerated lists.)
def split_on(sep, l):
    ans = EnumeratedList()
    current_elem = EnumeratedList()
    for x in l: 
        if x.value == sep: 
            ans.append(current_elem)
            current_elem = EnumeratedList()
        else: 
            current_elem.append(x.value)
    ans.append(current_elem)
    current_elem = EnumeratedList()
    return ans

def words(w):
    return split_on(" ", w)

def and_parts(ws): 
   return split_on("and", ws)

def concat(w):
    ans = EnumeratedList()
    for x in w:
        for y in x.value: 
            ans.append(y.value)
    return ans

def transformBibNames(input):
    if input == "":
        return toEnumeratedList("")
    ans = EnumeratedList()
    current_author = EnumeratedList()
    authors = and_parts(words(input))
    for author in authors:
        current_author.append(author.value.last().value)
        current_author.append(toEnumeratedList(", "))
        not_first_block = False
        for name in author.value:
            if name != author.value.last(): 
                if not_first_block:
                    current_author.append(toEnumeratedList(" "))
                not_first_block = True
                current_author.append(name.value)
        if author != authors.last(): 
            current_author.append(toEnumeratedList(" and "))
        ans.append(current_author)
        current_author = EnumeratedList()
    return concat(concat(ans))

input = toEnumeratedList("Alliaume Dorian Lopez and Rafał Marek Stefański")
print(transformBibNames(input).output())
print(transformBibNames(toEnumeratedList("")).output())
print(transformBibNames(toEnumeratedList("Harry James Potter")).output())

# Here is the general idea of well formed program. All variables are either const or var.
# The argument to the function are all const.
# The var variables are created by x = EnumeratedList(). 
# We can run a function using x = f(y) where y is a const. In this case x is also a const.
# We don't want to have dependency loops in the consts, such as x = f(x). 
# You can run x.append(y) where x and y are var variables. (Such a statement should have the side effect of emptying y.) TODO: Should it really? If so this should be a part of the implementation of append in an enumerated list. 
# You cannot run functions on var variables with one (or two) exceptions:
# - You can run return f(x) where x is a var variable.
# - You (maybe) can run x.append(f(y)) where x, y are a var variables. (This should also have the side effect of emptying y). TODO: Should it really? If so this maybe should not be a part of the implementation of append in an enumerated list.
