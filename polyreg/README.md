# Polyregular Model Checking

## Languages

### Python-like High Level Programs

We want to be able to do the following things:

```python
# reverse is a primitive
def prefix(l : List[Σ], Σ, i : Pos[l]) -> List[Σ]:
    for j,x in reverse(l):
        if i >= j:
            yield x

def prefixes(l : List[Σ]) -> List[List[Σ]]:
    for i,x in l:
        yield prefix(l,i)

def prefixes_inline(l : List[Σ]) -> List[List[Σ]]:
    for j,x in l:
        yield {{
            for i,x in l: 
                if i <= j:
                   yield x
        }}

def weird_test(l : List[Σ]) -> List[List[Σ]]:
    let p = test in
    p = l
    for j,x in l:
        let p = duplicate(p) in 
            ???
    yield l

def concat(a : List[Σ], b : List[Σ]) -> List[Σ]:
    for _,x in {{
       ... some code ...
    }}:
        yield x
    for _,x in b:
        yield x
        yield ["a", "b"]
        yield {{ yield "a"; yield "b" }}
```

```haskell
data BaseType a = List Int | Pos a | Bool
data Type a = Dyn (BaseType a) | ConsExpr (BaseType a)


data StringExpr a = 
    | ListVar String a
    | Call String [Expr a] a
    | List [Expr a] a
    | InlineYield (Stmt a) a
data BoolExpr a  = 
    | BoolVar String a
    | BinOp BinOp (BoolExpr a) (BoolExpr a)
    | Not (BoolExpr a)
    | StrEqual (StringExpr a) (StringExpr a)
data Param a = Bool String 
             | List String 
             | Pos String String
data Stmt a = 
    | Function String [Params a] (Stmt a)
    | Block [Stmt a]
    | For String String (StringExpr a) (Stmt a)
    | If (BoolExpr a) (Stmt a) (Stmt a)
    | Yield (StringExpr a)
    | Let String (StringExpr a) (Stmt a)
    | SetTrue String
```

### Classical For Programs

```haskell
data ForTest = Eq | Neq | Lt | Le | Gt | Ge | LabelEq
data ForBoolExpr a b = 
             | True
             | False
             | TestPos ForTest a a
             | LabelAt a b
             | Not BoolExpr
             | Bin BinOp BoolExpr BoolExpr

data ForDirection = LeftToRight | RightToLeft

-- p = position variables
-- b = boolean variables
-- l = label s
data ForStmt p b l = 
             -- assigns to true
             | SetTrue b
             -- if expression
             | If BoolExpr Stmt Stmt
             -- for loop with variable a
             -- direction, and using boolean
             -- variables [p].
             | For a ForDirection [p] Stmt
             -- prints what is a position p
             | PrintPos p
             -- prints the value "l" directly
             | PrintLbl l
data Stmt p b l = [ForStmt p b l]
data ForProgram p b l = ForProgram [p] (Stmt p b l)
```


### First order interpretations

```haskell
class Fin a where
    fin :: [a]


data BinOp  = Conj | Disj | Impl | Equiv
data TestOp = Eq | Neq | Lt | Le | Gt | Ge | LabelEq

data Formula a b = 
             | True
             | False
             | TestPos TestOp a a
             | LabelAt a b
             | Not Formula
             | Bin BinOp Formula Formula
             | Forall a Formula
             | Exists a Formula

-- a = name of variables in the domain
-- b = name of the labels 
-- c = number of colors
data Interpretation a b c = Interpretation {
    domain_formula :: c -> Formula a b,
    order_formula  :: c -> c -> Formula a b,
    label_formula  :: c -> Formula a b,
    copy_formula   :: c -> Formula a b,
    arity          :: c -> Int,
}
```
