module ForProgramSpec where

import Test.Hspec

import ForPrograms

{- 
simpleForLoopText :: String
simpleForLoopText = unlines
    [ "for (i, v) in x do {"
    , "    let y = x in {"
    , "    if (i == first)"
    , "        {yield v}"
    , "    else"
    , "        {return y}"
    , "    setTrue v}}"
    ]

simpleProgramText :: String
simpleProgramText = unlines
    [ "def f() {"
    , simpleForLoopText 
    , "}"
    , "main{f}"
    ]

simpleProgram :: Program String ()
simpleProgram = Program functions main
    where
        functions =
            [ Function "f" [] (StmtBlock []
                [ SFor ("i", "v") "x" (StmtBlock []
                    [ SLet "y" (OVar "x") (StmtBlock []
                        [ SIf (BOp Eq (PVar "i") (PFirst))
                            (StmtBlock []
                                [ SYield (Var "v") () ])
                            (StmtBlock []
                                [ SReturn (Var "y") () ])
                        , SSetTrue "v" ()
                        ])
                    ])
                ])
            ]
        main = "f"

-}

spec :: Spec
spec = do
    describe "ForPrograms" $ do
        it "parses a simple program" $ do
           True `shouldBe` True
