module LambdaCalculus

-- import Parser.Advanced
-- import Pratt.Advanced
import Parser
import Pratt

-- %hide Parser.Advanced.(|=)
-- %hide Pratt.Advanced.subExpression
-- %hide Parser.Advanced.spaces
-- %hide Pratt.Advanced.infixLeft
-- %hide Pratt.Advanced.postfix
-- %hide Parser.Advanced.(|.)
-- %hide Pratt.Advanced.prefix'
-- %hide Pratt.Advanced.literal
-- %hide Parser.Advanced.run
-- %hide Parser.Advanced.DeadEnd
-- %hide Parser.Advanced.oneOf


Name : Type
Name = String

data R  = Zero -- 0
        | One -- 0
        | MkVar String -- x

data Expr
    = Var String -- x
    | Lambda Name Expr -- \x . expr
    | App Expr Expr  -- expr expr
    | MkList (List Expr) -- [expr, ..., expr]
    | Pair Expr Expr -- expr, expr
    | Equality Expr Expr --- expr = expr
    | Proj1 Expr -- expr.p1
    | Successor Expr -- S expr
    | PathElim Expr R -- expr @ r



oneOrMoreSpaces : Parser ()
oneOrMoreSpaces = chompIf (\c => c == ' ' || c == '\n' || c == '\r')
                      |. spaces



parenthesizedExpression : Pratt.Config Expr -> Parser Expr
parenthesizedExpression config =
      pure id
        |. symbol "("
        |= Pratt.subExpression 0 config
        |. symbol ")"


listExpr : Config Expr -> Parser Expr
listExpr config =
     pure MkList
        |= sequence
          (MkSequence
            { start = "["
            , separator = ","
            , end = "]"
            , spaces = spaces
            , item = subExpression 0 config
            , trailing = Forbidden
            })


lambda : Parser ()
lambda =
    symbol "\\"


varName : Parser String
varName =
    variable
        (MkVariable { start = isLower
        , inner = \c => isAlphaNum c || c == '_'
        , reserved = [ "S" ]
        })


var : Parser Expr
var =
    map Var varName

rParser : Parser R
rParser = oneOf [pure Zero |. (keyword "0"), pure One |. (keyword "1"), map MkVar varName]

pathElim : Int -> Config Expr -> ( Int, Expr -> Parser Expr )
pathElim n config = (n, \expr => pure (PathElim expr)
                                  |. symbol "@"
                                  |. spaces
                                  |= rParser )

-- infix' : Int -> Parser () -> Parser rhs -> (Expr -> rhs -> Expr) -> Config Expr -> ( Int, Expr -> Parser Expr )
-- infix' n parserOperator parserRhs constructor config = (n, \expr => pure (constructor expr)
--                                   |. parserOperator
--                                   |. spaces
--                                   |= parserRhs )

lambdaExpr : Config Expr -> Parser Expr
lambdaExpr config =
      pure Lambda
        |. symbol "$"
        |. spaces
        |= varName
        |. spaces
        |. symbol "."
        |. spaces
        |= subExpression 0 config

lambdaCalcExpression : Parser Expr
lambdaCalcExpression =
    Pratt.expression
        (MkConfig { oneOf =
            [ prefix' 5 (keyword "S") Successor
            , literal var
            , lambdaExpr
            , listExpr
            , parenthesizedExpression
            ]
        , andThenOneOf =
            [ infixLeft 3 (symbol ",") Pair
            , infixLeft 1 (symbol "=") Equality
            , infixLeft 5 spaces App
            , postfix 10 (symbol ".p1") Proj1
            , pathElim 3
            ]
        , spaces = spaces
        })


p : Parser Expr
p =
      pure id
        |= lambdaCalcExpression
        |. end


test : Either (List DeadEnd) Expr
test = run p "$x . z  x,y = z  f , g  ($z . x y z)"
