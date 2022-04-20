module Pratt

import Parser.Advanced
import Parser
import Pratt.Advanced as Advanced
import public Pratt.Config

public export
Config : Type -> Type
Config expr =  Config Void Problem expr

public export
expression : Config expr -> Parser expr
expression config = Advanced.expression config

public export
subExpression : Int -> Config expr -> Parser expr
subExpression =
    Advanced.subExpression

public export
literal : Parser expr -> Config expr -> Parser expr
literal =
    Advanced.literal

public export
constant : Parser () -> expr -> Config expr -> Parser expr
constant =
    Advanced.constant

public export
prefix' : Int -> Parser () -> (expr -> expr) -> Config expr -> Parser expr
prefix' =
    Advanced.prefix'

public export
infixLeft : Int -> Parser () -> (expr -> expr -> expr) -> Config expr -> ( Int, expr -> Parser expr )
infixLeft =
    Advanced.infixLeft

public export
infixRight : Int -> Parser () -> (expr -> expr -> expr) -> Config expr -> ( Int, expr -> Parser expr )
infixRight =
    Advanced.infixRight

public export
postfix : Int -> Parser () -> (expr -> expr) -> Config expr -> ( Int, expr -> Parser expr )
postfix =
  Advanced.postfix
