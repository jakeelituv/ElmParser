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
expression config = Mk $ Advanced.expression config

public export
subExpression : Int -> Config expr -> Parser expr
subExpression n config =
    Mk $ Advanced.subExpression n config

public export
literal : Parser expr -> Config expr -> Parser expr
literal (Mk p) config =
    Mk $ Advanced.literal p config

public export
constant : Parser () -> expr -> Config expr -> Parser expr
constant (Mk p) x config =
    Mk $ Advanced.constant p x config

public export
prefix' : Int -> Parser () -> (expr -> expr) -> Config expr -> Parser expr
prefix' n (Mk p) f config =
    Mk $ Advanced.prefix' n p f config

public export
infixLeft : Int -> Parser () -> (expr -> expr -> expr) -> Config expr -> ( Int, expr -> Parser expr )
infixLeft n (Mk p) f config =
    let (num, g) = Advanced.infixLeft n p f config in (num, \x => Mk $ g x)

public export
infixRight : Int -> Parser () -> (expr -> expr -> expr) -> Config expr -> ( Int, expr -> Parser expr )
infixRight n (Mk p) f config =
    (let (num, g) = Advanced.infixRight n p f config in (num, \x => Mk $ g x))

public export
postfix : Int -> Parser () -> (expr -> expr) -> Config expr -> ( Int, expr -> Parser expr )
postfix n (Mk p) f config =
  let (num, g) = Advanced.postfix n p f config in (num, \x => Mk $ g x)
