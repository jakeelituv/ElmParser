module Pratt.Advanced

import Parser.Advanced
import Parser.Utils

public export
record Config c x e where
  constructor MkConfig
  oneOf : List (Config c x e -> Parser c x e)
  andThenOneOf : List (Config c x e -> ( Int, e -> Parser c x e ))
  spaces : Parser c x ()

filter : ( Int, e -> Parser c x e ) -> Int -> e -> Maybe (Parser c x e)
filter ( precedence, parser ) currentPrecedence leftExpression =
    if precedence > currentPrecedence then
        Just (parser leftExpression)

    else
        Nothing


filterMap : (a -> Maybe b) -> List a -> List b
filterMap f [] = []
filterMap f (x :: xs) =
  case f x of
     Nothing => filterMap f xs
     (Just y) => y :: filterMap f xs

operation : Config c x e -> Int -> e -> Parser c x e
operation config precedence leftExpression =
    Parser.Advanced.oneOf $
        filterMap
            (\toOperation => filter (toOperation config) precedence leftExpression)
            config.andThenOneOf


expressionHelp : ( Config c x e, Int, e ) -> Parser c x (Step ( Config c x e, Int, e ) e)
expressionHelp ( config, precedence, leftExpression ) =
    succeed id
        |. config.spaces
        |= oneOf
            [ map
                (\expr => Loop ( config, precedence, expr ))
                (operation config precedence leftExpression)
            , succeed (Done leftExpression)
            ]
public export
subExpression : Int -> Config c x e -> Parser c x e
subExpression precedence config =
    succeed id
        |. config.spaces
        |= lazy (\_ => oneOf $ map (\f => f config) config.oneOf)
        |> andThen (\leftExpression => loop ( config, precedence, leftExpression ) expressionHelp)


public export
expression : Config c x e -> Parser c x e
expression config =
    subExpression 0 config

public export
literal : Parser c x e -> Config c x e -> Parser c x e
literal =
    const

public export
constant : Parser c x () -> e -> Config c x e -> Parser c x e
constant constantParser e _ =
    map (const e) constantParser

public export
prefix' : Int -> Parser c x () -> (e -> e) -> Config c x e -> Parser c x e
prefix' precedence operator apply config =
    succeed apply
        |. operator
        |= subExpression precedence config

infixHelp : ( Int, Int ) -> Parser c x () -> (e -> e -> e) -> Config c x e -> ( Int, e -> Parser c x e )
infixHelp ( leftPrecedence, rightPrecedence ) operator apply config =
    ( leftPrecedence
    , \left =>
        succeed (apply left)
            |. operator
            |= subExpression rightPrecedence config
    )

public export
infixLeft : Int -> Parser c x () -> (e -> e -> e) -> Config c x e -> ( Int, e -> Parser c x e )
infixLeft precedence =
    infixHelp ( precedence, precedence )

public export
infixRight : Int -> Parser c x () -> (e -> e -> e) -> Config c x e -> ( Int, e -> Parser c x e )
infixRight precedence =
    infixHelp ( precedence, precedence - 1 )

public export
postfix : Int -> Parser c x () -> (e -> e) -> Config c x e -> ( Int, e -> Parser c x e )
postfix precedence operator apply _ =
    ( precedence
    , \left => map (\_ => apply left) operator
    )
