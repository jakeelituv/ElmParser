module Pratt.Config
import Parser.Advanced
import Parser.Utils

public export
record Config c x e where
  constructor MkConfig
  oneOf : List (Config c x e -> Parser c x e)
  andThenOneOf : List (Config c x e -> ( Int, e -> Parser c x e ))
  spaces : Parser c x ()
