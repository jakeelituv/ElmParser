module Parser
import public Parser.Utils
import Parser.Advanced as A

infixl 0 |>
infixl 5 |=
infixr 6 |.



public export
data Problem = Expecting String
              | ExpectingInt
              | ExpectingHex
              | ExpectingOctal
              | ExpectingBinary
              | ExpectingDouble
              | ExpectingNumber
              | ExpectingVariable
              | ExpectingSymbol String
              | ExpectingKeyword String
              | ExpectingEnd
              | UnexpectedChar
              | MkProblem String
              | BadRepeat

public export
data Parser : Type -> Type where
  Mk : A.Parser Void Problem a -> Parser a

public export
Functor Parser where
  map f (Mk parser) = Mk (map f parser)

public export
Applicative Parser where
  pure x = Mk (pure x)
  (Mk parserFunc) <*> (Mk parserArg) = Mk (parserFunc <*> parserArg)

public export
Monad Parser where
  (Mk parser) >>= f =
  Mk $
    do x <- parser
       let (Mk y) = f x
       y

public export
record DeadEnd where
  constructor MkDeadEnd
  row : Nat
  col : Nat
  problem : Problem

public export
problemToDeadEnd : A.DeadEnd Void Problem -> DeadEnd
problemToDeadEnd (MkDeadEnd row col problem' _)
  = MkDeadEnd row col problem'

public export
run : Parser a -> String -> Either (List DeadEnd) a
run (Mk parser) source
  = case A.run parser source of
      (Left problems) => Left (map problemToDeadEnd problems)
      (Right x) => Right x

public export
deadEndsToString : List DeadEnd -> String
deadEndsToString deadEnds =
  "TODO deadEndsToString"

public export
succeed : a -> Parser a
succeed x = Mk (A.succeed x)

public export
(|=) : Parser (a -> b) -> Parser a -> Parser b
(|=) parseFunc parseArg =
  pure $ !parseFunc !parseArg

public export
(|.) : Parser keep -> Parser _ -> Parser keep
(|.) keepParser ignoreParser =
    [| const keepParser ignoreParser |]


public export
keeper : Parser (a -> b) -> Parser a -> Parser b
keeper =
  Parser.(|=)

public export
ignorer : Parser keep -> Parser _ -> Parser keep
ignorer =
  Parser.(|.)


public export
lazy : (() -> Parser a) -> Parser a
lazy f = let test = A.lazy
             Mk res = f () in Mk $ test (\x => res)

public export
andThen : (a -> Parser b) -> Parser a -> Parser b
andThen f x =
  x >>= f

public export
problem : String -> Parser a
problem msg =
  Mk $ A.problem (MkProblem msg)

oneOfHelp : List (Parser a) -> List (Parser Void Problem a)
oneOfHelp [] = []
oneOfHelp ((Mk parser) :: xs) = parser :: oneOfHelp xs

public export
oneOf : List (Parser a) -> Parser a
oneOf xs = Mk (A.oneOf (oneOfHelp xs))


public export
backtrackable : Parser a -> Parser a
backtrackable (Mk parser) = Mk (A.backtrackable parser)

public export
commit : a -> Parser a
commit x =
  Mk (A.commit x)

public export
toToken : String -> A.Token Problem
toToken str =
  A.MkToken str (Expecting str)

public export
token : String -> Parser ()
token str =
  Mk (A.token (toToken str))

public export
loop : state -> (state -> Parser (Step state a)) -> Parser a
loop state callback =
  Mk $ A.loop state (\s => let Mk res = callback s in res)

public export
int : Parser Int
int =
  Mk $ A.int ExpectingInt ExpectingInt

public export
float : Parser Double
float =
  Mk $ A.float ExpectingDouble ExpectingDouble


public export
record Number a where
  constructor MkNumber
  int : Maybe (Int -> a)
  hex : Maybe (Int -> a)
  octal : Maybe (Int -> a)
  binary : Maybe (Int -> a)
  float : Maybe (Double -> a)

fromMaybe : x -> Maybe a -> Either x a
fromMaybe x Nothing = Left x
fromMaybe x (Just y) = Right y


public export
number : Number a -> Parser a
number i =
  Mk $ A.number $ MkNumber
    (fromMaybe ExpectingInt i.int)
    (fromMaybe ExpectingHex i.hex)
    (fromMaybe ExpectingOctal i.octal)
    (fromMaybe ExpectingBinary i.binary)
    (fromMaybe ExpectingDouble i.float)
    ExpectingNumber
    ExpectingNumber

public export
symbol : String -> Parser ()
symbol str =
  Mk $ A.symbol (A.MkToken str (ExpectingSymbol str))

public export
keyword : String -> Parser ()
keyword kwd =
  Mk $ A.keyword (A.MkToken kwd (ExpectingKeyword kwd))

public export
end : Parser ()
end =
  Mk $ A.end ExpectingEnd

public export
getChompedString : Parser a -> Parser String
getChompedString (Mk p)=
  Mk $ A.getChompedString p

public export
mapChompedString : (String -> a -> b) -> Parser a -> Parser b
mapChompedString f (Mk p) =
  Mk $ A.mapChompedString f p

public export
chompIf : (Char -> Bool) -> Parser ()
chompIf isGood =
  Mk $ A.chompIf isGood UnexpectedChar

public export
chompWhile : (Char -> Bool) -> Parser ()
chompWhile f =
  Mk $ A.chompWhile f

public export
chompUntil : String -> Parser ()
chompUntil str =
  Mk $ A.chompUntil (toToken str)

public export
chompUntilEndOr : String -> Parser ()
chompUntilEndOr x =
  Mk $ A.chompUntilEndOr x

public export
withIndent : Nat -> Parser a -> Parser a
withIndent n (Mk p) =
  Mk $ A.withIndent n p

public export
getIndent : Parser Nat
getIndent =
  Mk $ A.getIndent

public export
getPosition : Parser (Nat, Nat)
getPosition =
  Mk A.getPosition

public export
getRow : Parser Nat
getRow =
  Mk A.getRow

public export
getCol : Parser Nat
getCol =
  Mk A.getCol

public export
getOffset : Parser Int
getOffset =
  Mk A.getOffset

public export
getSource : Parser String
getSource =
  Mk A.getSource

public export
record Variable where
  constructor MkVariable
  start : Char -> Bool
  inner : Char -> Bool
  reserved : List String

public export
variable : Variable -> Parser String
variable i = Mk $
  A.variable $
    A.MkVariable
      i.start
      i.inner
      i.reserved
      ExpectingVariable


public export
record Sequence a where
  constructor MkSequence
  start : String
  separator : String
  end : String
  spaces : Parser ()
  item : Parser a
  trailing : Trailing

public export
sequence : Sequence a -> Parser (List a)
sequence (MkSequence start separator end (Mk spaces) (Mk item) trailing) =
  Mk $ A.sequence $
   A.MkSequence
    (toToken start)
    (toToken separator)
    (toToken end)
    spaces
    item
    trailing

public export
spaces : Parser ()
spaces =
  Mk A.spaces

public export
lineComment : String -> Parser ()
lineComment str =
  Mk $ A.lineComment (toToken str)

public export
multiComment : String -> String -> Nestable -> Parser ()
multiComment opn clse nstable =
  Mk $ A.multiComment (toToken opn) (toToken clse) nstable
