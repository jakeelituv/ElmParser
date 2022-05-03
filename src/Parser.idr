module Parser

import Parser.Advanced as A
import public Parser.Utils

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
Parser : Type -> Type
Parser a = Parser Void Problem a

public export
record DeadEnd where
  constructor MkDeadEnd
  row : Int
  col : Int
  problem : Problem

public export
problemToDeadEnd : DeadEnd Void Problem -> DeadEnd
problemToDeadEnd (MkDeadEnd row col problem' _)
  = MkDeadEnd row col problem'

public export
run : Parser a -> String -> Either (List DeadEnd) a
run parser source
  = case A.run parser source of
      (Left problems) => Left (map problemToDeadEnd problems)
      (Right x) => Right x

public export
Show Problem where
  show (Expecting x) = "Expecting " ++ x
  show ExpectingInt = "Expecting an Int"
  show ExpectingHex = "Expecting a Hex"
  show ExpectingOctal = "Expecting an Octal"
  show ExpectingBinary = "Expecting a Binary"
  show ExpectingDouble = "Expecting a Double"
  show ExpectingNumber = "Expecting a number"
  show ExpectingVariable = "Expecting a variable"
  show (ExpectingSymbol x) = "Expecting a symbol " ++ x
  show (ExpectingKeyword x) = "Expecting the keyword " ++ x
  show ExpectingEnd = "Expecting the end"
  show UnexpectedChar = "Expecting a Char"
  show (MkProblem x) = "Problem " ++ x
  show BadRepeat = "Bad repeat"

public export
Show DeadEnd where
  show (MkDeadEnd row col problem) = show problem ++ " at row: " ++
                                      show row ++ ", col: " ++ show col

public export
succeed : a -> Parser a
succeed =
  A.succeed

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
lazy =
  A.lazy

public export
andThen : (a -> Parser b) -> Parser a -> Parser b
andThen =
  A.andThen

public export
problem : String -> Parser a
problem msg =
  A.problem (MkProblem msg)

public export
oneOf : List (Parser a) -> Parser a
oneOf =
  A.oneOf

public export
backtrackable : Parser a -> Parser a
backtrackable =
  A.backtrackable

public export
commit : a -> Parser a
commit =
  A.commit

public export
toToken : String -> A.Token Problem
toToken str =
  A.Tok str (Expecting str)

public export
token : String -> Parser ()
token str =
  A.token (toToken str)

public export
loop : state -> (state -> Parser (Step state a)) -> Parser a
loop state callback =
  A.loop state (\s => callback s)

public export
int : Parser Int
int =
  A.int ExpectingInt ExpectingInt

public export
float : Parser Double
float =
  A.float ExpectingDouble ExpectingDouble


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
number i = ?number_rhs
  A.number
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
  A.symbol (A.Tok str (ExpectingSymbol str))

public export
keyword : String -> Parser ()
keyword kwd =
  A.keyword (A.Tok kwd (ExpectingKeyword kwd))

public export
end : Parser ()
end =
  A.end ExpectingEnd

public export
getChompedString : Parser a -> Parser String
getChompedString =
  A.getChompedString

public export
mapChompedString : (String -> a -> b) -> Parser a -> Parser b
mapChompedString =
  A.mapChompedString

public export
chompIf : (Char -> Bool) -> Parser ()
chompIf isGood =
  A.chompIf isGood UnexpectedChar

public export
chompWhile : (Char -> Bool) -> Parser ()
chompWhile =
  A.chompWhile

public export
chompUntil : String -> Parser ()
chompUntil str =
  A.chompUntil (toToken str)

public export
chompUntilEndOr : String -> Parser ()
chompUntilEndOr =
  A.chompUntilEndOr

public export
withIndent : Int -> Parser a -> Parser a
withIndent =
  A.withIndent

public export
getIndent : Parser Int
getIndent =
  A.getIndent

public export
getPosition : Parser (Int, Int)
getPosition =
  A.getPosition

public export
getRow : Parser Int
getRow =
  A.getRow

public export
getCol : Parser Int
getCol =
  A.getCol

public export
getOffset : Parser Int
getOffset =
  A.getOffset

public export
getSource : Parser String
getSource =
  A.getSource

public export
record Variable where
  constructor MkVariable
  start : Char -> Bool
  inner : Char -> Bool
  reserved : List String

public export
variable : Variable -> Parser String
variable i =
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
  separator : Parser ()
  end : String
  spaces : Parser ()
  item : Parser a
  trailing : Trailing

public export
sequence : Sequence a -> Parser (List a)
sequence i =
  A.sequence $
   A.MkSequence
    (toToken i.start)
    i.separator
    (toToken i.end)
    i.spaces
    i.item
    i.trailing

public export
spaces : Parser ()
spaces =
  A.spaces

public export
lineComment : String -> Parser ()
lineComment str =
  A.lineComment (toToken str)

public export
multiComment : String -> String -> Nestable -> Parser ()
multiComment opn clse nstable =
  A.multiComment (toToken opn) (toToken clse) nstable
