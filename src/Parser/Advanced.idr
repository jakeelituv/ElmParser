module Parser.Advanced

import Data.String
import Data.List
import Control.Monad.State
import Decidable.Equality
import Data.Vect
import Parser.Utils

infixl 0 |>
infixl 5 |=
infixr 6 |.


public export
(|>) : forall a, b . (x : a) -> (f : a -> b) -> b
(|>) x f = f x


public export
intToNat : Int -> Nat
intToNat x = integerToNat (cast x)




bagToList : Bag c x -> List (DeadEnd c x) -> List (DeadEnd c x)
bagToList Empty xs = xs
bagToList (AddRight bag x) list = bagToList bag (x :: list)
bagToList (Append bag1 bag2) list = bagToList bag1 (bagToList bag2 list)

initParserState : String -> ParserState ctx
initParserState src = MkParserState
                        src --src
                        0 --offset
                        1 --indent
                        [] --context
                        1 --row
                        1 --col

public export
run : Parser c x a -> String -> Either (List (DeadEnd c x)) a
run (MkParser parse) src =
  case parse $ initParserState src of
    (Good _ value _) => Right value
    (Bad _ bag) => Left (bagToList bag [])

fromState : ParserState c -> x -> Bag c x
fromState (MkParserState src offset indent context row col) z
  = AddRight Empty (MkDeadEnd row col z context)


fromInfo : Nat -> Nat -> x -> List (Located c) -> Bag c x
fromInfo row col x context = AddRight Empty (MkDeadEnd row col x context)



public export
problem : x -> Parser c x a
problem x =
  MkParser $ \s =>
    Bad False (fromState s x)



public export
succeed : a -> Parser c x a
succeed x =
  pure x

public export
(|=) : Parser c x (a -> b) -> Parser c x a -> Parser c x b
(|=) parseFunc parseArg =
  pure $ !parseFunc !parseArg

public export
(|.) : Parser c x keep -> Parser c x _ -> Parser c x keep
(|.) keepParser ignoreParser =
    [| const keepParser ignoreParser |]


public export
lazy : (() -> Parser c x a) -> Parser c x a
lazy thunk = MkParser $ \s =>
            let MkParser parse = thunk () in
            parse s

oneOfHelp : ParserState c -> Bag c x -> List (Parser c x a) -> PStep c x a
oneOfHelp s0 bag [] = Bad False bag
oneOfHelp s0 bag ((MkParser parse) :: remainingParsers) =
      case parse s0 of
        step@(Bad p y) => if p then step else
                             oneOfHelp s0 (Append bag y) remainingParsers
        step@(Good p y s) => step

public export
oneOf : List (Parser c x a) -> Parser c x a
oneOf parsers =
  MkParser $ \s => oneOfHelp s Empty parsers

public export
data Step parserState a =
    Loop parserState
  | Done a

loopHelp : Bool -> parserState -> (parserState -> Parser c x (Step parserState a)) -> ParserState c -> PStep c x a
loopHelp p parserState callback s0 =
    let MkParser parse = callback parserState in
        case parse s0 of
            (Bad p1 x) => Bad (p || p1) x
            (Good p1 (Loop newState) s1) => loopHelp (p || p1) newState callback s1
            (Good p1 (Done result) s1) => Good (p || p1) result s1

public export
loop : parserState -> (parserState -> Parser c x (Step parserState a)) -> Parser c x a
loop parserState callback =
  MkParser $ \s =>
    loopHelp False parserState callback s

public export
backtrackable : Parser c x a -> Parser c x a
backtrackable (MkParser parse) =
    MkParser $ \s =>
      case parse s of
        (Bad _ x) => Bad False x
        (Good _ a s1) => Good False a s1

public export
commit : a -> Parser c x a
commit a =
  MkParser $ \s =>
    Good True a s

public export
data Token : (x : Type) -> Type where
  MkToken : (str : String) -> (expecting : x) -> Token x


public export
token : Token x -> Parser c x ()
token (MkToken str expecting) =
    let progress = not $ str == "" in
      MkParser $ \s =>
    let (newOffset, newRow, newCol) =
          isSubString str s.offset s.row s.col s.src
    in
    if newOffset == -1 then
      Bad False (fromState s expecting)
    else
      Good progress () $
        MkParserState
          s.src --src
          newOffset --offset
          s.indent --indent
          s.context --context
          newRow --row
          newCol --col

public export
keyword : Token x -> Parser c x ()
keyword (MkToken kwd expecting) =
  let progress = not $ kwd == "" in
    MkParser $ \s =>
  let (newOffset, newRow, newCol) =
        isSubString kwd s.offset s.row s.col s.src
  in
  if newOffset == -1 || 0 <= isSubChar (\c => isAlphaNum c || c == '_') newOffset s.src then
    Bad False (fromState s expecting)
  else
    Good progress () $
      MkParserState
        s.src --src
        newOffset --offset
        s.indent --indent
        s.context --context
        newRow --row
        newCol --col

public export
symbol : Token x -> Parser c x ()
symbol = token

public export
end : x -> Parser c x ()
end x =
  MkParser $ \s =>
      if cast (length s.src) == s.offset then
        Good False () s
      else
        Bad False (fromState s x)

public export
mapChompedString : (String -> a -> b) -> Parser c x a -> Parser c x b
mapChompedString func (MkParser parse) =
  MkParser $ \s0 =>
    case parse s0 of
      Bad p x =>
        Bad p x
      Good p a s1 =>
        Good p (func (substr (intToNat s0.offset) (intToNat $ s1.offset - s0.offset) s0.src) a) s1

public export
getChompedString : Parser c x a -> Parser c x String
getChompedString parser =
  mapChompedString const parser

public export
chompIf : (Char -> Bool) -> x -> Parser c x ()
chompIf isGood expecting =
  MkParser $ \s =>
    let newOffset = isSubChar isGood s.offset s.src in
    if newOffset == -1 then
      Bad False (fromState s expecting)
    else if newOffset == -2 then
      Good True () $
        MkParserState
          s.src --src
          (s.offset + 1) --offset
          s.indent --indent
          s.context --context
          (s.row + 1) --row
          1 --col
    else
      Good True () $
        MkParserState
          s.src --src
          newOffset --offset
          s.indent --indent
          s.context --context
          s.row --row
          (s.col + 1) --col

chompWhileHelp : (Char -> Bool) -> Int -> Nat -> Nat -> ParserState c -> PStep c x ()
chompWhileHelp isGood offst row col s0 =
  let
    newOffset = isSubChar isGood offst s0.src
  in
  -- no match
  if newOffset == -1 then
    Good ((s0.offset) < offst) () $
      MkParserState
       s0.src --src
       offst --offset
       s0.indent --indent
       s0.context --context
       row --row
       col --col


  -- matched a newline
  else if newOffset == -2 then
    chompWhileHelp isGood (offst + 1) (row + 1) 1 s0

  -- normal match
  else
    chompWhileHelp isGood newOffset row (col + 1) s0

public export
chompWhile : (Char -> Bool) -> Parser c x ()
chompWhile isGood =
  MkParser $ \s =>
    chompWhileHelp isGood s.offset s.row s.col s

public export
chompUntil : Token x -> Parser c x ()
chompUntil (MkToken str expecting) =
  MkParser $ \s =>
    let
      (newOffset, newRow, newCol) =
        findSubString str s.offset s.row s.col s.src
    in
    if newOffset == -1 then
      Bad False (fromInfo newRow newCol expecting s.context)

    else
      Good (s.offset < newOffset) () $
        MkParserState
         s.src --src
         newOffset --offset
         s.indent --indent
         s.context --context
         newRow --row
         newCol --col

public export
chompUntilEndOr : String -> Parser c x ()
chompUntilEndOr str =
 MkParser $ \s =>
   let
     (newOffset, newRow, newCol) =
       findSubString str s.offset s.row s.col s.src

     adjustedOffset =
       if newOffset < 0 then cast (length s.src) else newOffset
   in
   Good (s.offset < adjustedOffset) () $
    MkParserState
      s.src --src
      adjustedOffset --offset
      s.indent --indent
      s.context --context
      newRow --row
      newCol --col

changeContext : List (Located c) -> ParserState c -> ParserState c
changeContext newContext s =
  MkParserState
   s.src --src
   s.offset --offset
   s.indent --indent
   newContext --context
   s.row --row
   s.col --col


public export
inContext : c -> Parser c x a -> Parser c x a
inContext ctx (MkParser parse) =
  MkParser $ \s0 =>
    case parse (changeContext (MkLocated s0.row s0.col ctx :: s0.context) s0) of
      Good p a s1 =>
        Good p a (changeContext s0.context s1)

      step @ (Bad _ _) =>
        step

public export
getIndent : Parser c x Nat
getIndent =
  MkParser $ \s => Good False s.indent s


changeIndent : Nat -> ParserState c -> ParserState c
changeIndent newIndent s =
  MkParserState
   s.src --src
   s.offset --offset
   newIndent --indent
   s.context --context
   s.row --row
   s.col --col

public export
withIndent : Nat -> Parser c x a -> Parser c x a
withIndent newIndent (MkParser parse) =
 MkParser $ \s0 =>
  let (MkParserState _ _ indent _ _ _) = s0 in
   case parse (changeIndent newIndent s0) of
     Good p a s1 =>
       Good p a (changeIndent indent s1)

     Bad p x =>
       Bad p x

public export
getPosition : Parser c x (Nat, Nat)
getPosition =
 MkParser $ \s => Good False (s.row, s.col) s


public export
getRow : Parser c x Nat
getRow =
 MkParser $ \s => Good False s.row s


public export
getCol : Parser c x Nat
getCol =
 MkParser $ \s => Good False s.col s


public export
getOffset : Parser c x Int
getOffset =
 MkParser $ \s => Good False s.offset s


public export
getSource : Parser c x String
getSource =
 MkParser $ \s => Good False s.src s


varHelp : (Char -> Bool) -> Int -> Nat -> Nat -> String -> Nat -> List (Located c) -> ParserState c
varHelp isGood offset row col src indent context =
 let
   newOffset = isSubChar isGood offset src
 in
 if newOffset == -1 then
   MkParserState
    src --src
    offset --offset
    indent --indent
    context --context
    row --row
    col --col

 else if newOffset == -2 then
   varHelp isGood (offset + 1) (row + 1) 1 src indent context
 else
   varHelp isGood newOffset row (col + 1) src indent context

public export
record Sequence c x a where
  constructor MkSequence
  start : Token x
  separator : Token x
  end : Token x
  spaces : Parser c x ()
  item : Parser c x a
  trailing : Trailing

public export
record Variable x where
  constructor MkVariable
  start : Char -> Bool
  inner : Char -> Bool
  reserved : List String
  expecting : x

revAlways : a -> b -> b
revAlways _ b =
  b

skip : Parser c x _ -> Parser c x keep -> Parser c x keep
skip iParser kParser =
  [| revAlways iParser kParser |]

sequenceEndForbidden : Parser c x () -> Parser c x () -> Parser c x a -> Parser c x () -> List a -> Parser c x (Step (List a) (List a))
sequenceEndForbidden ender ws parseItem sep revItems =
  let
    chompRest = \item =>
      sequenceEndForbidden ender ws parseItem sep (item :: revItems)
  in
  skip ws $
    oneOf [ skip sep $ skip ws $ map (\item => Loop (item :: revItems)) parseItem
      , ender |> map (\_ => Done (reverse revItems))]


sequenceEndOptional : Parser c x () -> Parser c x () -> Parser c x a -> Parser c x () -> List a -> Parser c x (Step (List a) (List a))
sequenceEndOptional ender ws parseItem sep revItems =
  let
    parseEnd =
      map (\_ => Done (reverse revItems)) ender
  in
  skip ws $
    oneOf
      [ skip sep $ skip ws $
          oneOf
            [ parseItem |> map (\item => Loop (item :: revItems))
            , parseEnd
            ]
      , parseEnd
      ]


sequenceEndMandatory : Parser c x () -> Parser c x a -> Parser c x () -> List a -> Parser c x (Step (List a) (List a))
sequenceEndMandatory ws parseItem sep revItems =
  oneOf
    [ map (\item => Loop (item :: revItems)) $
       parseItem
       |. ws
       |. sep
       |. ws
    , map (\_ => Done (reverse revItems)) (succeed ())
    ]

sequenceEnd : Parser c x () -> Parser c x () -> Parser c x a -> Parser c x () -> Trailing -> Parser c x (List a)
sequenceEnd ender ws parseItem sep trailing =
  oneOf
    [ parseItem >>= chompRest trailing ender ws parseItem sep
    , ender |> map (\_ => [])
    ] where
  chompRest : Trailing -> Parser c x () -> Parser c x () -> Parser c x a -> Parser c x () -> a -> Parser c x (List a)
  chompRest trailing ender ws parseItem sep item =
    case trailing of
      Forbidden =>
        loop [item] (sequenceEndForbidden ender ws parseItem sep)

      Optional =>
        loop [item] (sequenceEndOptional ender ws parseItem sep)

      Mandatory =>
          ( skip ws $ skip sep $ skip ws $
              loop [item] (sequenceEndMandatory ws parseItem sep)
          )
          |. ender


public export
sequence : Sequence c x a -> Parser c x (List a)
sequence i =
 skip (token i.start) $
 skip i.spaces $
   sequenceEnd (token i.end) i.spaces i.item (token i.separator) i.trailing

public export
variable : Variable x -> Parser c x String
variable i =
 MkParser $ \s =>
   let
     firstOffset =
       isSubChar i.start s.offset s.src
   in
   if firstOffset == -1 then
     Bad False (fromState s i.expecting)
   else
     let
       s1 =
         if firstOffset == -2 then
           varHelp i.inner (s.offset + 1) (s.row + 1) 1 s.src s.indent s.context
         else
           varHelp i.inner firstOffset s.row (s.col + 1) s.src s.indent s.context

       name =
         substr (intToNat s.offset) (intToNat $ s1.offset - s.offset) s.src
     in
     if elem name i.reserved then
       Bad False (fromState s i.expecting)
     else
       Good True name s1


public export
spaces : Parser c x ()
spaces =
 chompWhile (\c => c == ' ' || c == '\n' || c == '\r')


public export
lineComment : Token x -> Parser c x ()
lineComment start =
 token start
 |. chompUntilEndOr "\n"

public export
data Nestable = NotNestable | IsNestable

isChar : Char -> Bool
isChar char =
  True

nestableHelp : (Char -> Bool) -> Parser c x () -> Parser c x () -> x -> Int -> Parser c x ()
nestableHelp isNotRelevant opn cls expectingClose nestLevel =
  skip (chompWhile isNotRelevant) $
    oneOf [if nestLevel == 1 then cls
           else cls >>= (\_ => nestableHelp isNotRelevant opn cls expectingClose (nestLevel - 1))
          , opn >>= (\_ => nestableHelp isNotRelevant opn cls expectingClose (nestLevel + 1))
          , chompIf isChar expectingClose
             >>= (\_ => nestableHelp isNotRelevant opn cls expectingClose nestLevel)
          ]

nestableComment : Token x -> Token x -> Parser c x ()
nestableComment opn @ (MkToken oStr oX) cls @ (MkToken cStr cX) =
  case unpack oStr of
    [] => problem oX
    (openChar :: _) =>
      case unpack cStr of
        [] => problem cX
        (closeChar :: _) =>
          token opn
          |. nestableHelp (\char => char /= openChar && char /= closeChar) (token opn)
              (token cls) cX 1

public export
multiComment : Token x -> Token x -> Nestable -> Parser c x ()
multiComment opn cls NotNestable =
       token opn
       |. chompUntil cls
multiComment opn cls IsNestable =
       nestableComment opn cls


bumpOffset : Int -> ParserState c -> ParserState c
bumpOffset newOffset (MkParserState src offset indent context row col) =
  MkParserState
   src --src
   newOffset --offset
   indent --indent
   context --context
   row --row
   (col + intToNat (newOffset - offset)) --col


finalizeInt : x -> Either x (Int -> a) -> Int -> (Int, Int) -> ParserState c -> PStep c x a
finalizeInt invalid (Left x) startOffset (endOffset, n) s = Bad True (fromState s x)
finalizeInt invalid (Right toValue) startOffset (endOffset, n) s =
      if startOffset == endOffset
        then Bad (s.offset < startOffset) (fromState s invalid)
        else Good True (toValue n) (bumpOffset endOffset s)

consumeExp : Int -> String -> Int
consumeExp offset src =
  if isAsciiCode '\x0065' {- e -} offset src || isAsciiCode '\x0045' {- E -} offset src then
    let
      eOffset = offset + 1

      expOffset =
        if isAsciiCode '\x002B' {- + -} eOffset src || isAsciiCode '\x002D' {- - -} eOffset src then
          eOffset + 1
        else
          eOffset

      newOffset = chompBase10 expOffset src
    in
    if expOffset == newOffset then
      -newOffset
    else
      newOffset

  else
    offset

consumeDotAndExp : Int -> String -> Int
consumeDotAndExp offset src =
  if isAsciiCode '\x002E' {- . -} offset src then
    consumeExp (chompBase10 (offset + 1) src) src
  else
    consumeExp offset src

finalizeFloat : x -> x -> Either x (Int -> a) -> Either x (Double -> a) -> (Int, Int) -> ParserState c -> PStep c x a
finalizeFloat invalid expecting intSettings floatSettings intPair
    s @ (MkParserState src offset indent context row col) =
  let
    intOffset = fst intPair
    floatOffset = consumeDotAndExp intOffset src
  in
  if floatOffset < 0 then
    Bad True (fromInfo row (intToNat (cast col - (floatOffset + offset))) invalid context)

  else if offset == floatOffset then
    Bad False (fromState s expecting)

  else if intOffset == floatOffset then
    finalizeInt invalid intSettings offset intPair s

  else
    case floatSettings of
      Left x =>
        Bad True (fromState s invalid)

      Right toValue =>
        case Data.String.parseDouble (substr (intToNat offset) (intToNat $ floatOffset - offset) src) of
          Nothing => Bad True (fromState s invalid)
          Just n => Good True (toValue n) (bumpOffset floatOffset s)

public export
record Number x a where
  constructor MkNumber
  int : Either x (Int -> a)
  hex : Either x (Int -> a)
  octal : Either x (Int -> a)
  binary : Either x (Int -> a)
  float : Either x (Double -> a)
  invalid : x
  expecting : x

public export
number : Number x a -> Parser c x a
number (MkNumber int hex octal binary float invalid expecting ) =
  MkParser $ \s =>
    let (MkParserState src offset indent context row col) = s in
    if isAsciiCode '\x0030' {- 0 -} offset src then
      let
        zeroOffset = offset + 1
        baseOffset = zeroOffset + 1
      in
      if isAsciiCode '\x0078' {- x -} zeroOffset src then
        finalizeInt invalid hex baseOffset (consumeBase16 baseOffset src) s
      else if isAsciiCode '\x006F' {- o -} zeroOffset src then
        finalizeInt invalid octal baseOffset (consumeBase 8 baseOffset src) s
      else if isAsciiCode '\x0062' {- b -} zeroOffset src then
        finalizeInt invalid binary baseOffset (consumeBase 2 baseOffset src) s
      else
        finalizeFloat invalid expecting int float (zeroOffset, 0) s

    else
      finalizeFloat invalid expecting int float (consumeBase 10 offset src) s

public export
int : x -> x -> Parser c x Int
int expecting invalid =
  number $
    MkNumber
     (Right id) --int
     (Left invalid) --hex
     (Left invalid) --octal
     (Left invalid) --binary
     (Left invalid) --float
     invalid --invalid
     expecting --expecting

public export
float : x -> x -> Parser c x Double
float expecting invalid =
  number $
    MkNumber
     (Right cast) --int
     (Left invalid) --hex
     (Left invalid) --octal
     (Left invalid) --binary
     (Right id) --float
     invalid --invalid
     expecting --expecting

export
andThen : (a -> Parser c x b) -> Parser c x a -> Parser c x b
andThen callback (MkParser parseA) =
 MkParser $ \s0 =>
   case parseA s0 of
     Bad p x =>
       Bad p x

     Good p1 a s1 =>
       let
         (MkParser parseB) =
           callback a
       in
       case parseB s1 of
         Bad p2 x =>
           Bad (p1 || p2) x

         Good p2 b s2 =>
           Good (p1 || p2) b s2
