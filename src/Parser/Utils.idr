module Parser.Utils
import Data.List

public export
data Trailing = Forbidden | Optional | Mandatory

isSubStringHelp : (smallString : List Char) -> (offset : Int) -> (row : Nat) ->
                  (col : Nat) -> (bigString : List Char) -> (Int, Nat, Nat)
isSubStringHelp [] offset row col bigString = (offset, row, col)
isSubStringHelp (x :: xs) offset row col (y :: ys) =
  if x == y then
    if isNL x then
      isSubStringHelp xs (offset + 1) (S row) 1 ys
    else
      isSubStringHelp xs (offset + 1) row (S col) ys
  else
    (-1, row, col)
isSubStringHelp (x :: xs) offset row col [] = (-1, row, col)

drop : Int -> List a -> List a
drop n list =
  if n <= 0 then
    list
  else
    case list of
      [] =>
        list
      x :: xs =>
        drop (n-1) xs

public export
isSubString : (smallString : String) -> (offset : Int) -> (row : Nat) ->
                  (col : Nat) -> (bigString : String) -> (Int, Nat, Nat)
isSubString smallString offset row col bigString =
    if offset + cast (length smallString) <= cast (length bigString) then
      isSubStringHelp (unpack smallString) offset row col
        (drop offset (unpack bigString))
    else
      (-1, row, col)


public export
isSubChar : (pred : Char -> Bool) -> (offset : Int) -> (string : String) -> Int
isSubChar pred offset string =
    if cast (length $ unpack string) <= offset then -1 else
      case drop offset (unpack string) of
        [] => -1
        (x :: xs) =>
          if pred x then
            if isNL x then -2 else offset + 1
          else -1

indexOfHelp : (i : Int) -> (smallString : List Char) -> (bigString : List Char) -> Int
indexOfHelp i smallString [] = -1
indexOfHelp i smallString (x :: xs) =
  if isPrefixOf smallString (x :: xs) then
      cast i
  else indexOfHelp (i + 1) smallString xs


indexOf : (smallString : String) -> (bigString : String) -> (offset : Int) -> Int
indexOf smallString bigString offset = indexOfHelp offset (unpack smallString) (drop offset $ unpack bigString)



findSubStringHelp : (target : Int) -> (newOffset : Int) -> (offset : Int) -> (row : Nat) ->
                  (col : Nat) -> (bigString : List Char) -> (Int, Nat, Nat)
findSubStringHelp target newOffset offset row col [] = (newOffset, row, col)
findSubStringHelp target newOffset offset row col (code :: xs) =
              if offset < target then
                  if isNL code then findSubStringHelp target newOffset (offset + 1) (row + 1) 1 xs
                    else findSubStringHelp target newOffset (offset + 1) row (col + 1) xs
              else (newOffset, row, col)

public export
findSubString : (smallString : String) -> (offset : Int) -> (row : Nat) ->
                  (col : Nat) -> (bigString : String) -> (Int, Nat, Nat)
findSubString smallString offset row col bigString =
        let newOffset = indexOf smallString bigString offset
            target = if newOffset < 0 then cast (length bigString)
                     else newOffset + cast (length smallString)
        in
        findSubStringHelp target newOffset offset row col (drop offset $ unpack bigString)


public export
isAsciiCode : Char -> Int -> String -> Bool
isAsciiCode code offset string =
  case drop offset $ unpack string of
    [] => False
    _ => True

-- chompBase10Helper : Int -> List Char -> Int
-- chompBase10Helper offset [] = offset
-- chompBase10Helper offset (code :: xs) =
--     if (code < '\x0030' || '\x0039' < code) then
--       offset
--     else
--       chompBase10Helper (offset + 1) xs

public export
chompBase10 : Int -> String -> Int
-- chompBase10 offset string =
--     chompBase10Helper offset (drop (intToNat offset) (unpack string))

-- consumeBaseHelp : Int -> Int -> Int -> List Char -> (Int, Int)
-- consumeBaseHelp tot base offset [] = (offset, tot)
-- consumeBaseHelp tot base offset (x :: xs) =
--     let digit = ord x - ord '\x0030' in
--     if digit < 0 || base <= digit then (offset, tot)
--       else consumeBaseHelp (base * tot + digit) base (offset + 1) xs

public export
consumeBase : Int -> Int -> String -> (Int, Int)
-- consumeBase base offset string = consumeBaseHelp 0 base offset (drop (intToNat offset) (unpack string))

-- consumeBase16Help : Int -> Int -> List Char -> (Int, Int)
-- consumeBase16Help tot offset [] = (offset, tot)
-- consumeBase16Help tot offset (code :: xs) =
--     if ('\x0030' <= code && code <= '\x0039') then
--       consumeBase16Help (16 * tot + (ord code) - (ord '\x0030')) (offset + 1) xs
--     else if ('\x0041' <= code && code <= '\x0046') then
--       consumeBase16Help (16 * tot + (ord code) - 55) (offset + 1) xs
--     else if ('\x0061' <= code && code <= '\x0066') then
--       consumeBase16Help (16 * tot + (ord code) - 87) (offset + 1) xs
--     else
--       (offset, tot)

public export
consumeBase16 : Int -> String -> (Int, Int)
-- consumeBase16 offset string =
--   consumeBase16Help 0 offset (drop (intToNat offset) (unpack string))
