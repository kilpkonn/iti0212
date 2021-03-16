module RPNCalculator

import Data.Strings
import Data.List
import System
import System.File

import StackLang


mapToMaybeEntry : String -> Maybe (Entry Nat)
mapToMaybeEntry x = if x == "+" then Just $ Func (+)
              else if x == "*" then Just $ Func (*)
              else if x == "r" then Just $ Op ?rhs_r
              else if x == "p" then Just $ Op ?rhs_p
              else case parsePositive x of
                        Nothing => Nothing -- TODO: This should throw
                        Just n  => Just $ Elem n


filterNothing : List (Maybe a) -> List a
filterNothing []               = []
filterNothing (Nothing :: xs)  = filterNothing xs
filterNothing ((Just x) :: xs) = x :: (filterNothing xs)


parseInput : (input : String) -> Stack (Entry Nat)
parseInput input = stackFromList $
                   reverse $
                   filterNothing $ 
                   map mapToMaybeEntry (words input)


public export
eval : (input : String) -> Maybe Nat 
eval input = case run (parseInput input) of
                  Nothing => Nothing
                  Just (Elem n :: Empty) => Just n
                  Just _ => Nothing


main :  IO ()
main = case !getArgs of
       _ :: x :: xs => do
            file <- readFile x
            case file of
                Left err  => putStr "Error reading file!"
                Right content  => case eval content of
                       Nothing => putStr content
                       Just n  => putStr (show n) >>= (\_ => pure())
       _ => putStr "Please specify file name!"


