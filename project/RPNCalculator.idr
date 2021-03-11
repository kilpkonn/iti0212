module RPNCalculator

import Data.Strings
import Data.List

import StackLang


mapToMaybeNat : String -> Maybe (Entry Nat)
mapToMaybeNat x = if x == "+" then Just $ Func (+)
              else if x == "*" then Just $ Func (*)
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
                   map mapToMaybeNat (words input)

public export
eval : (input : String) -> Maybe Nat 
eval input = case run (parseInput input) of
                  Nothing => Nothing
                  Just (Elem n :: Empty) => Just n
                  Just _ => Nothing



