module RPNCalculator

import Data.Strings

import StackLang


export
eval : String -> Maybe Nat
--eval s = run mapToNats (stackFromList (unpack s))


mapToMaybeNat : String -> Maybe (Entry Nat)
mapToMaybeNat x = if x == "+" then Just $ Func (+)
              else if x == "*" then Just $ Func (*)
              else case parsePositive x of
                        Nothing => Nothing -- TODO: This should throw
                        Just n  => Just $ Elem n


