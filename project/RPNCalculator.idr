module RPNCalculator

import Data.Strings
import Data.List
import System
import System.File

import StackLang


interface EntryMappable a where
mapToMaybeEntry : String -> Maybe (Entry Nat)


runReadInput : IO (Stack (Entry Nat)) ->  IO (Stack (Entry Nat))
runReadInput stack = do
  putStr "Please enter a command: "
  input <- getLine
  maybeEntry <- mapToMaybeEntry input
  case maybeEntry of
       Nothing => pure $ Err :: Empty
       Just c  => do
         stack <- stack
         runResult <- runIO $ pure (c :: stack)
         case runResult of
                    Just xs => pure xs
                    Nothing => pure $ Err :: Empty


implementation EntryMappable String where
mapToMaybeEntry x = if x == "+" then Just $ Func (+)
              else if x == "*" then Just $ Func (*)
              else if x == "r" then Just $ Op runReadInput
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
eval : (input : String) -> IO (Maybe Nat) 
eval input = case run (parseInput input) of
                  Nothing => pure Nothing
                  Just (Elem n :: Empty) => pure $ Just n
                  Just _ => pure Nothing


main :  IO ()
main = case !getArgs of
       _ :: x :: xs => do
            file <- readFile x
            case file of
                Left err  => putStr "Error reading file!"
                Right content  => do
                  res <- eval content 
                  case res of
                       Nothing => putStr $ "Error parsing file:" ++ content 
                       Just n  => putStr (show n) >>= (\_ => pure())
       _ => putStr "Please specify file name!"


