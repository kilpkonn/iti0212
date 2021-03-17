module RPNCalculator

import Data.Strings
import Data.List
import System
import System.File

import StackLang


interface EntryMappable a where
mapToMaybeEntry : String -> IO (Maybe (Entry Nat))


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
mapToMaybeEntry x = if x == "+" then pure $ Just $ Func (+)
              else if x == "*" then pure $ Just $ Func (*)
              else if x == "r" then pure $ Just $ Op runReadInput
              else if x == "p" then pure $ Just $ Op ?rhs_p
              else case parsePositive x of
                        Nothing => pure Nothing -- TODO: This should throw
                        Just n  => pure $ Just $ Elem n


filterNothing : List (IO (Maybe a)) -> IO (List a)
filterNothing []            = pure []
filterNothing (ioX :: ioXs) = do
    x <- ioX  
    case x of
        Nothing    => filterNothing ioXs
        Just entry => filterNothing ioXs >>= (\xs => pure $ entry :: xs)
                    


parseInput : (input : String) -> IO (Stack (Entry Nat))
parseInput input = do
    cmds <- filterNothing $ map mapToMaybeEntry (words input)
    pure $ stackFromList $ reverse cmds


public export
eval : (input : String) -> IO (Maybe Nat) 
eval input = do
    res <- runIO (parseInput input) 
    case res of
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


