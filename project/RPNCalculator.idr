module RPNCalculator

import Data.Strings
import Data.List
import System
import System.File

import StackLang


implementation Show (Entry Nat) where
  show (Elem x) = show x
  show (Func f) = "fn"
  show (Op f)   = "operation"
  show Err      = "err"
  show Nil      = "nil"

interface EntryMappable a where
mapToMaybeEntry : String -> IO (Maybe (Entry Nat))


runReadInput : (Entry Nat) ->  IO (Stack (Entry Nat))
runReadInput top = do
  putStr "Please Enter a Symbol: "
  input <- getLine
  maybeEntry <- mapToMaybeEntry input
  case maybeEntry of
       Nothing => pure $ Err :: Empty
       Just c  => pure $ c :: (top :: Empty)


runPop : (Entry Nat) -> IO (Stack (Entry Nat))
runPop (Elem e) = putStrLn ("Evaluation prints: " ++ (show e)) >>= (\_ => pure Empty)
runPop Nil      = putStrLn "Unable to print: Stack is empty" >>= (\_ => pure Empty)
runPop _        = putStrLn "No Result!" >>= (\_ => pure Empty)  -- Or should I print?


implementation EntryMappable String where
mapToMaybeEntry x = if x == "+" then pure $ Just $ Func (+)
              else if x == "*" then pure $ Just $ Func (*)
              else if x == "r" then pure $ Just $ Op runReadInput
              else if x == "p" then pure $ Just $ Op runPop
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
    putStrLn $ show $ words input
    putStrLn $ show cmds
    pure $ stackFromList cmds


public export
eval : (input : String) -> IO (Maybe Nat) 
eval input = do
    res <- run (parseInput input) 
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
                       Nothing => putStr $ "No Result!"
                       Just n  => putStr (show n) >>= (\_ => pure())
       _ => putStr "Please specify file name!"

