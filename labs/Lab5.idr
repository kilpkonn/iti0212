import Data.Strings
import System.File

parseNat : String -> Maybe Nat
parseNat = parsePositive

getNat : IO Nat
getNat = putStr "Please Enter a Nat: " >>= (\_ => 
         getLine >>= (\line => 
         case (parseNat line) of
              Nothing => pure 0
              Just n  => pure n
         ))

insistNat : IO Nat
insistNat = do
  putStr "Please Enter a Nat: "
  line <- getLine
  case (parseNat line) of
       Nothing => insistNat
       Just n  => pure n

insistAdd : Nat -> IO Nat
insistAdd n = do
  nat <- insistNat
  pure (nat + n)

addAfter : (IO Nat) -> Nat -> IO Nat
addAfter io n = do
  nat <- io
  pure (nat + n)

natsGet : IO (Maybe (List Nat))
natsGet = do
  line <- getLine
  pure (natsAcc (map parseNat (words line))) where
    natsAcc : List (Maybe Nat) -> Maybe (List Nat)
    natsAcc []              = Just []
    natsAcc (Nothing :: xs) = Nothing
    natsAcc (Just x :: xs)  = case (natsAcc xs) of
                                   Nothing => Nothing
                                   Just ys => Just (x :: ys)

tryNats : IO (List Nat)
tryNats = do
  line <- getLine
  pure (natsAcc (words line)) where
    natsAcc : List String -> List Nat
    natsAcc []        = []
    natsAcc (x :: xs) = case (parseNat x) of
                             Nothing => natsAcc xs
                             Just n  => n :: (natsAcc xs)

getLines : IO (List String)
getLines = do
  putStr "Enter Line: "
  line <- getLine
  if line == "done" then pure [] else getLines >>= (\lines => pure (line :: lines))

  
dictate : IO ()
dictate = do
  lines <- getLines
  putStr "Enter storage Location: "
  filename <- getLine
  if toLower filename == "none" 
     then putStrLn "Throwing Lines Away!"
     else do 
       res <- writeFile filename (unlines lines)
       case res of 
         Left err  => putStrLn "Error Saving File!"
         Right ()  => putStrLn "Success!"
                                                       
