module StackLang

{-
 - Idris Lists are quite like Stacks on most C-like languages.
 - You can only access first element, and if you have taken that out
 - only then the next.
 - Althought this might be incorrect, as you technically can peek into list it
 - is similar enough to use Stack as 'type alias' for List.
 -
 - This is implemented sepparately so that we can restrict
 - how Stack can be accessed.
 -}



public export
data Stack : Type -> Type where
    Empty : Stack a 
    (::)  : (top : a) -> (stack : Stack a) -> Stack a 


public export
data Entry : Type -> Type where
  Elem : a -> Entry a
  Func : (a -> a -> a) -> Entry a
  Op   : ((state : List (Nat, (Entry a))) -> Stack (Entry a) ->
         IO (((List (Pair Nat (Entry a))), Stack (Entry a)))) -> Entry a
  Err  : Entry a
  Nil  : Entry a


implementation Show (Entry a) where
  show (Elem x) = "el"
  show (Func f) = "fn"
  show (Op   o) = "op"
  show Err      = "err"
  show Nil      = "nil"


implementation Show a => Show (Stack a) where
  show Empty        = "end"
  show (top :: stack) = (show top) ++ " :: " ++ (show stack)


public export
implementation Cast (List a) (Stack a) where
  cast []        = Empty
  cast (x :: xs) = x :: cast xs


reverse : Stack a -> Stack a
reverse xs = reverseOnto Empty xs where
  reverseOnto : Stack a -> Stack a -> Stack a
  reverseOnto xs Empty     = xs
  reverseOnto xs (y :: ys) = reverseOnto (y :: xs) ys


merge : Stack (Entry a) -> Stack (Entry a) -> Stack (Entry a)
merge Empty     ys = ys
merge (x :: xs) ys = merge xs (x :: ys)


runFunc : (a -> a -> a) -> Stack (Entry a) -> Stack (Entry a)
runFunc f ((Elem x) :: (Elem y) :: rest) = (Elem (f x y)) :: rest
runFunc f _ = Err :: Empty


--runOp : --(state : (List (Pair Nat (Entry a)))) -> 
--        (f : (Entry a) -> IO (List (Nat, (Entry a)), Stack (Entry a))) -> 
--        Stack (Entry a) -> IO (List (Nat, (Entry a)), Stack (Entry a))
--runOp f (top :: rest) = do
--                          (state, newStack) <- f top
--                          pure $ (state, merge (reverse newStack) rest)
--runOp f Empty = pure !(f Nil)


-- Forward declaration
runLeft : (state : List (Nat, (Entry a))) -> 
          IO (Stack (Entry a)) -> IO (Stack (Entry a)) -> IO (Maybe (Stack (Entry a)))

runRight : (state : List (Nat, (Entry a))) ->
          IO (Stack (Entry a)) -> IO (Stack (Entry a)) -> IO (Maybe (Stack (Entry a)))
runRight state ioStackLeft ioStackRight = do
  stackLeft <- ioStackLeft
  stackRight <- ioStackRight
  putStrLn "To right"
  putStrLn $ "State: " ++ (show state)
  putStrLn $ "left: " ++ (show stackLeft)
  putStrLn $ "right: " ++ (show stackRight)
  case stackRight of
       Empty => case stackLeft of
                     Empty  => pure Nothing
                     (Elem e) :: Empty => pure $ Just $ (Elem e) :: Empty
                     _ :: Empty => pure Nothing
                     _ => runLeft state ioStackLeft (pure Empty)
       (Elem e) :: rest => runRight state (pure ((Elem e) :: stackLeft)) (pure rest)
       (Func f) :: rest => runLeft state (pure (runFunc f stackLeft)) (pure rest)
       (Op   o) :: rest => do 
                             (s, left) <- o state stackLeft
                             runLeft s (pure left) (pure rest)
       Nil      :: rest => runRight state ioStackLeft (pure rest)
       Err      :: rest => pure Nothing

runLeft state ioStackLeft ioStackRight = do
  stackLeft <- ioStackLeft
  stackRight <- ioStackRight
  putStrLn "To left"
  putStrLn $ "State: " ++ (show state)
  putStrLn $ "left: " ++ (show stackLeft)
  putStrLn $ "right: " ++ (show stackRight)
  case stackLeft of
       Empty => runRight state (pure Empty) ioStackRight
       (Elem e) :: rest => runLeft state (pure rest) (pure ((Elem e) :: stackRight))
       (Func f) :: rest => runLeft state (pure (runFunc f rest)) ioStackRight
       (Op   o) :: rest => do
                             (s, left) <- o state stackLeft
                             runLeft s (pure left) ioStackRight
       Nil     :: rest  => runLeft state (pure rest) ioStackRight
       Err     :: rest  => pure Nothing


public export
run : IO (Stack (Entry a)) -> IO (Maybe (Stack (Entry a)))
run = runRight [] (pure Empty)
