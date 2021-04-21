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
  Jump : (dir : Bool) -> (n : Nat) -> Entry a
  Err  : Entry a
  Nil  : Entry a


implementation Show (Entry a) where
  show (Elem x) = "el"
  show (Func f) = "fn"
  show (Op   o) = "op"
  show (Jump dir n) = "j(" ++ (show n) ++ ")"
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


duplicateAcc : (n : Nat) -> (m : Nat) -> (acc : Stack (Entry Nat)) -> 
            (stack : Stack (Entry Nat)) -> Stack (Entry Nat) 
duplicateAcc 0 0 acc stack = merge acc stack 
duplicateAcc (S n) 0 acc stack = duplicateAcc n 0 acc (merge acc stack)
duplicateAcc n (S m) acc (top :: stack) = duplicateAcc n m (top :: acc) stack
duplicateAcc n (S m) acc Empty = Err :: Empty 


public export
duplicate : (n : Nat) -> (m : Nat) -> (stack : Stack (Entry Nat)) -> Stack (Entry Nat)
duplicate n m stack = duplicateAcc n m Empty stack


runFunc : (a -> a -> a) -> Stack (Entry a) -> Stack (Entry a)
runFunc f ((Elem x) :: (Elem y) :: rest) = (Elem (f x y)) :: rest
runFunc f _ = Err :: Empty


moveLeft : (n : Nat) -> (left : Stack (Entry a)) -> (right : Stack (Entry a)) ->
            (Stack (Entry a), Stack (Entry a))
moveLeft 0 left right = (left, right)
moveLeft (S n) (top :: stack) right = moveLeft n stack (top :: right)
moveLeft (S n) Empty right = (Err :: Empty, right)


moveRight : (n : Nat) -> (left : Stack (Entry a)) -> (right : Stack (Entry a)) ->
            (Stack (Entry a), Stack (Entry a))
moveRight 0 left right = (left, right)
moveRight (S n) left (top :: stack) = (top :: left, stack)
moveRight (S n) left Empty = (Err :: left, Empty)


move : (dir : Bool) -> (n : Nat) -> (left : Stack (Entry a)) -> (right : Stack (Entry a)) ->
            (Stack (Entry a), Stack (Entry a))
move True n left right = moveRight n left right
move False n left right = moveLeft n left right


-- Forward declaration
runLeft : (state : List (Nat, (Entry a))) -> 
          IO (Stack (Entry a)) -> IO (Stack (Entry a)) -> IO (Maybe (Stack (Entry a)))

runRight : (state : List (Nat, (Entry a))) ->
          IO (Stack (Entry a)) -> IO (Stack (Entry a)) -> IO (Maybe (Stack (Entry a)))
runRight state ioStackLeft ioStackRight = do
  stackLeft <- ioStackLeft
  stackRight <- ioStackRight
  --putStrLn "To right"
  --putStrLn $ "State: " ++ (show state)
  --putStrLn $ "left: " ++ (show stackLeft)
  --putStrLn $ "right: " ++ (show stackRight)
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
       (Jump dir n) :: rest => let
                                 (left, right) = move dir n stackLeft stackRight
                               in
                                 runLeft state (pure left) (pure right)
       Nil      :: rest => runRight state ioStackLeft (pure rest)
       Err      :: rest => pure Nothing

runLeft state ioStackLeft ioStackRight = do
  stackLeft <- ioStackLeft
  stackRight <- ioStackRight
  --putStrLn "To left"
  --putStrLn $ "State: " ++ (show state)
  --putStrLn $ "left: " ++ (show stackLeft)
  --putStrLn $ "right: " ++ (show stackRight)
  case stackLeft of
       Empty => runRight state (pure Empty) ioStackRight
       (Elem e) :: rest => runLeft state (pure rest) (pure ((Elem e) :: stackRight))
       (Func f) :: rest => runLeft state (pure (runFunc f rest)) ioStackRight
       (Op   o) :: rest => do
                             (s, left) <- o state stackLeft
                             runLeft s (pure left) ioStackRight
       (Jump dir n) :: rest => let
                                 (left, right) = move dir n stackLeft stackRight
                               in
                                 runLeft state (pure left) (pure right)
       Nil     :: rest  => runLeft state (pure rest) ioStackRight
       Err     :: rest  => pure Nothing


public export
run : IO (Stack (Entry a)) -> IO (Maybe (Stack (Entry a)))
run = runRight [] (pure Empty)
