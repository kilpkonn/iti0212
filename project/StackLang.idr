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
  Op   : (IO (Stack (Entry a)) -> IO (Stack (Entry a))) -> Entry a
  Err  : Entry a


public export
stackFromList : List a -> Stack a
stackFromList []        = Empty
stackFromList (x :: xs) = x :: stackFromList xs

{-
public export
run : Stack (Entry a) -> Maybe (Stack (Entry a))
run Empty = Just Empty
run ((Elem x) :: (Elem y) :: (Func f)) = ?rhs
run ((Elem x) :: stack) = Just $ (Elem x) :: stack
run ((Func f) :: ((Func g) :: (next :: stack))) = 
    case run ((Func g) :: next :: stack) of
         Nothing => Nothing
         Just stack => run $ (Func f) :: stack

run ((Func f) :: ((Elem x) :: ((Func g) :: stack))) =
    case run ((Func g) :: stack) of
         Nothing => Nothing
         Just stack =>  run $ (Func f) :: (Elem x) :: stack

run ((Func f) :: ((Elem x) :: ((Elem y) :: stack))) = 
    run $ (Elem (f x y)) :: stack
run _ = Nothing
-}

reverse : Stack a -> Stack a
reverse xs = reverseOnto xs Empty where
  reverseOnto : Stack a -> Stack a -> Stack a
  reverseOnto xs Empty     = xs
  reverseOnto xs (y :: ys) = reverseOnto (y :: xs) ys

merge : Stack (Entry a) -> Stack (Entry a) -> Stack (Entry a)
merge Empty     ys = ys
merge (x :: xs) ys = merge xs (x :: ys)


public export
runIO : IO (Stack (Entry a)) -> IO (Maybe (Stack (Entry a)))
runIO x = do
  stack <- x
  case stack of
       ((Op o) :: rest)    => do
            newFront <- o (pure Empty)
            runIO $ pure $ merge (reverse newFront) rest
       ((Elem x) :: (Op o) :: rest) => do
            putStr "a"
            newFront <- o (pure ((Elem x) :: Empty))
            runIO $ pure $ merge (reverse newFront) rest
       ((Elem x) :: (Elem y) :: (Op o) :: rest) => do
            putStr "b"
            newFront <- o (pure ((Elem y) :: ((Elem x) :: Empty)))
            runIO $ pure $ merge (reverse newFront) rest
       ((Elem x) :: (Elem y) :: (Func f) :: rest) => do
            putStr "c"
            runIO $ pure $ (Elem (f x y)) :: rest
       (x :: y :: z :: rest) => do
            putStr "d"
            newRestMaybe <- runIO $ pure $ (y :: (z :: rest))
            case newRestMaybe of
                 Nothing      => pure Nothing
                 Just newRest => runIO $ pure $ x :: newRest
       (Elem x) :: Empty => pure $ Just ((Elem x) :: Empty)
       _ => pure Nothing
