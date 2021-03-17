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
createSimpleFn : (a -> a -> a) -> Stack (IO (Entry a)) -> Stack (IO (Entry a))
createSimpleFn f Empty = Empty
createSimpleFn f (top :: next :: stack) = do 
  topElem <- top
  nextElem <- next
  case (topElem, nextElem) of
       (Elem x, Elem y) => ?rhs
       (Func f1, _) => f1 (next :: stack)
       (_, _) => ?rhs2
       -}


public export
run : Stack (Entry a) -> Maybe (Stack (Entry a))
run Empty = Just Empty
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


public export
runIO : IO (Stack (Entry a)) -> IO (Maybe (Stack (Entry a)))
runIO x = do
  stack <- x
  case stack of
       ((Op o) :: rest) => runIO $ o (pure rest)
       _ => pure $ run stack


