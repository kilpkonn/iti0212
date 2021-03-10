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
data Stack : Type -> Type where
    Empty : Stack a
    (::)  : (top : a) -> (stack : Stack a) -> Stack a


data StepResult : Type -> Type where
    Error    : StepResult a  -- Error has ocurred
    End      : StepResult a  -- Dont perform any operation, return
    Success  : a -> StepResult a  -- Perform operation and return
    Continue : a -> StepResult a  -- Done


data RunResult : Type -> Type where
    Completed  : a -> RunResult a
    Failed     : RunResult a


public export
data Entry : Type -> Type where
  Elem : a -> Entry a
  Func : (a -> a -> a) -> Entry a


exec : (f: (a -> a -> a)) -> (stack : Stack a) -> Stack a
exec f Empty                 = Empty
exec f (top :: Empty)        = top :: Empty
exec f (top :: (el :: stack)) = (f top el) :: stack


stackFromList : List a -> Stack a
stackFromList []        = Empty
stackFromList (x :: xs) = x :: stackFromList xs


{-
 - Run StackLang program.
 - @param f: (a -> a -> StepResult a) Function to run on two topmost elements.
 -           
 -}

--run : (f: (a -> a -> StepResult a)) -> (stack : Stack a) -> RunResult (Stack a)
--run f Empty                 = Failed
--run f (top :: Empty)        = Failed  -- TODO: Some other result or merge
--run f (top :: el :: stack) = case f top el of
--                                    Error    => Failed
--                                    End      => Completed (top :: (el :: stack))
--                                    Success  res => Completed (res :: stack)
--                                    Continue res => run f (res :: stack)

run : Stack (Entry a) -> Maybe (Stack (Entry a))
run Empty = Just Empty
run ((Elem x) :: stack) = Just $ (Elem x) :: stack
run ((Func f) :: Empty) = Nothing 
run ((Func f) :: (top :: Empty)) = Nothing
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

