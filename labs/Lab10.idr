module Lab10

import Data.Vect


indPair : Pair a b -> DPair a (\_ => b)
indPair (x, y) = (x ** y)


DisjointUnion : Type -> Type -> Type
DisjointUnion a b = DPair Bool (\i => if i then b else a)


fromDU : (f : a -> c) -> (g : b -> c) -> DisjointUnion a b -> c
fromDU f g (MkDPair True  snd) = g snd
fromDU f g (MkDPair False snd) = f snd 


fromEither : Either a b -> DisjointUnion a b
fromEither (Left x) = (False ** x)
fromEither (Right x) = (True ** x)


toEither : DisjointUnion a b -> Either a b
toEither x = fromDU Left Right x


record DUrec a b where
  constructor MkDUrec
  index : Bool
  value : if index then b else a


fromDUrec : DUrec a b -> DisjointUnion a b
fromDUrec (MkDUrec True value) = (True ** value)  -- Why does it need casesplit?
fromDUrec (MkDUrec False value) = (False ** value)


toDUrec : DisjointUnion a b -> DUrec a b
toDUrec (MkDPair True snd) = MkDUrec True snd
toDUrec (MkDPair False snd) = MkDUrec False snd


arySum : (n : Nat) -> Vect n Type -> Type
arySum n xs = (n ** index n xs)


data HVect : Vect n Type -> Type where
  Nil : HVect []
  (::) : t -> HVect ts -> HVect (t :: ts)


head : (v : HVect n) -> head n
head (x :: y) = x


tail : (v : HVect n) -> HVect (tail n)
tail (x :: y) = y


(++) : (a : HVect n) -> (b : HVect m) -> HVect (n ++ m)
(++) [] b = b
(++) (x :: y) b = x :: y ++ b


index' : (n : Fin len) -> (v : HVect ts) -> index n ts
index' FZ (x :: y) = x 
index' (FS m) (x :: y) = index' m y 
