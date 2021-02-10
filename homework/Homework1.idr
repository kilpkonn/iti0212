{-
  Tavo Annus
  186060IAIB
  Idris 2, version 0.3.0-3bbf52025
-}

-- Problem 1
ack : Nat -> Nat -> Nat
ack 0     n     = n + 1
ack (S m) 0     = ack m 1
ack (S m) (S n) = ack m (ack (S m) n)


-- Problem 2
-- TODO: What should these functions actually do???
diag : a -> Pair a a
diag a = (a, a)

anyway : Either a a -> a
anyway (Left a)  = a
anyway (Right a) = a

assocr : Pair (Pair a b) c -> Pair a (Pair b c)
assocr ((a, b), c) = (a, (b, c))

distl : Pair a (Either b c) -> Either (Pair a b) (Pair a c)
distl (a, (Left b))  = Left (a, b)
distl (a, (Right c)) = Right (a, c)

-- Problem 3
consolidate : List (Maybe a) -> Maybe (List a)
consolidate []               = Just []
consolidate (x :: xs) = consAdd x (consolidate xs) where
  consAdd : Maybe a -> Maybe (List a) -> Maybe (List a)
  consAdd Nothing  x         = Nothing
  consAdd x        Nothing   = Nothing
  consAdd (Just x) (Just xs) = Just (x :: xs)

