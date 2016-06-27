
module FarRP.Ideal

import FarRP.Time


||| This would've been the ideal form of SF. Unfortunately id, (.), arrow, and
||| first can't be made total in this form, so it can not implement the Arrow or
||| Category interfaces. I keep it here for reference.
public export
data SF : Type -> Type -> Type where
  ||| An SF is a computation that updates with time.
  MkSF : (DTime -> a -> (SF a b, b)) -> SF a b

stepSF : SF a b -> DTime -> a -> (SF a b, b)
stepSF (MkSF f) = f


id : SF a a
id = MkSF $ \_, x => (id, x)

infixl 9 .
(.) : SF b c -> SF a b -> SF a c
(.) (MkSF f) (MkSF g) = MkSF $ \dt, x =>
  case g dt x of
    (sf1, y) => case f dt y of
                  (sf2, z) => (sf2 . sf1, z)

arrow : (a -> b) -> SF a b
arrow f = MkSF $ \_, x => (arrow f, f x)

first : SF a b -> SF (a, c) (b, c)
first (MkSF f) = MkSF $ \dt, p =>
  case f dt (fst p) of
    (sf, x) => (first sf, (x, snd p))

second : SF a b -> SF (c, a) (c, b)
second sf = (arrow flipPair) . (first sf) . (arrow flipPair)
  where
    flipPair : (e, f) -> (f, e)
    flipPair (x, y) = (y, x)


sfFold : b -> (a -> b -> b) -> SF a b
sfFold x f = MkSF $ \dt, acc => let res = f acc x in
                                  (sfFold res f, res)

switch : SF a (b, Maybe c) -> (c -> SF a b) -> SF a b
switch (MkSF f) g = MkSF $ \dt, x =>
  case f dt x of
    (sf, (y, Nothing)) => (switch sf g, y)
    (_, (_, Just z)) => stepSF (g z) dt x
