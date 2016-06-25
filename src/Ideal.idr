
module Ideal


public export
DTime : Type
DTime = Double


||| This would've been the ideal form of SF. Unfortunately id, (.), arrow, and
||| first can't be made total with it. I keep it here for reference.
data SF : Type -> Type -> Type where
  ||| An SF is a computation that updates with time.
  MkSF : (DTime -> a -> (SF a b, b)) -> SF a b
