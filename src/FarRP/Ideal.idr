
module FarRP.Ideal

import FarRP.Time


||| This would've been the ideal form of SF. Unfortunately id, (.), arrow, and
||| first can't be made total with it. I keep it here for reference.
public export
data SF : Type -> Type -> Type where
  ||| An SF is a computation that updates with time.
  MkSF : (DTime -> a -> (SF a b, b)) -> SF a b
