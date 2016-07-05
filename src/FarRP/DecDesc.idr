
module FarRP.DecDesc

import FarRP.Time


%access public export
%default total


||| A decoupledness descriptor for SFs.
data DecDesc : Type where
  ||| A decoupled SF descriptor, which is a subtype of casual SF.
  Dec : DecDesc
  ||| A casual SF descriptor.
  Cau : DecDesc

infixr 5 \/
||| The join (as in subtyping) of two decoupledness descriptors.
(\/) : DecDesc -> DecDesc -> DecDesc
(\/) Dec Dec = Dec
(\/) _ _ = Cau

infixr 5 /\
||| The meet (as in subtyping) of two decoupledness descriptors.
(/\) : DecDesc -> DecDesc -> DecDesc
(/\) Cau Cau = Cau
(/\) _ _ = Dec

joinSym : {d1 : DecDesc} -> {d2 : DecDesc}
  -> d1 \/ d2 = d2 \/ d1
joinSym {d1 = Dec} {d2 = Dec} = Refl
joinSym {d1 = Dec} {d2 = Cau} = Refl
joinSym {d1 = Cau} {d2 = Dec} = Refl
joinSym {d1 = Cau} {d2 = Cau} = Refl

meetSym : {d1 : DecDesc} -> {d2 : DecDesc}
  -> d1 /\ d2 = d2 /\ d1
meetSym {d1 = Dec} {d2 = Dec} = Refl
meetSym {d1 = Dec} {d2 = Cau} = Refl
meetSym {d1 = Cau} {d2 = Dec} = Refl
meetSym {d1 = Cau} {d2 = Cau} = Refl

decJoin : {d : DecDesc} -> Dec \/ d = d
decJoin {d = Dec} = Refl
decJoin {d = Cau} = Refl

cauMeet : {d : DecDesc} -> Cau /\ d = d
cauMeet {d = Dec} = Refl
cauMeet {d = Cau} = Refl
