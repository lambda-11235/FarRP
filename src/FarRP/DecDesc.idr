
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
joinSym {d1} {d2} = joinSym' d1 d2
  where
    joinSym' Dec Dec = Refl
    joinSym' Dec Cau = Refl
    joinSym' Cau Dec = Refl
    joinSym' Cau Cau = Refl

meetSym : {d1 : DecDesc} -> {d2 : DecDesc}
  -> d1 /\ d2 = d2 /\ d1
meetSym {d1} {d2} = meetSym' d1 d2
  where
    meetSym' Dec Dec = Refl
    meetSym' Dec Cau = Refl
    meetSym' Cau Dec = Refl
    meetSym' Cau Cau = Refl

decJoin : {d : DecDesc} -> Dec \/ d = d
decJoin {d} = decJoin' d
  where
    decJoin' Dec = Refl
    decJoin' Cau = Refl

cauMeet : {d : DecDesc} -> Cau /\ d = d
cauMeet {d} = cauMeet' d
  where
    cauMeet' Dec = Refl
    cauMeet' Cau = Refl
