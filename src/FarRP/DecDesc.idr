
module FarRP.DecDesc

import FarRP.Time


%access public export
%default total


data DecDesc : Type where
  Dec : DecDesc
  Cau : DecDesc

infixr 5 \/
(\/) : DecDesc -> DecDesc -> DecDesc
(\/) Dec Dec = Dec
(\/) _ _ = Cau

infixr 5 /\
(/\) : DecDesc -> DecDesc -> DecDesc
(/\) Cau Cau = Cau
(/\) _ _ = Dec

decJoin : Dec \/ d = d
decJoin {d} = decJoin' d
  where
    decJoin' Dec = Refl
    decJoin' Cau = Refl

cauMeet : Cau /\ d = d
cauMeet {d} = cauMeet' d
  where
    cauMeet' Dec = Refl
    cauMeet' Cau = Refl
