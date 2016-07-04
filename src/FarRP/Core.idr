
module FarRP.Core

import FarRP.DecDesc
import FarRP.SigVect
import FarRP.Time


%access export
%default total


||| A state function, which can be abstractly thought of as `(Time -> SVRep as)
||| -> (Time -> SVRep bs)`.
public export
data SF : SVDesc -> SVDesc -> DecDesc -> Type where
  SFPrim : {State : Type} -> (DTime -> State -> SVRep as -> (State, SVRep bs))
         -> State -> SF as bs Cau

  SFDPrim : {State : Type} -> (DTime -> State -> (SVRep as -> State, SVRep bs))
         -> State -> SF as bs Dec

  SFComp : SF as bs d1 -> SF bs cs d2 -> SF as cs (d1 /\ d2)

  SFPair : SF as bs d1 -> SF cs ds d2 -> SF (as ++ cs) (bs ++ ds) (d1 \/ d2)

  SFLoop : SF (as ++ cs) (bs ++ ds) d -> SF ds cs Dec -> SF as bs d

  SFSwitch : SF as (E e :: bs) d1 -> (e -> SF as bs d2) -> SF as bs (d1 \/ d2)

  SFDSwitch : SF as (E e :: bs) d1 -> (e -> SF as bs d2) -> SF as bs (d1 \/ d2)


-- TODO: Prove this without believe_me.
||| A postulate that Dec is a subtype of Cau when considering a SF.
subtypeWeaken : SF as bs Dec -> SF as bs Cau
subtypeWeaken x = believe_me x

joinWeaken : SF as bs d -> SF as bs (d' \/ d)
joinWeaken {d} {d'} sf = joinWeaken' d' d sf
  where
    joinWeaken' Dec Dec sf = sf
    joinWeaken' Dec Cau sf = sf
    joinWeaken' Cau Dec sf = subtypeWeaken sf
    joinWeaken' Cau Cau sf = sf


-- TODO: Split into smaller functions.
||| Steps a state function through one moment in time, given the change in time
||| since the last step and the input for the current time. Returns an updated
||| version of the state function and its output.
partial
stepSF : SF as bs d -> DTime -> SVRep as -> (SF as bs d, SVRep bs)
stepSF (SFPrim f st) dt xs = let r = f dt st xs in (SFPrim f (fst r), snd r)
stepSF (SFDPrim f st) dt xs = let r = f dt st in (SFDPrim f (fst r xs), snd r)
stepSF (SFComp sf1 sf2) dt xs = let r1 = stepSF sf1 dt xs
                                    r2 = stepSF sf2 dt (snd r1)
                                in (SFComp (fst r1) (fst r2), snd r2)
stepSF (SFPair sf1 sf2) dt xs = let pxs = split xs
                                    r1 = stepSF sf1 dt (fst pxs)
                                    r2 = stepSF sf2 dt (snd pxs)
                                in (SFPair (fst r1) (fst r2), (snd r1) ++ (snd r2))
stepSF (SFLoop {as} {bs} {cs} {ds} {d} sf1 sf2) dt xs =
  (SFLoop (fst r1) (fst r2), fst $ split $ snd r1)
  where
    mutual
      partial
      r1 : (SF (as ++ cs) (bs ++ ds) d, SVRep (bs ++ ds))
      r1 = stepSF sf1 dt (xs ++ (snd r2))

      partial
      r2 : (SF ds cs Dec, SVRep cs)
      r2 = stepSF sf2 dt (snd $ split $ snd r1)
stepSF (SFSwitch sf f) dt xs = let r1 = stepSF sf dt xs
                               in
                                 case snd r1 of
                                   ECons Nothing svr => (SFSwitch (fst r1) f, svr)
                                   ECons (Just e) svr =>
                                     let r2 = stepSF (f e) dt xs
                                     in (joinWeaken (fst r2), svr)
stepSF (SFDSwitch sf f) dt xs = let r1 = stepSF sf dt xs
                                in
                                  case snd r1 of
                                    ECons Nothing svr => (SFSwitch (fst r1) f, svr)
                                    ECons (Just e) svr =>
                                      let r2 = (stepSF (f e) dt xs)
                                      in (joinWeaken (fst r2), snd r2)


||| Like stepSF, but with the input being an empty event signal.
partial
stepSFEE : SF [E a] bs d -> DTime -> (SF [E a] bs d, SVRep bs)
stepSFEE sf dt = stepSF sf dt eEmpty

||| Like stepSF, but with the input being an inhabited event signal.
partial
stepSFE : SF [E a] bs d -> DTime -> a -> (SF [E a] bs d, SVRep bs)
stepSFE sf dt x = stepSF sf dt (eSingle x)

||| Like stepSF, but with the input being part of a continuos signal.
partial
stepSFC : SF [C i a] bs d -> DTime -> a -> (SF [C i a] bs d, SVRep bs)
stepSFC sf dt x = stepSF sf dt (cSingle x)
