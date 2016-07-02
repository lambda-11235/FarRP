
module FarRP.Core

import FarRP.DecDesc
import FarRP.SigVect
import FarRP.Time


%access export
%default total


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
stepSF (SFLoop sf1 sf2) dt xs = ?loop
-- TODO: Get rid of believe_mes
stepSF (SFSwitch sf f) dt xs = let r1 = stepSF sf dt xs
                               in
                                 case snd r1 of
                                   ECons Nothing svr => (SFSwitch (fst r1) f, svr)
                                   ECons (Just e) svr =>
                                     let r2 = stepSF (f e) dt xs
                                     in believe_me (fst r2, svr)
stepSF (SFDSwitch sf f) dt xs = let r = stepSF sf dt xs
                                in
                                  case snd r of
                                    ECons Nothing svr => (SFSwitch (fst r) f, svr)
                                    ECons (Just e) svr => believe_me (stepSF (f e) dt xs)


pure : (a -> b) -> SF [C i a] [C i b] Cau
pure {i} f = SFPrim (func i) ()
  where
    func Ini dt () (CCons x xs) = ((), CCons (f x) xs)
    func Uni dt () (UnInitCons xs) = ((), UnInitCons xs)
