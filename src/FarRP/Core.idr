
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


postulate subtypeWeaken : SF as bs Dec -> SF as bs Cau

joinWeaken : SF as bs d -> SF as bs (d' \/ d)
joinWeaken {d} {d'} sf = joinWeaken' d' d sf
  where
    joinWeaken' Dec Dec sf = sf
    joinWeaken' Dec Cau sf = sf
    joinWeaken' Cau Dec sf = subtypeWeaken sf
    joinWeaken' Cau Cau sf = sf


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


pure : (a -> b) -> SF [C i a] [C i b] Cau
pure {i} f = SFPrim (func i) ()
  where
    func Ini dt () (CCons x xs) = ((), CCons (f x) xs)
    func Uni dt () (CCons x xs) = ((), CCons (f x) xs)
    func Uni dt () (UnInitCons xs) = ((), UnInitCons xs)

constant : b -> SF as [C Ini b] Dec
constant x = SFDPrim (\_, _ => (const (), CCons x SVRNil)) ()

infixl 9 >>>
(>>>) : SF as bs d1 -> SF bs cs d2 -> SF as cs (d1 /\ d2)
(>>>) = SFComp

infixr 3 ***
(***) : SF as bs d1 -> SF cs ds d2 -> SF (as ++ cs) (bs ++ ds) (d1 \/ d2)
(***) = SFPair

infixr 3 &&&
(&&&) : SF as bs d1 -> SF as cs d2 -> SF as (bs ++ cs) (d1 \/ d2)
(&&&) sf1 sf2 = replace cauMeet (double >>> (sf1 *** sf2))
  where
    double : SF as (as ++ as) Cau
    double = SFPrim (\_, _, svr => ((), svr ++ svr)) ()


edge : SF [C Ini Bool] [E Unit] Cau
edge = SFPrim edge' ()
  where
    edge' _ _ (CCons True xs) = ((), ECons (Just ()) xs)
    edge' _ _ _ = ((), ECons Nothing SVRNil)

hold : a -> SF [E a] [C Ini a] Cau
hold x = SFPrim hold' x
  where
    hold' _ _ (ECons (Just x') xs) = (x', CCons x' xs)
    hold' _ x' (ECons Nothing xs) = (x', CCons x' xs)

pre : SF [C Ini a] [C Uni a] Dec
pre = SFDPrim pre' Nothing
  where
    pre' : DTime -> Maybe (SVRep [C Ini a])
         -> (SVRep [C Ini a] -> Maybe (SVRep [C Ini a]), SVRep [C Uni a])
    pre' _ Nothing = (Just, UnInitCons SVRNil)
    pre' _ (Just (CCons x xs)) = (Just, (CCons x xs))

initialize : b -> SF [C Uni b] [C Ini b] Cau
initialize x = SFPrim init' ()
  where
    init' _ _ (CCons x' xs) = ((), CCons x' xs)
    init' _ _ (UnInitCons xs) = ((), CCons x xs)
