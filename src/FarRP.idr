{-# LANGUAGE Arrows #-}

module FarRP

import Control.Arrow
import Control.Category


%access export
%default total


Time : Type
Time = Double

DTime : Type
DTime = Double


data SF : Type -> Type -> Type where
  -- The three cases SFId, SFPure, and SFTime can all be represented by SFTime.
  -- Should they be condensed?
  SFId : SF a a
  SFPure : (a -> b) -> SF a b
  SFTime : (DTime -> a -> b) -> SF a b
  SFFold : b -> (DTime -> a -> b -> b) -> SF a b
  SFFst : SF a b -> SF (a, c) (b, c)
  SFComp : SF a b -> SF b c -> SF a c

stepSF : SF a b -> DTime -> a -> (SF a b, b)
stepSF SFId _ x = (SFId, x)
stepSF sf@(SFPure f) _ x = (sf, f x)
stepSF sf@(SFTime f) dt x = (sf, f dt x)
stepSF (SFFold acc f) dt x = let res = f dt x acc in
                               (SFFold res f, res)
stepSF (SFFst sf) dt x = let (sf', res) = stepSF sf dt (fst x) in
                           (SFFst sf', (res, snd x))
stepSF (SFComp sf1 sf2) dt x = let (sf1', res1) = stepSF sf1 dt x
                                   (sf2', res2) = stepSF sf2 dt res1
                               in (SFComp sf1' sf2', res2)


Category SF where
  id = SFId

  (.) SFId sf = sf
  (.) sf SFId = sf
  (.) (SFPure f) (SFPure g) = SFPure (f . g)
  (.) sf1 sf2 = SFComp sf2 sf1

Arrow SF where
  arrow = SFPure

  first SFId = SFId
  first (SFPure f) = SFPure (\p => (f (fst p), snd p))
  first sf = SFFst sf


sfFold : b -> (a -> b -> b) -> SF a b
sfFold x f = SFFold x (\_ => f)

-- TODO: Add special switch case
-- switch : SF a (b, Maybe c) -> (c -> SF a b) -> SF a b
-- switch sf f = ?impl


integrate : Double -> SF Double Double
integrate c = SFFold c $ \dt, x, acc => x * dt + acc

differentiate : SF Double Double
differentiate = SFTime (\dt, x => x*dt)

time : SF () Time
time = (integrate 0) . arrow (const 1)
