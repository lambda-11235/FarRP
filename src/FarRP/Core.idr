
module FarRP.Core

import Control.Arrow
import Control.Category

import FarRP.Time


%access export
%default total


||| SF can be thought of as a function from one time varying value to another.
||| That is, `SF a b = (a -> Time) -> (b -> Time)`
public export
data SF : Type -> Type -> Type where
  SFFun : (DTime -> a -> b) -> SF a b
  SFFold : b -> (DTime -> a -> b -> b) -> SF a b
  SFSwitch : SF a (b, Maybe c) -> (c -> SF a b) -> SF a b
  SFFst : SF a b -> SF (a, c) (b, c)
  SFComp : SF a b -> SF b c -> SF a c

||| Steps an SF through one computation, given a time delta and an input.
||| An updated SF value and the computation output are then returned.
stepSF : SF a b -> DTime -> a -> (SF a b, b)
stepSF sf@(SFFun f) dt x = (sf, f dt x)
stepSF (SFFold acc f) dt x = let res = f dt x acc in
                               (SFFold res f, res)
stepSF (SFSwitch sf f) dt x = let (sf', (res, ms)) = stepSF sf dt x in
  case ms of
    Nothing => (SFSwitch sf' f, res)
    (Just y) => let (sf'', res') = stepSF (f y) dt x in (sf'', res')
stepSF (SFFst sf) dt x = let (sf', res) = stepSF sf dt (fst x) in
                           (SFFst sf', (res, snd x))
stepSF (SFComp sf1 sf2) dt x = let (sf1', res1) = stepSF sf1 dt x
                                   (sf2', res2) = stepSF sf2 dt res1
                               in (SFComp sf1' sf2', res2)


Category SF where
  id = SFFun (\_, x => x)

  (.) (SFFun f) (SFFun g) = SFFun (\dt => (f dt . g dt))
  (.) sf1 sf2 = SFComp sf2 sf1

Arrow SF where
  arrow f = SFFun (\_ => f)

  first (SFFun f) = SFFun (\dt, p => (f dt (fst p), snd p))
  first sf = SFFst sf


sfFold : b -> (a -> b -> b) -> SF a b
sfFold x f = SFFold x (\_ => f)

switch : SF a (b, Maybe c) -> (c -> SF a b) -> SF a b
switch = SFSwitch


||| Integrate an SF's input.
||| `c` The interation constant.
integrate : Double -> SF Double Double
integrate c = SFFold c $ \dt, x, acc => x * (dtimeToDouble dt) + acc

differentiate : SF Double Double
differentiate = SFFun (\dt, x => x * (dtimeToDouble dt))

time : SF () Double
time = (integrate 0) . arrow (const 1)
