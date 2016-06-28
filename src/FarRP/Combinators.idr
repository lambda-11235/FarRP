
module FarRP.Combinators

import Control.Arrow
import Control.Category

import FarRP.Core
import FarRP.Time


%access export
%default total


sfFold : b -> (a -> b -> b) -> SF a b
sfFold x f = SFFold x (\_ => f)

switch : SF a (b, Maybe c) -> (c -> SF a b) -> SF a b
switch = SFSwitch


||| Integrate an SF's output with respect to time.
||| The input value is the integration constant.
integrate : Double -> SF Double Double
integrate c = SFFold c $ \dt, x, acc => x * (dtimeToDouble dt) + acc

||| Differentiate an SF's output with respect to time.
differentiate : SF Double Double
differentiate = SFFun (\dt, x => x * (dtimeToDouble dt))

||| Returns the time in seconds since this wire started receiving input.
time : SF () Double
time = (integrate 0) . arrow (const 1)
