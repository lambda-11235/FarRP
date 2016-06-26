
module FarRP.Time

import System


%access export
%default total


||| A time in seconds.
public export
data Time = MkTime Double

||| A time delta in seconds.
public export
DTime : Type
DTime = Time

timeToDouble : Time -> Double
timeToDouble (MkTime x) = x

Num Time where
  (+) (MkTime x) (MkTime y) = MkTime (x + y)
  (*) (MkTime x) (MkTime y) = MkTime (x * y)
  fromInteger n = MkTime (fromInteger n)

Neg Time where
  negate (MkTime x) = MkTime (negate x)
  (-) (MkTime x) (MkTime y) = MkTime (x - y)
  abs (MkTime x) = MkTime (abs x)


getTime : IO Time
getTime = map (MkTime . fromInteger) time


data DiffTimer : Type where
  MkDiffTimer : Time -> DiffTimer

newDiffTimer : IO DiffTimer
newDiffTimer = map MkDiffTimer getTime

stepDiffTimer : DiffTimer -> IO (DTime, DiffTimer)
stepDiffTimer (MkDiffTimer oldtime) = do newtime <- getTime
                                         let dt = newtime - oldtime
                                         return (dt, MkDiffTimer newtime)
