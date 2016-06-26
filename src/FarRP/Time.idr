
module FarRP.Time

import System


%access export
%default total


public export
Time : Type
Time = Double

-- TODO: Make a seperate data type from double.
||| A difference in time.
public export
DTime : Type
DTime = Double


getTime : IO Time
getTime = map fromInteger time


data DiffTimer : Type where
  MkDiffTimer : Time -> DiffTimer

newDiffTimer : IO DiffTimer
newDiffTimer = map MkDiffTimer getTime

stepDiffTimer : DiffTimer -> IO (DTime, DiffTimer)
stepDiffTimer (MkDiffTimer oldtime) = do newtime <- getTime
                                         let dt = newtime - oldtime
                                         return (dt, MkDiffTimer newtime)
