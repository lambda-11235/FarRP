
module FarRP.Time

import Control.IOExcept
import Effects
import System


%include C "idris_farrp_time.h"

%access export
%default total


||| A time delta in seconds.
public export
data DTime = MkDTime Double

dtimeToDouble : DTime -> Double
dtimeToDouble (MkDTime x) = x

public export
Num DTime where
  (+) (MkDTime x) (MkDTime y) = MkDTime (x + y)
  (*) (MkDTime x) (MkDTime y) = MkDTime (x * y)
  fromInteger n = MkDTime (fromInteger n)

public export
Neg DTime where
  negate (MkDTime x) = MkDTime (negate x)
  (-) (MkDTime x) (MkDTime y) = MkDTime (x - y)

public export
Abs DTime where
  abs (MkDTime x) =  MkDTime (abs x)

getTime' : IO Double
getTime' = foreign FFI_C "getTime" (IO Double)


public export
data Time : Effect where
  GetTime : sig Time Double

public export
Handler Time IO where
    handle () GetTime k = do t <- getTime'; k t ()

public export
Handler Time (IOExcept a) where
    handle () GetTime k = do t <- ioe_lift getTime'; k t ()

public export
TIME : EFFECT
TIME = MkEff () Time

||| Get the time in seconds since the Epoch.
getTime : Eff Double [TIME]
getTime = call $ GetTime


||| Produces time deltas in an IO context.
data DiffTimer : Type where
  MkDiffTimer : Double -> DiffTimer

newDiffTimer' : IO DiffTimer
newDiffTimer' = map MkDiffTimer getTime'

newDiffTimer : Eff DiffTimer [TIME]
newDiffTimer = do t <- getTime
                  pure $ MkDiffTimer t

stepDiffTimer' : DiffTimer -> IO (DTime, DiffTimer)
stepDiffTimer' (MkDiffTimer oldtime) = do newtime <- getTime'
                                          let dt = newtime - oldtime
                                          pure (MkDTime dt, MkDiffTimer newtime)

stepDiffTimer : DiffTimer -> Eff (DTime, DiffTimer) [TIME]
stepDiffTimer (MkDiffTimer oldtime) = do newtime <- getTime
                                         let dt = newtime - oldtime
                                         pure (MkDTime dt, MkDiffTimer newtime)
