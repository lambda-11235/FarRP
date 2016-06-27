{-
This program simply integrates over a set of given inputs with respect to time.
-}

import FarRP
import FarRP.Time

import Effects
import Effect.StdIO
import Control.Arrow
import Control.Category
import Data.String


loop : SF Double Double -> DiffTimer -> Eff () [STDIO, TIME]
loop sf diffTimer = do str <- getStr
                       case parseDouble str of
                         Nothing => putStrLn "Couldn't parse input"
                         Just x => do (dt, diffTimer') <- stepDiffTimer diffTimer
                                      let (sf', v) = stepSF sf dt x
                                      printLn v
                                      loop sf' diffTimer'

main' : Eff () [STDIO, TIME]
main' = do diffTimer <- newDiffTimer
           loop (integrate 0) diffTimer

main : IO ()
main = run $ main'
