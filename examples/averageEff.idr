{-
This program simply computes the average of a set of given inputs.
This version uses the effects library.
-}

import FarRP
import FarRP.Time

import Effects
import Effect.StdIO
import Data.String


sum' : SF [E Double] [E Double] Cau
sum' = evFold 0 (+)

count : SF [E Double] [E Double] Cau
count = evFold 0 (\_, acc => acc + 1)

average : SF [E Double] [E Double] Cau
average = (sum' &&& count) >>> merge (\x, y => x / y)

loop : SF [E Double] [E Double] Cau -> DiffTimer -> Eff () [STDIO, TIME]
loop sf diffTimer = do str <- getStr
                       case parseDouble str of
                         Nothing => putStrLn "Couldn't parse input"
                         Just x => do (dt, diffTimer') <- stepDiffTimer diffTimer
                                      let (sf', avg) = stepSFE sf dt x
                                      case eHead avg of
                                        Nothing => return ()
                                        Just x => printLn x
                                      loop sf' diffTimer'

main' : Eff () [STDIO, TIME]
main' = do diffTimer <- newDiffTimer
           loop average diffTimer

main : IO ()
main = run $ main'
