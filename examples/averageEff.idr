{-
This program simply computes the average of a set of given inputs.
This version uses the effects library.
-}

import FarRP
import FarRP.Time

import Effects
import Effect.StdIO
import Control.Arrow
import Control.Category
import Data.String


sum' : SF Double Double
sum' = sfFold 0 (+)

count : SF Double Double
count = sfFold 0 (\_, acc => acc + 1)

average : SF Double Double
average = arrow (\p => fst p / snd p) . (sum' &&& count)

loop : SF Double Double -> DiffTimer -> Eff () [STDIO, TIME]
loop sf diffTimer = do str <- getStr
                       case parseDouble str of
                         Nothing => putStrLn "Couldn't parse input"
                         Just x => do (dt, diffTimer') <- stepDiffTimer diffTimer
                                      let (sf', avg) = stepSF sf dt x
                                      printLn avg
                                      loop sf' diffTimer'

main' : Eff () [STDIO, TIME]
main' = do diffTimer <- newDiffTimer
           loop average diffTimer

main : IO ()
main = run $ main'
