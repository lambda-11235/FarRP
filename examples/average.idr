{-
This program simply computes the average of a set of given inputs.
-}

import FarRP
import FarRP.Time

import Control.Arrow
import Control.Category
import Data.String


sum' : SF Double Double
sum' = sfFold 0 (+)

count : SF Double Double
count = sfFold 0 (\_, acc => acc + 1)

average : SF Double Double
average = arrow (\p => fst p / snd p) . (sum' &&& count)

loop : SF Double Double -> DiffTimer -> IO ()
loop sf diffTimer = do str <- getLine
                       case parseDouble str of
                         Nothing => putStrLn "Couldn't parse input"
                         Just x => do (dt, diffTimer') <- stepDiffTimer diffTimer
                                      let (sf', avg) = stepSF sf dt x
                                      printLn avg
                                      loop sf' diffTimer'

main : IO ()
main = do diffTimer <- newDiffTimer
          loop average diffTimer
