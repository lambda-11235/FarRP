{-
This program simply computes the average of a set of given inputs.
-}

import FarRP
import FarRP.Time

import Data.String


sum' : SF [E Double] [E Double] Cau
sum' = evFold 0 (+)

count : SF [E Double] [E Double] Cau
count = evFold 0 (\_, acc => acc + 1)

average : SF [E Double] [E Double] Cau
average = (sum' &&& count) >>> merge (\x, y => x / y)

loop : SF [E Double] [E Double] Cau -> DiffTimer -> IO ()
loop sf diffTimer = do str <- getLine
                       case parseDouble str of
                         Nothing => putStrLn "Couldn't parse input"
                         Just x => do (dt, diffTimer') <- stepDiffTimer' diffTimer
                                      let (sf', avg) = stepSFE sf dt x
                                      case eHead avg of
                                        Nothing => return ()
                                        Just x => printLn x
                                      loop sf' diffTimer'

main : IO ()
main = do diffTimer <- newDiffTimer'
          loop average diffTimer
