{-
This program simply integrates over a set of given inputs with respect to time.
-}

import FarRP
import FarRP.Time

import Effects
import Effect.StdIO
import Data.String


loop : SF [C Ini Double] [C Ini Double] Cau -> DiffTimer -> Eff () [STDIO, TIME]
loop sf diffTimer = do str <- getStr
                       case parseDouble str of
                         Nothing => putStrLn "Couldn't parse input"
                         Just x => do (dt, diffTimer') <- stepDiffTimer diffTimer
                                      let (sf', CCons v _) = stepSFC sf dt x
                                      printLn v
                                      loop sf' diffTimer'

main' : Eff () [STDIO, TIME]
main' = do diffTimer <- newDiffTimer
           loop (integrate 0) diffTimer

main : IO ()
main = run $ main'
