
module FarRP.Event

import Control.Arrow
import Control.Category

import FarRP.Core
import FarRP.Combinators
import FarRP.Time


%access export
%default total


||| Events are maybe values, which produce nothing or just something.
public export
Event : Type -> Type
Event = Maybe


||| A version of arrow that automatically raises the given function to the event
||| level.
arrEvent : (a -> b) -> SF (Event a) (Event b)
arrEvent = arrow . map

||| Folds across events to produce a value.
eventFold : b -> (a -> b -> b) -> SF (Event a) b
eventFold init f = sfFold init (\x, acc => case x of
                                             Just x' => f x' acc
                                             Nothing => acc)

||| Applies a function held in an event to the SF's value everytime the event
||| occurs, accumulating a new value.
accum : a -> SF (Event (a -> a)) a
accum x = eventFold x apply

||| Hold on to the last value produced by an event.
hold : a -> SF (Event a) a
hold x = eventFold x const

||| Merge two events, using a combining function if they occure at the same
||| time.
merge : (a -> a -> a) -> Event a -> Event a -> Event a
merge _ Nothing ev = ev
merge _ ev Nothing = ev
merge f (Just x) (Just y) = Just (f x y)

||| Merge raised to an SF.
merge' : (a -> a -> a) -> SF (Event a, Event a) (Event a)
merge' f = arrow (\evp => merge f (fst evp) (snd evp))
