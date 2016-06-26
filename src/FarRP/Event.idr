
module FarRP.Event

import Control.Arrow
import Control.Category

import FarRP.Core


%access export
%default total


||| Events are maybe values, which produce nothing or just something.
public export
Event : Type -> Type
Event = Maybe


hold : a -> SF (Event a) a
hold x = sfFold x (\ev, y => case ev of
                               Nothing => y
                               Just z => z)

||| Merge two events, using a combining function if they occure at the same
||| time.
merge : (a -> a -> a) -> Event a -> Event a -> Event a
merge _ Nothing ev = ev
merge _ ev Nothing = ev
merge f (Just x) (Just y) = Just (f x y)

||| Merge raised to an SF.
merge' : (a -> a -> a) -> SF (Event a, Event a) (Event a)
merge' f = arrow (\evp => merge f (fst evp) (snd evp))
