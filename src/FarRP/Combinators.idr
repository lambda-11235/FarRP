
module FarRP.Combinators

import FarRP.Core
import FarRP.DecDesc
import FarRP.SigVect
import FarRP.Time


%access export
%default total


-- Basic Combinators

pure : (a -> b) -> SF [C i a] [C i b] Cau
pure {i} f = SFPrim (pure' i) ()
  where
    pure' Ini dt () (CCons x xs) = ((), CCons (f x) xs)
    pure' Uni dt () (CCons x xs) = ((), CCons (f x) xs)
    pure' Uni dt () (UnInitCons xs) = ((), UnInitCons xs)

pureE : (a -> b) -> SF [E a] [E b] Cau
pureE f = SFPrim pureE' ()
  where
    pureE' dt () (ECons x xs) = ((), ECons (map f x) xs)

constant : b -> SF as [C Ini b] Dec
constant x = SFDPrim (\_, _ => (const (), CCons x SVRNil)) ()

join : (a -> b -> c) -> SF (C Ini a :: C Ini b :: as) (C Ini c :: as) Cau
join f = SFPrim join' ()
  where
    join' _ _ (CCons x (CCons y xs)) = ((), CCons (f x y) xs)

||| Merges two event streams, using the given function to combine values that
||| occur at the same time.
merge : (a -> a -> a) -> SF (E a :: E a :: xs) (E a :: xs) Cau
merge {a} f = SFPrim merge' ()
  where
    merge'' : Maybe a -> Maybe a -> Maybe a
    merge'' Nothing Nothing = Nothing
    merge'' (Just x) Nothing = Just x
    merge'' Nothing (Just y) = Just y
    merge'' (Just x) (Just y) = Just (f x y)

    merge' _ _ (ECons x (ECons y xs)) = ((), ECons (merge'' x y) xs)


-- Combinator Operators

infixl 9 >>>
(>>>) : SF as bs d1 -> SF bs cs d2 -> SF as cs (d1 /\ d2)
(>>>) = SFComp

infixr 9 <<<
(<<<) : SF bs cs d2 -> SF as bs d1 -> SF as cs (d1 /\ d2)
(<<<) = flip SFComp

infixr 3 ***
(***) : SF as bs d1 -> SF cs ds d2 -> SF (as ++ cs) (bs ++ ds) (d1 \/ d2)
(***) = SFPair

infixr 3 &&&
(&&&) : SF as bs d1 -> SF as cs d2 -> SF as (bs ++ cs) (d1 \/ d2)
(&&&) sf1 sf2 = replace cauMeet (double >>> (sf1 *** sf2))
  where
    double : SF as (as ++ as) Cau
    double = SFPrim (\_, _, svr => ((), svr ++ svr)) ()


-- Event Combinators

||| Never produces a signal output.
never : SF as [E b] Dec
never = SFDPrim (\_, _ => (\_ => (), eEmpty)) ()

||| Produces a signal output now, but never again.
now : SF as [E Unit] Dec
now = SFDPrim now' True
  where
    now' _ True = (const False, eSingle ())
    now' _ False = (const False, eEmpty)

||| Produces an event whenever the input changes from False to True.
edge : SF [C Ini Bool] [E Unit] Cau
edge = SFPrim edge' False
  where
    edge' _ False (CCons True xs) = (True, ECons (Just ()) xs)
    edge' _ _ (CCons x xs) = (x, ECons Nothing xs)

hold : a -> SF [E a] [C Ini a] Cau
hold x = SFPrim hold' x
  where
    hold' _ _ (ECons (Just x') xs) = (x', CCons x' xs)
    hold' _ x' (ECons Nothing xs) = (x', CCons x' xs)

evFold : b -> (a -> b -> b) -> SF [E a] [E b] Cau
evFold x f = SFPrim evFold' x
  where
    evFold' _ x (ECons Nothing xs) = (x, ECons Nothing xs)
    evFold' _ x (ECons (Just x') xs) = let r = f x' x
                                       in (r, ECons (Just r) xs)


-- Pre Combinators

||| Delays a signal for the smallest possible time. Must be initialized.
pre : SF [C Ini a] [C Uni a] Dec
pre = SFDPrim pre' Nothing
  where
    pre' : DTime -> Maybe (SVRep [C Ini a])
         -> (SVRep [C Ini a] -> Maybe (SVRep [C Ini a]), SVRep [C Uni a])
    pre' _ Nothing = (Just, UnInitCons SVRNil)
    pre' _ (Just (CCons x xs)) = (Just, (CCons x xs))

||| Initializes an input signal with a starting value.
initialize' : b -> SF [C Uni b] [C Ini b] Cau
initialize' x = SFPrim init' ()
  where
    init' _ _ (CCons x' xs) = ((), CCons x' xs)
    init' _ _ (UnInitCons xs) = ((), CCons x xs)

||| Initializes an SF with a starting value.
initialize : b -> SF as [C i b] d -> SF as [C Ini b] d
initialize {i=Ini} x sf = sf
initialize {i=Uni} x sf = replace (trans meetSym cauMeet)
                                  (sf >>> initialize' x)


-- Integration and Differentiation Combinators

||| Integrates the input signal over time.
integrate : Double -> SF [C Ini Double] [C Ini Double] Cau
integrate c = SFPrim integ' c
  where
    integ' dt c (CCons x xs) = let r = x * (dtimeToDouble dt) + c
                               in (r, CCons r xs)

||| Differentiates the input signal with respect to time.
diff : SF [C Ini Double] [C Ini Double] Cau
diff = SFPrim diff' ()
  where
    diff' dt _ (CCons x xs) = ((), CCons (x * dtimeToDouble dt) xs)
