
module FarRP.SigVect

import FarRP.Time


%access public export
%default total


||| A descriptor for the initialization state of a signal.
data Init : Type where
  ||| An initialized signal (ie. one that has a starting value).
  Ini : Init
  ||| An uninitialized signal (ie. one that needs a starting value).
  Uni : Init

||| A signal description.
data SigDesc : Type where
  ||| An event signal description, which contains the event output type.
  E : Type -> SigDesc
  ||| A continuous signal description, which contains the initialization state
  ||| and output type of the signal.
  C : Init -> Type -> SigDesc

SVDesc : Type
SVDesc = List SigDesc

data SVRep : SVDesc -> Type where
  SVRNil : SVRep []
  ECons : Maybe a -> SVRep as -> SVRep ((E a) :: as)
  CCons : a -> SVRep as -> SVRep ((C i a) :: as)
  UnInitCons : SVRep as -> SVRep ((C Uni a) :: as)

||| An empty event.
eEmpty : SVRep [E a]
eEmpty = ECons Nothing SVRNil

||| An event containing a value.
eSingle : a -> SVRep [E a]
eSingle x = ECons (Just x) SVRNil

cSingle : a -> SVRep [C i a]
cSingle x = CCons x SVRNil

eHead : SVRep (E a :: as) -> Maybe a
eHead (ECons x _) = x

cHead : SVRep (C i a :: as) -> Maybe a
cHead (CCons x _) = Just x
cHead (UnInitCons _) = Nothing

tail : SVRep (a :: as) -> SVRep as
tail (ECons _ xs) = xs
tail (CCons _ xs) = xs
tail (UnInitCons xs) = xs


||| Concatenates two signal vector representations together.
(++) : SVRep as -> SVRep bs -> SVRep (as ++ bs)
(++) {as = []} SVRNil svr2 = svr2
(++) {as} {bs = []} svr1 SVRNil = replace (sym $ appendNilRightNeutral as) svr1
(++) {as = (E a) :: as'} (ECons x xs) svr2 = ECons x (xs ++ svr2)
(++) {as = (C Ini a) :: as'} (CCons x xs) svr2 = CCons x (xs ++ svr2)
(++) {as = (C Uni a) :: as'} (CCons x xs) svr2 = CCons x (xs ++ svr2)
(++) {as = (C Uni a) :: as'} (UnInitCons xs) svr2 = UnInitCons (xs ++ svr2)


||| Splits a signal vector representation into two SVRs.
split : SVRep (as ++ bs) -> (SVRep as, SVRep bs)
split {as = []} {bs = []} svr = (SVRNil, SVRNil)
split {as = []} svr = (SVRNil, svr)
split {as} {bs = []} svr = (replace {P = SVRep} (appendNilRightNeutral as) svr, SVRNil)
split {as = (E a) :: as'} (ECons x xs) = let r = split xs
                                         in (ECons x (fst r), snd r)
split {as = (C Ini a) :: as'} (CCons x xs) = let r = split xs
                                             in (CCons x (fst r), snd r)
split {as = (C Uni a) :: as'} (CCons x xs) = let r = split xs
                                             in (CCons x (fst r), snd r)
split {as = (C Uni a) :: as} (UnInitCons xs) = let r = split xs
                                               in (UnInitCons (fst r), snd r)
