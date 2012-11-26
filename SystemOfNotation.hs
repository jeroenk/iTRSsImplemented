{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
{-
Copyright (C) 2010, 2011, 2012 Jeroen Ketema and Jakob Grue Simonsen

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
-}

-- This module defines systems of notation for computable ordinals and
-- computable sequences over computable ordinals (given a system of notation).

module SystemOfNotation (
    OrdinalKind(ZeroOrdinal, SuccOrdinal, LimitOrdinal),
    SystemOfNotation(ordKind, ordPred, ordLimit, ordLimitPred, ord2Int),
    UnivalentSystem(ordLeq, ordZero, ordSucc),
    ComputableSequence(getElem, getFrom, select, hasOmegaDomain),
) where

import Prelude

-- An ordinal can have three different kinds.
data OrdinalKind
    = ZeroOrdinal
    | SuccOrdinal
    | LimitOrdinal

instance Eq OrdinalKind where
    ZeroOrdinal  == ZeroOrdinal  = True
    SuccOrdinal  == SuccOrdinal  = True
    LimitOrdinal == LimitOrdinal = True
    _ == _                       = False

-- A system of notation defines the operations ordKind, ordPred, and ordLimit
-- (called k, p, and q in Kleene's original paper). To add flexibility, the
-- type of a system of notation is left unspecified, i.e., it is not fixed as
-- a subset of the natural numbers.
--
-- The function ordLimitPred yields the largest ordinal limit ordinal smaller
-- than or equal to the given ordinal and yields zero in case no such ordinal
-- exists. The function ord2Int only makes sense in case the represented
-- ordinal is at most omega.
class SystemOfNotation o where
    ordKind      :: o -> OrdinalKind
    ordPred      :: o -> o
    ordLimit     :: o -> Integer -> o
    ordLimitPred :: o -> o
    ord2Int      :: o -> Integer

    -- Default implementation of ordLimitPred.
    ordLimitPred alpha = ordLimitPred' (ordKind alpha) alpha
        where ordLimitPred' ZeroOrdinal  beta = beta
              ordLimitPred' SuccOrdinal  beta = ordLimitPred (ordPred beta)
              ordLimitPred' LimitOrdinal beta = beta

    -- Default implementation of ord2Int
    ord2Int _ = error "Function ord2Int not implemented"

-- In a univalent, recursively related system of notation it is possible to
-- compare two ordinals and compute the unique representation of zero and of
-- any successor of an ordinal. The behaviour of ordSucc is undefined in
-- case the ordinal whose successor is being computed does not have one in
-- the given system of notation.
class SystemOfNotation o => UnivalentSystem o where
    ordLeq  :: o -> o -> Bool
    ordZero :: o
    ordSucc :: o -> o

-- A computable sequence of elements is a function from an ordinal to the
-- elements of a certain type. The employed ordinal might be choosen larger
-- than strictly required for the given sequence, in which case the behaviour
-- of the operations is undefined for ordinals outside the range of the
-- defined sequence.
--
-- The operations are as follows:
-- * getElem s a        Yields the a-th element of the sequence s
-- * getFrom s a        Enumerates the elements of s starting from a
-- * select s f (x, a)  Selects elements of the sequence; the function f yields
--                      the next element to select and is expected to be a
--                      monotone function
class UnivalentSystem o => ComputableSequence o t s | s -> o t where
    getElem        :: s -> o -> t
    getFrom        :: s -> o -> [t]
    select         :: s -> ((a, o) -> (a, Maybe o)) -> (a, Maybe o) -> [t]
    hasOmegaDomain :: s -> Bool

    -- Default implementation of get_from.
    getFrom s alpha = getElem s alpha : getFrom s (ordSucc alpha)

    -- Default implementation of select.
    select _ _ (_, Nothing)    = []
    select s f (x, Just alpha) = getElem s alpha : select s f next_elem
        where next_elem = f (x, alpha)

    -- Default implementation of hasOmegaDomain
    hasOmegaDomain _ = False
