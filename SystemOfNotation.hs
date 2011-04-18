{-# LANGUAGE MultiParamTypeClasses,
             FunctionalDependencies,
             FlexibleInstances #-}
{-
Copyright (C) 2010 Jeroen Ketema and Jakob Grue Simonsen

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
-- computable sequences over computable ordinals (given systems of notation).

module SystemOfNotation (
    OrdinalKind(ZeroOrdinal, SuccOrdinal, LimitOrdinal),
    SystemOfNotation(ord_kind, ord_pred, ord_limit, ord_lim_pred),
    UnivalentSystem(ord_leq, ord_eq, ord_less, ord_zero, ord_succ),
    ComputableSequence(get_elem, get_from, get_range),
    Omega(OmegaElement),
    OmegaSequence, construct_sequence
) where

-- An ordinal can have three different types.
data OrdinalKind
    = ZeroOrdinal
    | SuccOrdinal
    | LimitOrdinal

instance Eq OrdinalKind where
    ZeroOrdinal  == ZeroOrdinal  = True
    SuccOrdinal  == SuccOrdinal  = True
    LimitOrdinal == LimitOrdinal = True
    _ == _                       = False

-- A system of notation defines operations ord_kind, ord_pred, and ord_limit
-- (called k, p, and q in Kleene's original paper). To add flexibility, the
-- type of a system of notation is left unspecified.
--
-- The function ord_lim_pred yields the largest ordinal limit ordinal smaller
-- than or equal to the given ordinal and yields zero in case no such ordinal
-- exists.
class SystemOfNotation o where
    ord_kind     :: o -> OrdinalKind
    ord_pred     :: o -> o
    ord_limit    :: o -> (Int -> o)
    ord_lim_pred :: o -> o

    -- Default implementation of ord_lim_pred
    ord_lim_pred a = ord_lim_pred' (ord_kind a) a
        where ord_lim_pred' ZeroOrdinal  b = b
              ord_lim_pred' SuccOrdinal  b = ord_lim_pred (ord_pred b)
              ord_lim_pred' LimitOrdinal b = b

-- In a univalent, recursively related system of notation it is possible to
-- compare two ordinals, to find the representation of zero, and to compute
-- the successor of an ordinal. The behaviour of ord_succ is undefined in
-- case the ordinal whose successor is being computed does not have one in
-- the given system of notation.
class SystemOfNotation o => UnivalentSystem o where
    ord_leq     :: o -> o -> Bool
    ord_eq      :: o -> o -> Bool -- Existence follows from univalence
    ord_less    :: o -> o -> Bool -- Existence follows from ord_leq and ord_eq
    ord_zero    :: o              -- Existence follows by univalence
    ord_succ    :: o -> o         -- Existence follows by univalence

    -- Default implementation of ord_less
    a `ord_less` b    = a `ord_leq` b && not (a `ord_eq` b)

-- A computable sequence of elements is a function from some ordinal to the
-- elements of a certain type. The employed ordinal might be choosen larger
-- than strickly required for the given sequence, in which case the behaviour
-- of the operations is undefined for ordinals outside the range of the
-- defined sequence.
--
-- The operations are as follows:
-- * get_elem s a     Yields the a-th element of the sequence s
-- * get_from s a     Enumerates the elements of s starting from a
-- * get_range s a b  Enumerates the elements of s starting from s and up to b
class UnivalentSystem o => ComputableSequence o t s | s -> o t where
    get_elem  :: s -> o -> t
    get_from  :: s -> o -> [t]
    get_range :: s -> o -> o -> [t]

    -- Default implementation of get_from
    get_from s a = get_elem s a : get_from s (ord_succ a)

    -- Default implementation of get_range
    get_range s a b
        | b `ord_leq` a = []
        | otherwise     = get_elem s a : get_range s (ord_succ a) b

-- A system of notation for the ordinal omega.
data Omega = OmegaElement Int

instance SystemOfNotation Omega where
    ord_kind (OmegaElement n)
        | n == 0    = ZeroOrdinal
        | otherwise = SuccOrdinal
    ord_pred  (OmegaElement n)
        | n > 0     = OmegaElement (n - 1)
        | otherwise = error "Predeccessor undefined"
    ord_limit  (OmegaElement _)
        = error "Limit function undefined" -- Omega has no limit ordinals
    ord_lim_pred (OmegaElement _)
        = OmegaElement 0

instance UnivalentSystem Omega where
    ord_leq (OmegaElement m) (OmegaElement n)
        = m <= n
    ord_eq (OmegaElement m) (OmegaElement n)
        = m == n
    ord_less (OmegaElement m) (OmegaElement n)
        = m < n
    ord_zero
        = OmegaElement 0
    ord_succ (OmegaElement n)
        = OmegaElement (n + 1)

data OmegaSequence t = OmegaSequenceCons [t]

instance ComputableSequence Omega t (OmegaSequence t) where
    get_elem  (OmegaSequenceCons xs) (OmegaElement n)
        = xs!!n
    get_from  (OmegaSequenceCons xs) (OmegaElement n)
        = drop n xs
    get_range (OmegaSequenceCons xs) (OmegaElement m) (OmegaElement n)
        = take (n - m) (drop m xs)

-- Construct a computable sequence of length at most omega out of a list
construct_sequence :: [t] -> OmegaSequence t
construct_sequence xs = OmegaSequenceCons xs
