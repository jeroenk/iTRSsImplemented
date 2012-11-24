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
-- computable sequences over computable ordinals (given systems of notation).

module SystemOfNotation (
    OrdinalKind(ZeroOrdinal, SuccOrdinal, LimitOrdinal),
    SystemOfNotation(ord_kind, ord_pred, ord_limit, ord_lim_pred, ord_to_int),
    UnivalentSystem(ord_leq, ord_zero, ord_succ),
    ComputableSequence(get_elem, get_from, select, omega_dom),
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
-- exists. The function ord_to_int only makes sense in case the represented
-- ordinal is at most omega.
class SystemOfNotation o where
    ord_kind     :: o -> OrdinalKind
    ord_pred     :: o -> o
    ord_limit    :: o -> Integer -> o
    ord_lim_pred :: o -> o
    ord_to_int   :: o -> Integer

    -- Default implementation of ord_lim_pred
    ord_lim_pred alpha = ord_lim_pred' (ord_kind alpha) alpha
        where ord_lim_pred' ZeroOrdinal  beta = beta
              ord_lim_pred' SuccOrdinal  beta = ord_lim_pred (ord_pred beta)
              ord_lim_pred' LimitOrdinal beta = beta

    -- Default implementation of ord_to_int
    ord_to_int _ = error "Function ord_to_int not implemented"

-- In a univalent, recursively related system of notation it is possible to
-- compare two ordinals and compute the unique representation of zero and
-- any successor of an ordinal. The behaviour of ord_succ is undefined in
-- case the ordinal whose successor is being computed does not have one in
-- the given system of notation.
class SystemOfNotation o => UnivalentSystem o where
    ord_leq     :: o -> o -> Bool
    ord_zero    :: o
    ord_succ    :: o -> o

-- A computable sequence of elements is a function from some ordinal to the
-- elements of a certain type. The employed ordinal might be choosen larger
-- than strictly required for the given sequence, in which case the behaviour
-- of the operations is undefined for ordinals outside the range of the
-- defined sequence.
--
-- The operations are as follows:
-- * get_elem s a       Yields the a-th element of the sequence s
-- * get_from s a       Enumerates the elements of s starting from a
-- * select s f (x, a)  Selects elements of the sequence; the function f yields
--                      the next element to select and is expected to be a
--                      monotone function
-- * omega_dom s        Yield True in case the employed ordinal is at most omega
class UnivalentSystem o => ComputableSequence o t s | s -> o t where
    get_elem  :: s -> o -> t
    get_from  :: s -> o -> [t]
    select    :: s -> ((a, o) -> (a, Maybe o)) -> (a, Maybe o) -> [t]
    omega_dom :: s -> Bool

    -- Default implementation of get_from
    get_from s alpha = get_elem s alpha : get_from s (ord_succ alpha)

    -- Default implementation of select
    select _ _ (_, Nothing)    = []
    select s f (x, Just alpha) = get_elem s alpha : select s f next_elem
        where next_elem = f (x, alpha)

    -- Default implementation of omega_dom
    omega_dom _ = False
