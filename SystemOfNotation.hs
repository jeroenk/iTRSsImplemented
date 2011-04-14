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

-- This module defines systems of notation (for computable ordinals).

module SystemOfNotation (
    OrdinalKind(ZeroOrdinal, SuccOrdinal, LimitOrdinal),
    SystemOfNotation(ord_kind, ord_pred, ord_limit, ord_to_int),
    get_limit_pred,
    UnivalSystem(ord_leq, ord_zero, ord_succ),
    Omega(OmegaElement)
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

-- A system of notation defines functions ord_kind, ord_pred, and ord_limit
-- (called k, p, and q in Kleene's original paper).
--
-- To add flexibility, the type of a system of notation is left unspecified
-- (not defaulting to natural numbers). This does mean a way is needed to
-- unpack an element of the type to a natural number (ord_to_int).
class SystemOfNotation o where
    ord_kind   :: o -> OrdinalKind
    ord_pred   :: o -> o
    ord_limit  :: o -> (Int -> o)
    ord_to_int :: o -> Int

-- Given an ordinal yield the largest ordinal that is a limit ordinal or zero
-- and that is smaller than the given ordinal.
get_limit_pred :: (SystemOfNotation o) => o -> o
get_limit_pred n = get_limit_pred' (ord_kind n) n
    where get_limit_pred' ZeroOrdinal  m = m
          get_limit_pred' SuccOrdinal  m = get_limit_pred (ord_pred m)
          get_limit_pred' LimitOrdinal m = m

-- In a univalent, recursively related system of notation it is possible to
-- compare two ordinals, to find the representation of zero, and to compute
-- the successor of an ordinal.
class SystemOfNotation o => UnivalSystem o where
    ord_leq  :: o -> o -> Bool
    ord_zero :: o      -- Existence follows by univalence
    ord_succ :: o -> o -- Existence follows by univalence

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
        = error "Limit function undefined" -- omega has no limit ordinals
    ord_to_int  (OmegaElement n)
        = n

instance UnivalSystem Omega where
    ord_leq (OmegaElement m) (OmegaElement n)
        = m <= n
    ord_zero
        = OmegaElement 0
    ord_succ (OmegaElement n)
        = OmegaElement (n + 1)
