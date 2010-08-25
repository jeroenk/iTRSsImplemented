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

-- This module defines systems of notation (for computable ordinals)

module SystemsOfNotation (
    OrdinalType(ZeroOrdinal, SuccOrdinal, LimitOrdinal),
    SystemOfNotation(k, p, q, to_int),
    get_limit_pred,
    UnivalSystem(leq, zer, suc),
    Omega(OmegaElement)
) where

-- An ordinal can have three different types
data OrdinalType
    = ZeroOrdinal
    | SuccOrdinal
    | LimitOrdinal

instance Eq OrdinalType where
    ZeroOrdinal == ZeroOrdinal   = True
    SuccOrdinal == SuccOrdinal   = True
    LimitOrdinal == LimitOrdinal = True
    _ == _                       = False

-- A system of notation defines the functions k, p, and q
--
-- Because we want some flexibility, we leave the actual type of a system of
-- notation unspecified (we do not default to natural numbers). This means we
-- do need a way to unpack an element of the type to a natural number (to_int).
class SystemOfNotation o where
    k :: o -> OrdinalType
    p :: o -> o
    q :: o -> (Int -> o)
    to_int :: o -> Int

-- Get the largest ordinal that is a limit ordinal or zero and smaller than a
-- certain other ordinal 
get_limit_pred :: (SystemOfNotation o) => o -> o
get_limit_pred n = get_limit_pred' (k n) n
    where get_limit_pred' ZeroOrdinal m  = m
          get_limit_pred' SuccOrdinal m  = get_limit_pred (p m)
          get_limit_pred' LimitOrdinal m = m

-- In a univalent system of notation it is possible to compare two ordinals
class SystemOfNotation o => UnivalSystem o where
    leq :: o -> o -> Bool
    zer :: o      -- Existence follows by univalence
    suc :: o -> o -- Existence follows by univalence

-- A system of notation for the ordinal omega
data Omega = OmegaElement Int

instance SystemOfNotation Omega where
    k (OmegaElement n)
        | n == 0    = ZeroOrdinal
        | otherwise = SuccOrdinal
    p  (OmegaElement n)
        | n > 0     = OmegaElement (n - 1)
        | otherwise = error "Predeccessor undefined"
    q  (OmegaElement _)
        = error "Limit function undefined" -- omega has no limit ordinals
    to_int  (OmegaElement n)
        = n

instance UnivalSystem Omega where
    leq (OmegaElement m) (OmegaElement n)
        = m <= n
    zer
        = OmegaElement 0
    suc (OmegaElement n)
        = OmegaElement (n + 1)
