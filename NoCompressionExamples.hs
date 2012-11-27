{-
Copyright (C) 2011, 2012 Jeroen Ketema

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

-- This file defines a non-compressible reduction.

import Omega
import Reduction
import NoCompression

import Prelude

-- The depths at which reduction steps occur.
finInSet :: Integer -> Bool
finInSet n = n `elem` [1, 3, 5, 7]

-- Upper-bound on the depths at which reduction steps occur.
finGeqLub :: Integer -> Bool
finGeqLub n = n >= 10

-- Bijection between depths and steps of the reduction.
finNu :: Integer -> Omega
finNu 1 = OmegaElement 2
finNu 3 = OmegaElement 1
finNu 5 = OmegaElement 0
finNu 7 = OmegaElement 3
finNu _ = error "Impossible"

-- Helper function for the construction of computable sequences.
constr :: (Omega -> t) -> OmegaSequence t
constr fun = constructSequence (map fun [OmegaElement n | n <- [0..]])

finRed :: CReduction Sigma Var SystemNonLL
finRed = constructReduction finInSet finGeqLub finNu lim constr constr
    where lim = OmegaElement 4
