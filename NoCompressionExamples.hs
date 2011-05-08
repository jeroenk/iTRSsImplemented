{-
Copyright (C) 2011 Jeroen Ketema

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

-- This file defines some non-compressible reductions.

import Omega
import Reduction
import NoCompression

-- The depths at which reduction steps occur.
fin_in_set :: Integer -> Bool
fin_in_set n = n `elem` [1, 3, 5, 7]

-- Upper-bound on the depths at which reduction steps occur.
fin_geq_lub :: Integer -> Bool
fin_geq_lub n = n >= 10

-- Bijection between depths and steps of the reduction.
fin_nu :: Integer -> Omega
fin_nu 1 = OmegaElement 2
fin_nu 3 = OmegaElement 1
fin_nu 5 = OmegaElement 0
fin_nu 7 = OmegaElement 3
fin_nu _ = error "Impossible"

-- Helper function for the construction of computable sequences.
constr :: (Omega -> t) -> OmegaSequence t
constr fun = construct_sequence (map fun [OmegaElement n | n <- [0..]])

fin_red :: CReduction Sigma Var System_Non_LL
fin_red = construct_reduction fin_in_set fin_geq_lub fin_nu lim constr constr
    where lim = OmegaElement 4
