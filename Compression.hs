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

-- This module implements compression of transfinite reductions.
--
-- Note that the module uses the internal structure of the system of notation
-- defined for Omega: the system is assumed to be effectively the identity
-- mapping.

module Compression (
    compression
) where

import SignatureAndVariables
import RuleAndSystem
import SystemOfNotation
import TransfiniteReduction

-- The function compr_devel computes the compressed reduction. The steps of the
-- reduction are returned as a list of lists of steps, where it is ensured for
-- the ith item in the list that all its steps occur at depth i.
compr_devel :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o -> [[Step s v]]
compr_devel s = compr_devel' 0 []
    where compr_devel' d prev = new_steps : compr_devel' (d + 1) total
              where total     = needed_steps s d
                    new_steps = filter_steps prev total

-- Concatenate the lists produced by compr_devel to obtain all steps.
compr_steps :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o -> [Step s v]
compr_steps s = concat (compr_devel s)

-- Compute the modulus using that the ith element of the list produced by
-- compr_devel contains all steps at depth i.
compr_modulus :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o -> (Modulus Omega)
compr_modulus s (OmegaElement n)
    | n == 0    = \m -> OmegaElement (compute m)
    | otherwise = error "Modulus only defined for zero"
        where compute m = length (concat (take (m + 1) (compr_devel s)))

-- Compression of left-linear rewrite systems with finite right-hand sides.
compression :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => r -> (CReduction s v r o) -> (CReduction s v r Omega)
compression _ s = CRCons (RCons terms steps ord_zero) modulus
    where terms   = rewrite_steps (initial_term s) steps
          steps   = compr_steps s
          modulus = compr_modulus s
