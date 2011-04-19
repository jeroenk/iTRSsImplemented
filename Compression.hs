{-
Copyright (C) 2010, 2011 Jeroen Ketema and Jakob Grue Simonsen

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

module Compression (
    compression
) where

import RuleAndSystem
import TransfiniteReduction
import Omega

-- The function compr_list computes the compressed reduction. The steps of the
-- reduction are returned as a list of lists of steps, where it is ensured for
-- the i-th item in the list that all its steps occur at depth i.
compr_list :: RewriteSystem s v r
    => CReduction s v r -> [[Step s v]]
compr_list reduction = compr_list' 0 []
    where compr_list' depth prev = steps_new : compr_list' (depth + 1) total
              where total     = needed_steps reduction depth
                    steps_new = filter_steps prev total

-- Concatenate the lists produced by compr_devel to obtain all steps.
compr_steps :: RewriteSystem s v r
    => CReduction s v r -> [Step s v]
compr_steps reduction = concat list_steps
    where list_steps = compr_list reduction

-- Compute the modulus using that the ith element of the list produced by
-- compr_devel contains all steps at depth i.
compr_modulus :: RewriteSystem s v r
    => CReduction s v r -> (Modulus Omega)
compr_modulus reduction = construct_modulus phi
    where phi x      = length (concat (take (x + 1) steps_list))
          steps_list = compr_list reduction

-- Compression of left-linear rewrite systems with finite right-hand sides.
compression :: RewriteSystem s v r
    => r -> CReduction s v r -> CReduction s v r
compression _ reduction
    | at_most_omega reduction = reduction
    | otherwise               = CRCons (RCons ts ss) phi
        where ts    = construct_sequence terms
              ss    = construct_sequence steps
              phi   = compr_modulus reduction
              terms = rewrite_steps (initial_term reduction) steps
              steps = compr_steps reduction
