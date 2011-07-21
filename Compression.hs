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

import PositionAndSubterm
import RuleAndSystem
import Reduction
import Omega

import Data.List

-- The function compr_list computes the compressed reduction. The steps of the
-- reduction are returned as a list of lists of steps, where it is ensured for
-- the ith item in the list that all its steps occur at depth at least i.
--
-- The function gather has four arguments: depth, previous steps, and previous
-- parallel steps.
compr_list :: RewriteSystem s v r
    => CReduction s v r -> [[Step s v]]
compr_list reduction = gather 0 [] []
    where t_final = final_term reduction
          gather d prev psteps = steps_d : gather (d + 1) total psteps'
              where (steps_d, psteps') = filter_steps prev psteps total ps
                    total = needed_steps reduction ps
                    ps    = pos_to_depth t_final d

-- Concatenate the lists produced by compr_list to obtain all steps.
compr_steps :: RewriteSystem s v r
    => CReduction s v r -> [Step s v]
compr_steps reduction = concat list_steps
    where list_steps = compr_list reduction

-- Compute the modulus using that the ith element of the list produced by
-- compr_list contains only steps at depth at least i.
compr_modulus :: RewriteSystem s v r
    => CReduction s v r -> Modulus Omega
compr_modulus reduction = construct_modulus phi
    where phi n      = genericLength (concat (genericTake (n + 1) steps_list))
          steps_list = compr_list reduction

-- Compression of left-linear rewrite systems.
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
