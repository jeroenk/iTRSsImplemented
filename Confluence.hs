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

-- This module implements confluence.

module Confluence (
    confluence
) where

import PositionAndSubterm
import RuleAndSystem
import SystemOfNotation
import Reduction
import Omega
import StripLemma
import Compression

import List

-- The function confl_devel computes one side of the confluence diagram. The
-- steps of the reduction are returned as a list of lists of steps, where it
-- is ensured for the ith item in the list that all its steps occur at depth
-- at least i.
--
-- The function gather has six arguments: depth, number of used steps, unused
-- steps, current projected reduction, previous steps, previous parallel steps.
confl_list :: RewriteSystem s v r
    => r -> CReduction s v r -> CReduction s v r -> [[Step s v]]
confl_list system (CRCons (RCons _ ss) phi) reduction
    = gather 0 0 reduction (get_from ss ord_zero) [] []
    where gather d n r unused prev psteps
              | add_steps = steps_d : gather (d + 1) n r unused total psteps'
              | otherwise = gather d (n + 1) r' (tail unused) prev psteps
                  where add_steps = ord_to_int modulus <= n
                        modulus   = phi ord_zero (maximum (map pos_len ps'))
                        ps'       = needed_positions r ps
                        (steps_d, psteps') = filter_steps prev psteps total ps
                        total = needed_steps r ps
                        ps    = pos_to_depth (final_term r) d
                        r'    = fst (strip_lemma system r (head unused))

-- Concatenate the lists produced by confl_list to obtain all steps.
confl_steps :: RewriteSystem s v r
    => r -> CReduction s v r -> CReduction s v r -> [Step s v]
confl_steps system reduction_0 reduction_1 = concat steps_list
    where steps_list = confl_list system reduction_0 reduction_1

-- Compute the modulus using that the ith element of the list produced by
-- confl_devel contains all steps at depth i.
confl_modulus :: RewriteSystem s v r
    => r -> CReduction s v r -> CReduction s v r -> Modulus Omega
confl_modulus system reduction_0 reduction_1 = construct_modulus phi
    where phi n      = genericLength (concat (genericTake (n + 1) steps_list))
          steps_list = confl_list system reduction_0 reduction_1

-- Yield either the right-most or bottom reduction of the confluence diagram.
confl_side :: RewriteSystem s v r
    => r -> CReduction s v r -> CReduction s v r -> CReduction s v r
confl_side system reduction_0 reduction_1 = CRCons (RCons ts ss) phi
    where ts    = construct_sequence terms
          ss    = construct_sequence steps
          phi   = confl_modulus system reduction_0 reduction_1
          terms = rewrite_steps (final_term reduction_0) steps
          steps = confl_steps system reduction_0 reduction_1

-- Confluence of orthogonal, non-collapsing rewrite systems.
confluence :: (RewriteSystem s v r)
    => r -> (CReduction s v r, CReduction s v r)
              -> (CReduction s v r, CReduction s v r)
confluence system (left_reduction, top_reduction) = (bottom, right)
    where bottom = confl_side system left top
          right  = confl_side system top left
          left   = compression system left_reduction
          top    = compression system top_reduction
