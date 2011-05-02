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

-- This module implements Church-Rosser.
--
-- A conversion is defined as a finite sequence of valleys, i.e. a sequence
-- of the form: s (->>.<<-)^+ t. The sequence is represented as a element
-- of the type [(CReduction s v r, CReduction s v r)], i.e. as a list of
-- valleys. Note that the list may not be empty, which would make it impossible
-- to output a pair of reductions, as we can no longer compute any initial
-- terms of the reductions.

module ChurchRosser (
    church_rosser
) where

import SignatureAndVariables
import PositionAndSubterm
import RuleAndSystem
import Reduction
import Omega
import Compression
import Confluence

import List

-- The function interleave_devel computes the interleaving of a pair of
-- reductions that can be concatenated. The steps of the reduction are returned
-- as a list of lists of steps, where it is ensured for the ith item in the
-- list that all its steps occur at depth at least i.
--
-- The function gather has three arguments: depth, previous steps, and previous
-- parallel steps.
interleave_list :: RewriteSystem s v r
    => CReduction s v r -> CReduction s v r -> [[Step s v]]
interleave_list reduction_0 reduction_1 = gather 0 [] []
    where t_final = final_term reduction_1
          gather d prev psteps = steps_d : gather (d + 1) total psteps'
              where (steps_d, psteps') = filter_steps prev psteps total ps
                    total   = total_0 ++ total_1
                    total_0 = needed_steps reduction_0 ps'
                    total_1 = needed_steps reduction_1 ps
                    ps'     = needed_positions reduction_1 ps
                    ps      = pos_to_depth t_final d

-- Concatenate the lists produced by interleave_list to obtain all steps.
interleave_steps :: RewriteSystem s v r
    => CReduction s v r -> CReduction s v r -> [Step s v]
interleave_steps reduction_0 reduction_1 = concat steps_list
    where steps_list = interleave_list reduction_0 reduction_1

-- Compute the modulus using that the ith element of the list produced by
-- interleave_list contains only steps at depth at least i.
interleave_modulus :: RewriteSystem s v r
    => CReduction s v r -> CReduction s v r -> Modulus Omega
interleave_modulus reduction_0 reduction_1 = construct_modulus phi
    where phi n      = genericLength (concat (genericTake (n + 1) steps_list))
          steps_list = interleave_list reduction_0 reduction_1

-- Yield the interleaving of a pair of reductions that can be concatenated,
-- i.e. given s ->>.->> t a reduction s ->> t is returned.
interleave :: RewriteSystem s v r
    => r -> CReduction s v r -> CReduction s v r -> CReduction s v r
interleave _ reduction_0 reduction_1 = CRCons (RCons ts ss) phi
    where ts    = construct_sequence terms
          ss    = construct_sequence steps
          terms = rewrite_steps (initial_term reduction_0) steps
          steps = interleave_steps reduction_0 reduction_1
          phi   = interleave_modulus reduction_0 reduction_1

-- Church-Rosser of orthogonal, non-collapsing rewrite systems. The function
-- implements the classic proof except for the concatenation of reductions
-- which is replaced by an interleaving scheme.
church_rosser ::  (Signature s, Variables v, RewriteSystem s v r)
    => r -> [(CReduction s v r, CReduction s v r)]
               -> (CReduction s v r, CReduction s v r)
church_rosser system conversion = church_rosser' (map compress conversion)
    where compress (s, t) = (compression system s, compression system t)
          church_rosser' []
              = error "Conversion withour reductions"
          church_rosser' ((s, t):[])
              = (s, t)
          church_rosser' ((s_1, t_1):(s_2, t_2):cs)
              = church_rosser' ((s_new, t_new) : cs)
              where s_new = interleave system s_1 (fst confl)
                    t_new = interleave system t_2 (snd confl)
                    confl = confluence system (t_1, s_2)
