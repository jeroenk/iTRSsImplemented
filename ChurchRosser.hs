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

-- This module implements a Church-Rosser property.

module ChurchRosser (
    churchRosser
) where

import SignatureAndVariables
import PositionAndSubterm
import RuleAndSystem
import Reduction
import ParallelReduction
import Omega
import Compression
import Confluence

import Prelude
import Data.List

-- A conversion is defined as a finite sequence of valleys, i.e., as a sequence
-- of the form: s (->>.<<-)^+ t. The sequence may not be empty; this would make
-- it impossible to output a pair of reductions, as we can no longer compute
-- any initial terms of the reductions.
type Conversion s v r = [(CReduction s v r, CReduction s v r)]

-- The function interleaveList computes the interleaving of a pair of
-- reductions that can be concatenated. The steps of the reduction are returned
-- as a list of lists of steps, where it is ensured for the ith item in the
-- list that all its steps occur at depth at least i.
--
-- The function gather has three arguments: depth, previous steps, and previous
-- parallel steps.
interleaveList :: RewriteSystem s v r
    => CReduction s v r -> CReduction s v r -> [[Step s v]]
interleaveList reduction_0 reduction_1 = gather 0 [] []
    where final = finalTerm reduction_1
          gather d prev psteps = steps_d : gather (d + 1) total psteps'
              where (steps_d, psteps') = filterNeededSteps prev psteps total ps
                    total   = total_0 ++ total_1
                    total_0 = neededSteps reduction_0 ps'
                    total_1 = neededSteps reduction_1 ps
                    ps'     = origins reduction_1 ps
                    ps      = posToDepth final d

-- Concatenate the lists produced by interleaveList to obtain all steps.
interleaveSteps :: RewriteSystem s v r
    => CReduction s v r -> CReduction s v r -> [Step s v]
interleaveSteps reduction_0 reduction_1 = concat steps_list
    where steps_list = interleaveList reduction_0 reduction_1

-- Compute the modulus using that the ith element of the list produced by
-- interleaveList contains only steps at depth at least i.
interleaveModulus :: RewriteSystem s v r
    => CReduction s v r -> CReduction s v r -> Modulus Omega
interleaveModulus reduction_0 reduction_1 = constructModulus phi
    where phi n      = genericLength $ concat $ genericTake (n + 1) steps_list
          steps_list = interleaveList reduction_0 reduction_1

-- Yield the interleaving of a pair of reductions that can be concatenated,
-- i.e. given s ->>.->> t a reduction s ->> t is returned.
interleave :: RewriteSystem s v r
    => r -> CReduction s v r -> CReduction s v r -> CReduction s v r
interleave _ reduction_0 reduction_1 = CRCons (RCons ts ss) phi
    where ts    = constructSequence terms
          ss    = constructSequence steps
          terms = rewriteSteps (initialTerm reduction_0) steps
          steps = interleaveSteps reduction_0 reduction_1
          phi   = interleaveModulus reduction_0 reduction_1

-- Church-Rosser of orthogonal, non-collapsing rewrite systems. The function
-- implements the classic proof except for the concatenation of reductions
-- which is replaced by an interleaving scheme.
churchRosser ::  (Signature s, Variables v, RewriteSystem s v r)
    => r -> Conversion s v r -> (CReduction s v r, CReduction s v r)
churchRosser system conversion = churchRosser' (map compress conversion)
    where compress (s, t) = (compression system s, compression system t)
          churchRosser' []
              = error "Conversion without reductions"
          churchRosser' ((s, t):[])
              = (s, t)
          churchRosser' ((s_1, t_1):(s_2, t_2):cs)
              = churchRosser' ((s_new, t_new) : cs)
              where s_new = interleave system s_1 (fst confl)
                    t_new = interleave system t_2 (snd confl)
                    confl = confluence system (t_1, s_2)
