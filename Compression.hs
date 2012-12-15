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

-- This module implements compression of transfinite reductions.

module Compression (
    compression
) where

import PositionAndSubterm
import RuleAndSystem
import Reduction
import ParallelReduction
import Omega

import Prelude
import Data.List

-- The function compressionList computes the compressed reduction. The steps of
-- the reduction are returned as a list of lists of steps, where it is ensured
-- for the i-th item in the list that all its steps occur at depth at least i.
--
-- The function gather has three arguments: depth, previous steps, and previous
-- parallel steps.
compressionList :: RewriteSystem s v r
    => CReduction s v r -> [[Step s v]]
compressionList reduction = gather 0 [] []
    where final = finalTerm reduction
          gather d prev psteps = steps_d : gather (d + 1) total psteps'
              where (steps_d, psteps') = filterNeededSteps prev psteps total ps
                    total = neededSteps reduction ps
                    ps    = posToDepth final d

-- Concatenate the lists produced by compressionList to obtain all steps.
compressionSteps :: RewriteSystem s v r
    => CReduction s v r -> [Step s v]
compressionSteps reduction = concat steps_list
    where steps_list = compressionList reduction

-- Compute the modulus using that the ith element of the list produced by
-- compressionList contains only steps at depth at least i.
compressionModulus :: RewriteSystem s v r
    => CReduction s v r -> Modulus Omega
compressionModulus reduction = constructModulus phi
    where phi n      = genericLength $ concat $ genericTake (n + 1) steps_list
          steps_list = compressionList reduction

-- Compression of reductions in left-linear rewrite systems.
--
-- Return the original reduction in case it already has length at most omega.
compression :: RewriteSystem s v r
    => r -> CReduction s v r -> CReduction s v r
compression _ reduction
    | atMostLengthOmega reduction = reduction
    | otherwise                   = CRCons (RCons ts ss) phi
        where ts    = constructSequence terms
              ss    = constructSequence steps
              phi   = compressionModulus reduction
              terms = rewriteSteps (initialTerm reduction) steps
              steps = compressionSteps reduction
