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

import Prelude
import Data.List

-- The function confluenceList computes one side of the confluence diagram. The
-- steps of the reduction are returned as a list of lists of steps, where it
-- is ensured for the ith item in the list that all its steps occur at depth
-- at least i.
--
-- The function gather has six arguments: depth, number of used steps of the
-- reduction projected over, unused steps of the reduction projected over,
-- current projected reduction, number of previously found steps.
confluenceList :: RewriteSystem s v r
    => r -> CReduction s v r -> CReduction s v r -> [[Step s v]]
confluenceList system (CRCons (RCons _ ss) phi) reduction
    = gather 0 0 reduction (getFrom ss ordZero) 0
    where gather d n r unused prev
              | add_steps = steps_d : gather (d + 1) n r unused (length total)
              | otherwise = gather d (n + 1) r' (tail unused) prev
                  where add_steps = ord2Int modulus <= n
                        modulus   = phi ordZero origin_d
                        origin_d  = maximum $ map positionLength origin_ps
                        origin_ps = origins r ps
                        steps_d   = genericDrop prev total
                        total     = neededSteps r ps
                        ps        = posToDepth (finalTerm r) d
                        r'        = fst $ stripLemma system r $ head unused

-- Concatenate the lists produced by confluenceList to obtain all steps.
confluenceSteps :: RewriteSystem s v r
    => r -> CReduction s v r -> CReduction s v r -> [Step s v]
confluenceSteps system reduction_0 reduction_1 = concat steps_list
    where steps_list = confluenceList system reduction_0 reduction_1

-- Compute the modulus using that the ith element of the list produced by
-- confluenceList contains all steps at depth i.
confluenceModulus :: RewriteSystem s v r
    => r -> CReduction s v r -> CReduction s v r -> Modulus Omega
confluenceModulus system reduction_0 reduction_1 = constructModulus phi
    where phi n      = genericLength $ concat $ genericTake (n + 1) steps_list
          steps_list = confluenceList system reduction_0 reduction_1

-- Yield either the right-most or bottom reduction of the confluence diagram.
confluenceSide :: RewriteSystem s v r
    => r -> CReduction s v r -> CReduction s v r -> CReduction s v r
confluenceSide system reduction_0 reduction_1 = CRCons (RCons ts ss) phi
    where ts    = constructSequence terms
          ss    = constructSequence steps
          phi   = confluenceModulus system reduction_0 reduction_1
          terms = rewriteSteps (finalTerm reduction_0) steps
          steps = confluenceSteps system reduction_0 reduction_1

-- Confluence of orthogonal, non-collapsing rewrite systems.
confluence :: (RewriteSystem s v r)
    => r -> (CReduction s v r, CReduction s v r)
       -> (CReduction s v r, CReduction s v r)
confluence system (left_reduction, top_reduction) = (bottom, right)
    where bottom = confluenceSide system left top
          right  = confluenceSide system top left
          left   = compression system left_reduction
          top    = compression system top_reduction
