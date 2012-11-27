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

-- This module implements the Strip Lemma for reductions up to length omega.

module StripLemma (
    stripLemma
) where

import SignatureAndVariables
import Term
import PositionAndSubterm
import RuleAndSystem
import SystemOfNotation
import Reduction
import ParallelReduction
import Omega

import Prelude
import Data.List

-- The function bottomList computes the bottom reduction from the Strip Lemma.
-- The steps of the reduction are returned as a list of lists of steps, where it
-- is ensured for the ith item in the list that all its steps occur at depth
-- at least i.
--
-- The function gather has four arguments: depth, number of used parallel steps,
-- unused parallel steps, previous parallel steps.
--
-- For the modulus use the observation that in the worst case a variable in the
-- left-hand side of a rewrite rule is moved all the way to the root of the
-- right-hand side.
bottomList :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> Term s v -> [[Step s v]]
bottomList (CRCons (RCons _ ss) phi) step@(_, Rule l _) final
    = gather 0 0 psteps_all []
    where psteps_all = project (getFrom ss ordZero) step
          height     = termHeight l
          gather d p_used unused psteps
              = steps_d : gather (d + 1) p_used' unused' psteps'
                  where (steps_d, psteps') = parallelNeededSteps psteps_new ps
                        ps          = posToDepth final d
                        psteps_new  = psteps ++ used
                        (used, unused') = genericSplitAt p_new unused
                        p_new    = p_used' - p_used
                        p_used'  = max p_used modulus
                        modulus  = ord2Int (phi ordZero (d + height))

-- Project the steps from the top reduction to obtain the parallel steps that
-- form the bottom reduction.
project :: (Signature s, Variables v)
    => [Step s v] -> Step s v -> [ParallelStep s v]
project steps (position, rule) = project' steps pstep
    where pstep = (pos2PosFun position, rule)
          project' [] _      = []
          project' (s:ss) ps = s_projected : project' ss ps_projected
              where (ps_projected, s_projected) = diamondProperty s ps

-- Concatenate the lists produced by bottomList to obtain all steps of the
-- bottom reduction.
bottomSteps :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> Term s v -> [Step s v]
bottomSteps reduction step final = concat steps_list
    where steps_list = bottomList reduction step final

-- Compute the modulus of the bottom reduction using that the ith element of
-- the list produced by bottomList contains only steps at depth at least i.
bottomModulus :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> Term s v -> Modulus Omega
bottomModulus reduction step final = constructModulus phi
    where phi n      = genericLength $ concat $ genericTake (n + 1) steps_list
          steps_list = bottomList reduction step final

-- Yield the bottom reduction of the Strip Lemma.
bottomReduction :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> Term s v -> CReduction s v r
bottomReduction reduction step final = CRCons (RCons ts ss) phi
    where ts      = constructSequence terms
          ss      = constructSequence steps
          phi     = bottomModulus reduction step final
          terms   = rewriteSteps initial steps
          initial = rewriteStep (initialTerm reduction) step
          steps   = bottomSteps reduction step final

-- The function rightList computes the right-most reduction of the Strip
-- Lemma. The steps of the reduction are returned as a list of lists of steps,
-- where it is ensured for the ith item in the list that all steps occur at
-- depth i.
rightList :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> [[Step s v]]
rightList reduction (position, rule) = map (map pair) pf_d
    where pf     = pos2PosFun position
          pf_d   = descendants reduction pf
          pair p = (p, rule)

-- Concatenate the lists produced by rightList to obtain all steps of the
-- right-most reduction.
rightSteps :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> [Step s v]
rightSteps reduction step = concat steps_list
    where steps_list = rightList reduction step

-- Compute the modulus of the right-most reduction using that the ith element
-- of the list produced by rightList contains all steps at depth i.
rightModulus :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> Modulus Omega
rightModulus reduction step = constructModulus phi_new
    where phi_new n  = genericLength $ concat $ genericTake (n + 1) steps_list
          steps_list = rightList reduction step

-- Yield the right-most reduction of the Strip Lemma.
rightReduction :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> CReduction s v r
rightReduction reduction step = CRCons (RCons ts ss) phi
    where ts    = constructSequence terms
          ss    = constructSequence steps
          phi   = rightModulus reduction step
          terms = rewriteSteps (finalTerm reduction) steps
          steps = rightSteps reduction step

-- The Strip Lemma for orthogonal systems.
--
-- It is assumed the input reduction has at most length omega.
stripLemma :: RewriteSystem s v r
    => r -> CReduction s v r -> Step s v -> (CReduction s v r, CReduction s v r)
stripLemma _ reduction step
    | atMostLengthOmega reduction = (bottom, right)
    | otherwise                   = error "Reduction too long"
        where bottom = bottomReduction reduction step (finalTerm right)
              right  = rightReduction reduction step
