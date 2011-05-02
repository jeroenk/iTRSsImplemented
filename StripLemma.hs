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

-- This module implements the Strip Lemma for reductions up to length omega.

module StripLemma (
    strip_lemma
) where

import SignatureAndVariables
import PositionAndSubterm
import RuleAndSystem
import SystemOfNotation
import Reduction
import Omega

import List

-- The function bottom_list computes the bottom reduction from the Strip Lemma.
-- The steps of the reduction are returned as a list of lists of steps, where it
-- is ensured for the ith item in the list that all its steps occur at depth
-- at least i.
--
-- The function gather has five arguments: depth, number of used parallel steps,
-- unused parallel steps, previous parallel steps, the final term after applying
-- all rewrite steps found thusfar.
--
-- For the modulus use the observation that in the worst case a variable in the
-- left-hand side of a rewrite rule is moved all the way to the root of the
bottom_list :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> [[Step s v]]
bottom_list reduction@(CRCons (RCons _ ss) phi) step@(_, rule)
    = gather 0 0 psteps_all [] t_initial
    where t_initial  = rewrite_step (initial_term reduction) step
          psteps_all = project (enum ss) step
          height     = left_height rule
          gather d p_used unused psteps t
              = steps_d : gather (d + 1) p_used' unused' psteps' t'
                  where t' = last (rewrite_steps t steps_d)
                        (steps_d, psteps') = parallel_needed_steps psteps_new ps
                        ps         = pos_to_depth t d
                        psteps_new = psteps ++ used
                        (used, unused') = genericSplitAt p_new unused
                        p_new   = p_used' - p_used
                        p_used' = max p_used modulus
                        modulus = ord_to_int (phi ord_zero (d + height))

project :: (Signature s, Variables v)
    => [Step s v] -> Step s v -> [ParallelStep s v]
project steps (position, rule) = project' steps (pos_to_dpos position)
    where project' [] _           = []
          project' ((p, r):ss) qd = pstep : project' ss descendants_qd
              where relevant_qd    = genericTake (pos_len p + 1) qd
                    steps_down     = zip (concat relevant_qd) (repeat rule)
                    descendants_p  = descendants steps_down (pos_to_dpos p)
                    pstep          = (descendants_p, r)
                    descendants_qd = descendants [(p, r)] qd

-- Concatenate the lists produced by bottom_list to all steps of the bottom
-- reduction.
bottom_steps :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> [Step s v]
bottom_steps reduction step = concat steps_list
    where steps_list = bottom_list reduction step

-- Compute the modulus of the bottom reduction using that the ith element of
-- the list produced by bottom_list contains only steps at depth at least i.
bottom_modulus :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> Modulus Omega
bottom_modulus reduction step = construct_modulus phi
    where phi n      = genericLength (concat (genericTake (n + 1) steps_list))
          steps_list = bottom_list reduction step

-- Yield the bottom reduction of the Strip Lemma.
bottom_reduction :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> CReduction s v r
bottom_reduction reduction step = CRCons (RCons ts ss) phi
    where ts    = construct_sequence terms
          ss    = construct_sequence steps
          phi   = bottom_modulus reduction step
          terms = rewrite_steps term steps
          term  = rewrite_step (initial_term reduction) step
          steps = bottom_steps reduction step

-- The function right_list computes the right-most reduction of the Strip
-- Lemma. The steps of the reduction are returned as a list of lists of steps,
-- where it is ensured for the ith item in the list that all steps occur at
-- depth i.
--
-- The function gather has two arguments: depth and the final term after
-- applying all rewrite steps found thusfar.
right_list :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> [[Step s v]]
right_list reduction (position, rule) = gather 0 (final_term reduction)
    where pd = pos_to_dpos position
          gather d t = steps_d : gather (d + 1) t'
              where t'      = last (rewrite_steps t steps_d)
                    steps_d = zip (genericIndex pd' d) (repeat rule)
                    pd'     = descendants steps pd
                    steps   = needed_steps reduction ps
                    ps      = pos_to_depth t d

-- Concatenate the lists produced by right_list to obtain all steps of the
-- right-most reduction.
right_steps :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> [Step s v]
right_steps reduction step = concat steps_list
    where steps_list = right_list reduction step

-- Compute the modulus of the right-most reduction using that the ith element
-- of the list produced by right_list contains all steps at depth i.
right_modulus :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> Modulus Omega
right_modulus reduction step = construct_modulus phi_new
    where phi_new n  = genericLength (concat (genericTake (n + 1) steps_list))
          steps_list = right_list reduction step

-- Yield the right-most reduction of the Strip Lemma.
right_reduction :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> CReduction s v r
right_reduction reduction step = CRCons (RCons ts ss) phi
    where ts    = construct_sequence terms
          ss    = construct_sequence steps
          phi   = right_modulus reduction step
          terms = rewrite_steps (final_term reduction) steps
          steps = right_steps reduction step

-- The Strip Lemma for orthogonal systems.
--
-- It is assumed the input reduction has at most length omega.
strip_lemma :: RewriteSystem s v r
    => r -> CReduction s v r -> Step s v -> (CReduction s v r, CReduction s v r)
strip_lemma _ reduction step
    | at_most_omega reduction = (bottom, right)
    | otherwise               = error "Reduction too long"
        where bottom = bottom_reduction reduction step
              right  = right_reduction reduction step
