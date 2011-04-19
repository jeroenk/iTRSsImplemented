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
import TransfiniteReduction
import Omega

-- Yield a sequence of steps all employing the same rule r given a set of
-- parallel positions and the rule r.
sequence_steps :: (Signature s, Variables v)
    => Positions -> RewriteRule s v -> [Step s v]
sequence_steps ps r = map (\p -> (p, r)) ps

-- The function bottom_list computes developments of the bottom reduction
-- of the Strip Lemma. The computation proceeds from left to right and each
-- development is represented by a list of steps.
bottom_list :: (Signature s, Variables v)
    => [Step s v] -> Step s v -> [[Step s v]]
bottom_list steps (p, r) = project steps [p]
    where project [] _
              = []
          project (x@(p', r'):xs) qs
              = steps_new : project xs descendants_qs
              where steps_down     = sequence_steps qs r
                    descendants_p' = descendants steps_down [p']
                    steps_new      = sequence_steps descendants_p' r'
                    descendants_qs = descendants [x] qs

-- Concatenate the developments of the bottom reduction to obtain all steps.
bottom_steps :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> [Step s v]
bottom_steps (CRCons (RCons _ ss) _) step = concat steps_list
    where steps_list = bottom_list (enum ss) step

-- Compute the modulus of the bottom reduction using the observation that in
-- the worse case a variable in the left-hand side of a rewrite rule is moved
-- all the way to the top of the right-hand side term.
bottom_modulus :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> Modulus Omega
bottom_modulus (CRCons (RCons _ ss) phi) step@(_, r) (OmegaElement n)
    | n == 0    = \m -> OmegaElement (compute m)
    | otherwise = error "Modulus only defined for zero"
        where compute m = length (concat (take (ord_to_int modulus) steps_list))
                  where modulus    = phi ord_zero (m + left_height r)
                        steps_list = bottom_list (enum ss) step

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
-- Lemma (which is a development). The steps of the reduction are returned as
-- a list of lists of steps, where it is ensured for the i-th item in the list
-- that all steps occur at depth i.
right_list :: (Signature s, Variables v, UnivalentSystem o)
    => [Step s v] -> Modulus o -> Step s v -> [[Step s v]]
right_list steps phi (p, r) = project steps [p] 0 0
    where project _ [] _ _
              = []
          project xs ps n depth
              = steps_new : project xs_left descendants_nd n' (depth + 1)
              where n' = max n (ord_to_int (phi ord_zero depth))
                    xs_use  = take (n' - n) xs
                    xs_left = drop (n' - n) xs
                    descendants_ps = descendants xs_use ps
                    descendants_d  = filter at_d descendants_ps
                        where at_d q = (length q) == depth
                    descendants_nd = filter not_at_d descendants_ps
                        where not_at_d q = (length q) /= depth
                    steps_new = sequence_steps descendants_d r

-- Concatenate the lists of the right-most reduction to obtain all steps
right_steps :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> [Step s v]
right_steps (CRCons (RCons _ ss) phi) step = concat steps_list
    where steps_list = right_list (enum ss) phi step

-- Compute the modulus of the right-most reduction using that the ith element
-- of the list produced by right_develop contains all steps at depth i.
right_modulus :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> Modulus Omega
right_modulus (CRCons (RCons _ ss) phi) step (OmegaElement n)
    | n == 0    = \m -> OmegaElement (compute m)
    | otherwise = error "Modulus only defined for zero"
        where compute m  = length (concat (take (m + 1) steps_list))
              steps_list = right_list (enum ss) phi step

-- Yield the right-most reduction of the Strip Lemma.
right_reduction :: RewriteSystem s v r
    => CReduction s v r -> Step s v -> CReduction s v r
right_reduction reduction step = CRCons (RCons ts ss) phi
    where ts    = construct_sequence terms
          ss    = construct_sequence steps
          phi   = right_modulus reduction step
          terms = rewrite_steps (final_term reduction) steps
          steps = right_steps reduction step

-- Strip Lemma for orthogonal systems with finite right-hand sides.
--
-- It is assumed the input reduction has at most length omega.
strip_lemma :: RewriteSystem s v r
    => r -> CReduction s v r -> Step s v -> (CReduction s v r, CReduction s v r)
strip_lemma _ reduction step
    | at_most_omega reduction = (bottom, right)
    | otherwise               = error "Reduction too long"
        where bottom = bottom_reduction reduction step
              right  = right_reduction reduction step
