{-
Copyright (C) 2010 Jeroen Ketema and Jakob Grue Simonsen

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
import PositionsAndSubterms
import RulesAndSystems
import OmegaReductions

-- Yield a sequence of steps all employing the same rule r given a set of
-- parallel positions and a rule r.
sequence_steps :: (Signature s, Variables v)
    => Positions -> RewriteRule s v -> [Step s v]
sequence_steps ps r = map (\p -> (p, r)) ps

-- The function bottom_develop computes developments of the bottom reduction
-- of the Strip Lemma. The computation proceeds from left to right and each
-- development is represented by a list of steps.
bottom_develop :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> [[Step s v]]
bottom_develop (CRConst (RConst _ ps) _) (q, r)
    = project ps [q]
    where project [] _
              = []
          project ((p', r'):ps') qs
              = new_steps : (project ps' descendants_qs)
              where down_steps = sequence_steps qs r
                    descendants_p = descendants [p'] down_steps
                    new_steps = sequence_steps descendants_p r'
                    descendants_qs = descendants qs [(p', r')]

-- Concatenate the developments of the bottom reduction to obtain all steps.
bottom_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> [Step s v]
bottom_steps r p
    = concat (bottom_develop r p)

-- Compute the modulus of the bottom reduction using the observation that in
-- the worse case a variable in the left-hand side of a rewrite rule is moved
-- all the way to the top of the right-hand side term.
bottom_modulus :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> Modulus
bottom_modulus r@(CRConst _ phi) s@(_, rule) n
    = length (concat (take (phi (n + left_height rule)) (bottom_develop r s)))

-- Yield the bottom reduction of the Strip Lemma.
bottom_reduction :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> CReduction s v r
bottom_reduction r s
    = CRConst (RConst terms steps) modulus
    where terms = (rewrite_steps (rewrite_step (initial_term r) s) steps)
          steps = bottom_steps r s
          modulus = bottom_modulus r s

-- The function right_develop computes the right-most reduction of the Strip
-- Lemma (which is a development). The steps of the reduction are returned as
-- a list of lists of steps, where it is ensured for the ith item in the list
-- that all its steps occur at depth i.
right_develop :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> [[Step s v]]
right_develop (CRConst (RConst _ ps) phi) (q, r)
    = project ps [q] 0 0
    where project _ [] _ _
              = []
          project ps' qs n d
              = new_steps : (project ps_left descendants_nd n' (d + 1))
              where n' = max n (phi d)
                    ps_use = take (n' - n) ps'
                    ps_left = drop (n' - n) ps'
                    descendants_qs = descendants qs ps_use
                    descendants_d  = filter at_d descendants_qs
                        where at_d xs = (length xs) == d
                    descendants_nd = filter not_at_d descendants_qs
                        where not_at_d xs = (length xs) /= d
                    new_steps = sequence_steps descendants_d r

-- Concatenate the lists of the right-most reduction to obtain all steps
right_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> [Step s v]
right_steps r p
    = concat (right_develop r p)

-- Compute the modulus of the right-most reduction using that the ith element
-- of the list produced by right_develop contains all steps at depth i.
right_modulus :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> Modulus
right_modulus r p n
    = length (concat (take (n + 1) (right_develop r p)))

-- Yield the right-most reduction of the Strip Lemma.
right_reduction :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> CReduction s v r
right_reduction r s
    = CRConst (RConst terms steps) modulus
    where terms = (rewrite_steps (final_term r) steps)
          steps = right_steps r s
          modulus = right_modulus r s

-- Strip Lemma for orthogonal systems with finite right-hand sides.
strip_lemma :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> Step s v -> (CReduction s v r, CReduction s v r)
strip_lemma _ r s = (bottom_reduction r s, right_reduction r s)
