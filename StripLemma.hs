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

-- This module implements the Strip Lemma for reductions up to length omega

module StripLemma (
    strip_lemma
) where

import SignatureAndVariables
import PositionsAndSubterms
import RulesAndSystems
import OmegaReductions

-- Yield a sequence of steps all employing the same rule r given a set of
-- parallel positions and a rule r
sequence_steps :: (Signature s, Variables v)
    => [NatString] -> RewriteRule s v -> [Step s v]
sequence_steps ps r = map (\p -> (p, r)) ps

bottom_develop :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> [[Step s v]]
bottom_develop (CRConst (RConst _ ps) _) (q, r)
    = steps ps [q]
    where steps [] _
              = []
          steps ((p, r') : ps) qs
              = bottom_steps : (steps ps descendants_qs)
              where down_steps     = sequence_steps qs r
                    descendants_p  = descendants [p] down_steps
                    bottom_steps   = sequence_steps descendants_p r'
                    descendants_qs = descendants qs [(p, r')]

bottom_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> [Step s v]
bottom_steps rs s
    = concat (bottom_develop rs s)

bottom_modulus :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> Modulus
bottom_modulus rs@(CRConst _ phi) s@(_, r) n
    = length (concat (take (phi (n + left_height r)) (bottom_develop rs s)))

bottom_reduction :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> CReduction s v r
bottom_reduction r s
    = CRConst (RConst terms steps) modulus
    where terms = (rewrite_steps (rewrite_step (initial_term r) s) steps)
          steps = bottom_steps r s
          modulus = bottom_modulus r s

right_develop :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> [[Step s v]]
right_develop (CRConst (RConst _ ps) phi) (q, r)
    = steps ps [q] 0 0
    where steps _ [] _ _
              = []
          steps ps qs m d
              = right_steps : (steps ps_left descendants_nd m_new (d + 1))
              where m_new          = max m (phi d)
                    ps_use         = take (m_new - m) ps
                    ps_left        = drop (m_new - m) ps
                    descendants_qs = descendants qs ps_use
                    descendants_d  = filter at_d descendants_qs
                        where at_d qs = (length qs) == d
                    descendants_nd = filter not_at_d descendants_qs
                        where not_at_d qs = (length qs) /= d
                    right_steps = sequence_steps descendants_d r

right_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> [Step s v]
right_steps rs s
    = concat (right_develop rs s)

right_modulus :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> Modulus
right_modulus rs s n
    = length (concat (take (n + 1) (right_develop rs s)))

right_reduction :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Step s v -> CReduction s v r
right_reduction r s
    = CRConst (RConst terms steps) modulus
    where terms = (rewrite_steps (final_term r) steps)
          steps = right_steps r s
          modulus = right_modulus r s

strip_lemma :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> Step s v -> (CReduction s v r, CReduction s v r)
strip_lemma _ r s = (bottom_reduction r s, right_reduction r s)
