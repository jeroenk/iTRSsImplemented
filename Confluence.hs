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

-- This module implements confluence for reductions up to length omega.

module Confluence (
    confluence
) where

import SignatureAndVariables
import RulesAndSystems
import OmegaReductions
import StripLemma

-- The function confl_devel computes one side of the confluence diagram. The
-- steps of the reduction are returned as a list of lists of steps, where it
-- is ensured for the ith item in the list that all its steps occur at depth i.
confl_devel :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> CReduction s v r -> [[Step s v]]
confl_devel r (CRConst (RConst _ ps) phi) s
    = confl_devel' s ps 0 0 []
    where confl_devel' t qs d n prev -- project t over qs
              | add_steps = steps_new:(confl_devel' t qs (d + 1) n total)
              | otherwise = confl_devel' t_new (tail qs) d (n + 1) prev
                    where add_steps = phi (needed_depth t d) <= n
                          steps_new = filter_steps prev total
                          total = needed_steps t d
                          t_new = fst (strip_lemma r t (head qs))

-- Concatenate the lists produced by confl_devel to obtain all steps.
confl_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> CReduction s v r -> [Step s v]
confl_steps r s t = concat (confl_devel r s t)

-- Compute the modulus using that the ith element of the list produced by
-- confl_devel contains all steps at depth i.
confl_modulus :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> CReduction s v r -> Modulus
confl_modulus r s t n = length (concat (take (n + 1) (confl_devel r s t)))

-- Yield either the right-most or bottom reduction of the confluence diagram.
confl_side :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> CReduction s v r -> CReduction s v r
confl_side r s t = CRConst (RConst terms steps) modulus
    where terms = rewrite_steps (final_term s) steps
          steps = confl_steps r s t
          modulus = confl_modulus r s t

-- Confluence of orthogonal, non-collapsing rewrite systems with finite
-- right-hand sides. The function yields (t/s, s/t).
confluence :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> (CReduction s v r, CReduction s v r)
              -> (CReduction s v r, CReduction s v r)
confluence r (s, t) = (confl_side r s t, confl_side r t s)
