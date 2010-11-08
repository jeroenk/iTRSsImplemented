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
import PositionsAndSubterms
import RulesAndSystems
import OmegaReductions
import StripLemma

-- Compute which steps from a finite reduction (represented by its steps) are
-- needed for a certain prefix-closed set of positions of the final term of
-- the reduction. The function yields both the needed steps and the needed
-- positions from the initial term of the reduction.
needed_steps :: (Signature s, Variables v)
    => [Step s v] -> [NatString] -> ([Step s v], [NatString])
needed_steps [] qs             = ([], qs)
needed_steps (p@(p', _):ps) qs = (ps_new, qs_new)
    where (ps', qs') = needed_steps ps qs
          qs_new = origins_across qs' p
          ps_new
              | p' `elem` qs_new = p : ps'
              | otherwise        = ps'

-- Accumulate the needed steps of a reduction in case we are interested in the
-- positions up to a certain depth d in the final term of the reduction. The
-- function yields both the needed steps and the needed positions from the
-- initial term of the reduction.
accumulate :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Int -> ([Step s v], [NatString])
accumulate (CRConst (RConst ts ps) phi) d
    = needed_steps used_steps last_pos
    where used_steps = take (phi d) ps
          last_term  = last (rewrite_steps (head ts) used_steps)
          last_pos   = pos_to_depth last_term d

-- Compute the needed depth of the initial term of a reduction given a depth d
-- of the final term of the reduction.
needed_depth :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Int -> Int
needed_depth s d = maximum (map length (snd (accumulate s d)))

-- Yield the steps of a reduction needed given a depth d of the final term of
-- the reduction.
get_steps_to_depth :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Int -> [Step s v]
get_steps_to_depth s d = fst (accumulate s d)

-- Filter the steps from a reduction based on the steps that were found earlier.
-- To ensure proper concatenation the the steps are projected over the previous
-- steps using the Strip Lemma.
filter_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> [Step s v] -> Int -> [Step s v]
filter_steps _ s [] d     = get_steps_to_depth s d
filter_steps r s (p:ps) d = filter_steps r s' ps d
    where s' = fst (strip_lemma r s p)

-- The function confl_devel computes one side of the confluence diagram. The
-- steps of the reduction are returned as a list of lists of steps, where it
-- is ensured for the ith item in the list that all its steps occur at depth i.
confl_devel :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> CReduction s v r -> [[Step s v]]
confl_devel r (CRConst (RConst _ ps) phi_s) s
    = confl_devel' s ps 0 0 []
    where confl_devel' t qs d n prev -- project t over qs
              | steps_needed = steps_new:(confl_devel' t qs (d + 1) n prev_new)
              | otherwise    = confl_devel' t_new (tail qs) d (n + 1) prev
                    where steps_needed = (phi_s (needed_depth t d)) <= n
                          steps_new = filter_steps r t prev d
                          prev_new = prev ++ steps_new
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
    where terms = (rewrite_steps (final_term s) steps)
          steps = confl_steps r s t
          modulus = confl_modulus r s t

-- Confluence of orthogonal, non-collapsing rewrite systems with finite
-- right-hand sides.
confluence :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> (CReduction s v r, CReduction s v r)
              -> (CReduction s v r, CReduction s v r)
confluence r (s, t) = (confl_side r s t, confl_side r t s)
