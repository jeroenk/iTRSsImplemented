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

-- This module implements confluence for reductions up to length omega

module Confluence (
    confluence
) where

import SignatureAndVariables
import PositionsAndSubterms
import RulesAndSystems
import OmegaReductions
import StripLemma

accumulate :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Int -> ([Step s v], [NatString])
accumulate (CRConst (RConst ts ps) phi) d
    = needed_steps used_steps last_pos
    where used_steps = take (phi d) ps
          last_term  = last (rewrite_steps (head ts) used_steps)
          last_pos   = pos_to_depth last_term d
          needed_steps [] qs
              = ([], qs)
          needed_steps (p@(p', _):ps) qs
              = (ps_new, qs_new)
              where (ps', qs') = needed_steps ps qs
                    qs_new = origins_across qs' p
                    ps_new
                        | p' `elem` qs_new = p : ps'
                        | otherwise        = ps'

needed_depth :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Int -> Int
needed_depth s d = maximum (map length (snd (accumulate s d)))

get_steps_to_depth :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Int -> [Step s v]
get_steps_to_depth s d = fst (accumulate s d)

filter_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> [Step s v] -> Int -> [Step s v]
filter_steps r s [] d     = get_steps_to_depth s d
filter_steps r s (p:ps) d = filter_steps r s' ps d
    where s' = fst (strip_lemma r s p)

confl_devel :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> CReduction s v r -> [[Step s v]]
confl_devel r (CRConst (RConst _ ps) phi_s) t
    = confl_devel' t ps 0 0 []
    where confl_devel' t ps d n prev
              | steps_needed = steps_new:(confl_devel' t ps (d + 1) n prev_new)
              | otherwise    = confl_devel' t_new (tail ps) d (n + 1) prev
                    where steps_needed = (phi_s (needed_depth t d)) <= n
                          steps_new = filter_steps r t prev d
                          prev_new = prev ++ steps_new
                          t_new = fst (strip_lemma r t (head ps))

confl_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> CReduction s v r -> [Step s v]
confl_steps r s t = concat (confl_devel r s t)

confl_modulus :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> CReduction s v r -> Modulus
confl_modulus r s t n = length (concat (take (n + 1) (confl_devel r s t)))

confl_side :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> CReduction s v r -> CReduction s v r
confl_side r s t = CRConst (RConst terms steps) modulus
    where terms = (rewrite_steps (final_term s) steps)
          steps = confl_steps r s t
          modulus = confl_modulus r s t

confluence :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> (CReduction s v r, CReduction s v r)
              -> (CReduction s v r, CReduction s v r)
confluence r (s, t) = (confl_side r s t, confl_side r t s)
