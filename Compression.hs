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

-- This module implements compression of transfinite reductions 

module Compression (
    compression
) where

import SignatureAndVariables
import PositionsAndSubterms
import RulesAndSystems
import SystemsOfNotation hiding (q)
import TransfiniteReductions

accumulate :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o -> Int -> [(Step s v, o)]
accumulate s@(CRConst (RConst _ ps z) phi) d
    = needed_steps (pos_to_depth (final_term s) d) a (k a)
    where a = phi z d
          needed_steps qs b SuccOrdinal
              | b `leq` z = []
              | otherwise = ss_new
                  where q@(q', _) = ps!!(to_int (p b))
                        qs_new = origins_across qs q
                        ss_new
                            | q' `elem` qs_new = ss' ++ [(q, p b)]
                            | otherwise        = ss'
                        ss' = needed_steps qs_new (p b) (k (p b))
          needed_steps qs b LimitOrdinal
              | b `leq` z = []
              | otherwise = needed_steps qs b' (k b')
                  where b' = phi b (maximum (map length qs))
          needed_steps _ b ZeroOrdinal
              | b `leq` z   = []
              | otherwise = error "Greater than zero but also equal or smaller"

filter_steps :: (Signature s, Variables v, UnivalSystem o)
    => [(Step s v, o)] -> [(Step s v, o)] -> [Step s v]
filter_steps prevs total = filter_steps' prevs total []
    where filter_steps' [] left ss
              =  ss ++ (map fst left)
          filter_steps' prev@((s, n):prevs') ((t, m):left') ss
              | (n `leq` m) && (m `leq` n)
                  = filter_steps' prevs' left' (project_over [s] ss)
              | otherwise
                  = filter_steps' prev left' (ss ++ [t])
          filter_steps' _ _ _
              = error "All previous steps should be included in total"
          project_over _ []
              = []
          project_over ss ((ps, r):qs)
              = ss_new ++ (project_over ss_new qs)
              where ps_add = descendants [ps] ss
                    ss_new = map (\q -> (q, r)) ps_add

compr_devel :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o -> [[Step s v]]
compr_devel s = (map fst initial) : (compr_devel' 1 initial)
    where initial = accumulate s 0
          compr_devel' d prevs = new_steps : (compr_devel' (d + 1) total)
                  where total = accumulate s d
                        new_steps = filter_steps prevs total

compr_steps :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o -> [Step s v]
compr_steps s = concat (compr_devel s)

compr_modulus :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o -> (Modulus Omega)
compr_modulus s (OmegaElement n)
    | n == 0    = \m -> OmegaElement (compute m)
    | otherwise = error "Modulus only defined for 0"
        where compute m = length (concat (take (m + 1) (compr_devel s)))

compression :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => r -> (CReduction s v r o) -> (CReduction s v r Omega)
compression _ s = CRConst (RConst terms steps zer) modulus
    where terms = (rewrite_steps (initial_term s) steps)
          steps = compr_steps s
          modulus = compr_modulus s
