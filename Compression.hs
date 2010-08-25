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
import SystemsOfNotation
import TransfiniteReductions

accumulate_essential :: (Signature s, Variables v, RewriteSystem s v r,
                         UnivalentSystem o)
    => CReduction s v r o -> Int -> [(Step s v, o)]
accumulate_essential s@(CRConst (RConst _ ps z) phi) d
    = needed_steps (pos_to_depth (final_term s) d) n (k n)
    where n = phi z d
          needed_steps qs n SuccOrdinal
              | leq n z   = []
              | otherwise = ss_new
                  where q@(q', _) = ps!!(to_int (p n))
                        qs_new = origins_across qs q
                        ss_new
                            | q' `elem` qs_new = ss' ++ [(q, p n)]
                            | otherwise        = ss'
                        ss' = needed_steps qs_new (p n) (k (p n))
          needed_steps qs n LimitOrdinal
              | leq n z   = []
              | otherwise = needed_steps qs n' (k n')
                  where n' = phi n (maximum (map length qs))
          needed_steps qs n ZeroOrdinal
              | leq n z   = []
              | otherwise = error("Greater than 0 while being equal or smaller")

filter_steps :: (Signature s, Variables v, UnivalentSystem o)
    => [(Step s v, o)] -> [(Step s v, o)] -> [Step s v]
filter_steps prev total = filter_steps' prev total []
    where filter_steps' [] left ss =  ss ++ (map fst left)
          filter_steps' prev@((s, n):prev') ((t, m):left') ss
              | (leq n m) && (leq m n)
                  = filter_steps' prev' left' (project_over [s] ss)
              | otherwise
                  = filter_steps' prev left' (ss ++ [t])
          project_over ss []
              = []
          project_over ss ((ps, r):qs)
              = ss_new ++ (project_over ss_new qs)
              where ps_add = descendants [ps] ss
                    ss_new = map (\p -> (p, r)) ps_add

compr_devel :: (Signature s, Variables v, RewriteSystem s v r,
                UnivalentSystem o)
    => CReduction s v r o -> [[Step s v]]
compr_devel s = (map fst initial) : (compr_devel' 1 initial)
    where initial
              = accumulate_essential s 0
          compr_devel' d prev
              = new : (compr_devel' (succ d) total)
                  where total = accumulate_essential s d
                        new   = filter_steps prev total

compr_steps :: (Signature s, Variables v, RewriteSystem s v r,
                UnivalentSystem o)
    => CReduction s v r o -> [Step s v]
compr_steps s = concat (compr_devel s)

compr_modulus :: (Signature s, Variables v, RewriteSystem s v r,
                  UnivalentSystem o)
    => CReduction s v r o -> (Modulus Omega)
compr_modulus s (OmegaElement n)
    | n == 0
        = (\m -> OmegaElement (length (concat (take (succ m) (compr_devel s)))))
    | otherwise
        = error("Modulus only defined for 0")

compression :: (Signature s, Variables v, RewriteSystem s v r,
                UnivalentSystem o)
    => r -> (CReduction s v r o) -> (CReduction s v r Omega)
compression r s = CRConst reduction modulus
    where reduction = RConst terms steps zer
          terms = (rewrite_steps (initial_term s) steps)
          steps = compr_steps s
          modulus = compr_modulus s
