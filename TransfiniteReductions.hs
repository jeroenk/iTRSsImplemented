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

-- This module defines computable reductions up to length omega.
--
-- Note that the final term of a reduction is not represented, but can be
-- computed in case a modulus of convergence is associated with the reduction;
-- the final term might be uncomputable otherwise. A consequence of all this
-- is that it suffices to use a system of notation for omega to express
-- convergent reductions of length omega (which have omega + 1 terms).
--
-- This module is incompatible with the OmegaReductions module.

module TransfiniteReductions (
    Reduction(RCons), Modulus,
    CReduction(CRCons),
    initial_term, final_term,
    needed_steps
) where

import SignatureAndVariables
import Terms
import PositionsAndSubterms
import RulesAndSystems
import SystemsOfNotation hiding (q)

-- Computable reductions are lists of terms and rewrite steps.
--
-- The number of terms is equal to 1 + alpha, where alpha is the number of
-- steps in the reduction.
--
-- The initial index of terms and steps is given explicitly (and is assumed to
-- be the same for both).
data (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
     => Reduction s v r o
    = RCons [Term s v] [Step s v] o

-- Helper function for show.
show_from :: (Show s, Show v,
              Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => (Reduction s v r o) -> o -> String
show_from (RCons ts _ _) a
    | indexof (to_int a) ts = show' a True True
    | otherwise             = error "Reduction without terms"
        where show' b True frst = fst_term ++ lst_terms
                  where n = to_int b
                        fst_term = (if frst then "" else " -> ") ++ show (ts!!n)
                        lst_terms = show' (suc b) is_index False
                        is_index = indexof (to_int (suc b)) ts
              show' _ False _   = ""
              indexof _ []     = False
              indexof 0 _      = True
              indexof n (_:ss) = indexof (n - 1) ss

instance (Show s, Show v,
          Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => Show (Reduction s v r o) where
    show s = show_from s (get_zero s)
        where get_zero (RCons _ _ z) = z

-- Moduli of convergence are functions from limit ordinals to functions from
-- natural numbers to ordinals (where the ordinals come from a designated
-- system of notation).
type Modulus o = o -> Int -> o

-- Computably convergent reductions are reductions with an associated modulus.
data (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o
    = CRCons (Reduction s v r o) (Modulus o)

-- A show function for computably convergent reductions.
--
-- The function detects whether more terms need to be shown based on the
-- modulus associated with the reduction. Note that this is not complete
-- termination detection, which cannot exist.
instance (Show s, Show v,
          Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => Show (CReduction s v r o) where
    show (CRCons (RCons [] _ _) _)   = error "Reduction without terms"
    show (CRCons (RCons ts _ z) phi) = show t ++ show' t z 0
        where t = ts!!(to_int z)
              show' s a d
                  | less_height s d = ""
                  | otherwise       = fst_steps ++ lst_steps
                      where fst_steps = show_steps fst_terms
                            lst_steps = show' s_new a_new (d + 1)
                            fst_terms = collect_terms (suc a) a_new
                            s_new
                                | null fst_terms = s
                                | otherwise      = last fst_terms
                            a_new
                                | (suc a) `leq` (phi z d) = phi z d
                                | otherwise               = a
              collect_terms a b
                  | a `leq` b = ts!!(to_int a) : collect_terms (suc a) b
                  | otherwise = []
              show_steps []     = ""
              show_steps (s:ss) = " -> " ++ show s ++ show_steps ss

-- Yield the initial term of a computably convergent reduction.
initial_term :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o -> Term s v
initial_term (CRCons (RCons ts _ z) _) = ts!!(to_int z)

-- Yield the final term of a computably convergent reduction.
final_term :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o -> Term s v
final_term (CRCons (RCons ts _ z) phi)
    = final_subterm [] (stable_terms 0)
    where final_subterm ps ss = construct_subterm top ps (tail ss)
                  where top = get_symbol (head ss) ps
          construct_subterm (FunctionSymbol f) ps ss = function_term f s
                  where a = arity f
                        s = [(i, final_subterm (ps ++ [i]) ss) | i <- [1..a]]
          construct_subterm (VariableSymbol x) _ _   = Variable x
          stable_terms d = ts!!n : stable_terms (d + 1)
              where n = to_int (phi z d)

-- Yield the needed steps of a reduction in case we are interested in the
-- positions up to a certain depth d in the final term of the reduction.
needed_steps :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o -> Int -> [Step s v]
needed_steps s@(CRCons (RCons _ ps z) phi) d
    = needed_steps' (pos_to_depth (final_term s) d) a (k a)
    where a = phi z d
          needed_steps' qs b SuccOrdinal
              | b `leq` z = []
              | otherwise = ps_new
                  where q@(q', _) = ps!!(to_int (p b))
                        qs_new = origins_across q qs
                        ps_new
                            | q' `elem` qs_new = ps' ++ [q]
                            | otherwise        = ps'
                        ps' = needed_steps' qs_new (p b) (k (p b))
          needed_steps' qs b LimitOrdinal
              | b `leq` z = []
              | otherwise = needed_steps' qs b' (k b')
                  where b' = phi b (maximum (map length qs))
          needed_steps' _ b ZeroOrdinal
              | b `leq` z = []
              | otherwise = error "Inconsistent system of notation"
