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
    Reduction(RConst),
    Modulus,
    CReduction(CRConst),
    initial_term,
    final_term
) where

import MyShow
import SignatureAndVariables
import Terms
import PositionsAndSubterms
import RulesAndSystems
import SystemsOfNotation

-- Computable reductions are lists of terms and rewrite steps.
--
-- The number of terms is equal to 1 + alpha, where alpha is the number of
-- steps in the reduction.
--
-- The initial index of terms and steps is given explicitly (and is assumed to
-- be the same for both).
data (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
     => Reduction s v r o
    = RConst [Term s v] [Step s v] o

get_zero :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => (Reduction s v r o) -> o
get_zero (RConst _ _ z) = z

-- Helper function for show.
show_from :: (MyShow s, MyShow v,
              Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => (Reduction s v r o) -> o -> String
show_from (RConst ts _ _) a
    | indexof (to_int a) ts = show' a True True
    | otherwise             = error "Cannot show empty reductions"
        where show' b True frst = fst_term ++ lst_terms
                  where n = to_int b
                        fst_term = (if frst then "" else " -> ") ++ show (ts!!n)
                        lst_terms = show' (suc b) is_index False
                        is_index = indexof (to_int (suc b)) ts
              show' _ False _   = ""
              indexof _ []     = False
              indexof 0 _      = True
              indexof n (_:ss) = indexof (n - 1) ss

instance (MyShow s, MyShow v,
          Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => Show (Reduction s v r o) where
    show r = show_from r (get_zero r)

-- Moduli of convergence are functions from limit ordinals to functions from
-- natural numbers to ordinals (where the ordinals come from a designated
-- system of notation).
type Modulus o = o -> Int -> o

-- Computably convergent reductions are reductions with an associated modulus.
data (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o
    = CRConst (Reduction s v r o) (Modulus o)

-- A show function for computably convergent reductions.
--
-- The function detects whether more terms need to be shown based on the
-- modulus associated with the reduction.
instance (MyShow s, MyShow v,
          Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => Show (CReduction s v r o) where
    show (CRConst (RConst [] _ _) _)   = error "Cannot show empty reductions"
    show (CRConst (RConst ts _ z) phi) = show' z 0
        where show' a d
                  | less_height (ts!!n) d = show_t (ts!!n) (a `leq` z)
                  | otherwise             = fst_steps ++ lst_steps
                      where n = to_int a
                            fst_steps = show_steps a (phi z d)
                            lst_steps = show' (phi z d) (d + 1)
              show_steps a b
                  | a' `leq` b = show_t (ts!!n) (a `leq` z) ++ show_steps a' b
                  | otherwise = ""
                      where n = to_int a
                            a' = suc a
              show_t s True = show s
              show_t s False = " -> " ++ show s

-- Yield the initial term of a computably convergent reduction.
initial_term :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o -> Term s v
initial_term (CRConst (RConst ts _ z) _) = ts!!(to_int z)

-- Yield the final term of a computably convergent reduction.
final_term :: (Signature s, Variables v, RewriteSystem s v r, UnivalSystem o)
    => CReduction s v r o -> Term s v
final_term (CRConst (RConst ts _ z) phi)
    = final_subterm []
    where final_subterm ps
              = construct_subterm top ps
                  where a = phi z (length ps)
                        top = get_symbol (ts!!(to_int a)) ps
          construct_subterm (FunctionSymbol f) ps
              = function_term f ss
                  where a = arity f
                        ss = [(i, final_subterm (ps ++ [i])) | i <- [1..a]]
          construct_subterm (VariableSymbol x) _
              = Variable x
