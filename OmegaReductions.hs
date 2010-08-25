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

-- This module defines computable reductions up to length omega
--
-- Note that the final term of a reduction is not represented, but can be
-- computed in case a modulus of convergence is associated with the reduction;
-- the final term might be uncomputable otherwise.

module OmegaReductions (
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

-- Computable reductions are lists of terms and rewrite steps.
--
-- The number of terms is equal to 1 + n, where n is the number of steps in
-- the reduction.
data (Signature s, Variables v, RewriteSystem s v r) => Reduction s v r
    = RConst [Term s v] [Step s v]

instance (MyShow s, MyShow v, Signature s, Variables v, RewriteSystem s v r)
    => Show (Reduction s v r) where
    show (RConst [] _) = error "Cannot show empty reductions"
    show (RConst ss _) = show' ss True
        where show' [] _   = ""
              show' (s:ss) True  = show s ++ show' ss False
              show' (s:ss) False = " -> " ++ show s ++ show' ss False

-- Moduli of convergence are functions from natural numbers to natural numbers
type Modulus = Int -> Int

-- Computably convergent reductions are reductions with an associated modulus
data (Signature s, Variables v, RewriteSystem s v r) => CReduction s v r
    = CRConst (Reduction s v r) Modulus

-- A show function for computably convergent reductions.
--
-- The function detects whether more terms need to be shown based on the
-- modulus associated with the reduction.
instance (MyShow s, MyShow v, Signature s, Variables v, RewriteSystem s v r)
    => Show (CReduction s v r) where
    show (CRConst (RConst [] _) _)   = error "Cannot show empty reductions"
    show (CRConst (RConst ts _) phi) = show' ts 0 0
        where show' ts n d
                  | less_height (head ts) d = show_steps (take 1 ts) (n == 0)
                  | otherwise               = fst_steps ++ lst_steps
                      where n' = max n (phi d)
                            fst_steps = show_steps (take (n' - n) ts) (n == 0)
                            lst_steps = show' (drop (n' - n) ts) n' (d + 1)
              show_steps [] _     = ""
              show_steps (t:ts) True = show t ++ show_steps ts False
              show_steps (t:ts) False = " -> " ++ show t ++ show_steps ts False

-- Yield the initial term of a computably convergent reduction
initial_term :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Term s v
initial_term (CRConst (RConst (x:_) _) _) = x

-- Yield the final term of a computably convergent reduction
final_term :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Term s v
final_term (CRConst (RConst ts _) phi) = final_subterm [] 0 ts
    where final_subterm ps n ts
              = construct_subterm top ps n' ts'
                  where n' = max n (phi (length ps))
                        ts' = drop (n' - n) ts
                        top = get_symbol (head ts') ps
          construct_subterm (FunctionSymbol f) ps n ts
              = function_term f ss
                  where a = arity f
                        ss = [(i, final_subterm (ps ++ [i]) n ts) | i <- [1..a]]
          construct_subterm (VariableSymbol x) _ _ _
              = Variable x
