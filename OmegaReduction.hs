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
-- the final term might be uncomputable otherwise.

module OmegaReduction (
    Reduction(RCons), Modulus,
    CReduction(CRCons),
    get_terms, get_modulus,
    initial_term, final_term,
    needed_depth, needed_steps
) where

import SignatureAndVariables
import Term
import PositionAndSubterm
import RuleAndSystem

-- Computable reductions are lists of terms and rewrite steps.
--
-- The number of terms is equal to 1 + n, where n is the number of steps in
-- the reduction.
data (Signature s, Variables v, RewriteSystem s v r) => Reduction s v r
    = RCons [Term s v] [Step s v]

instance (Show s, Show v, Signature s, Variables v, RewriteSystem s v r)
    => Show (Reduction s v r) where
    show (RCons [] _) = error "Reduction without terms"
    show (RCons ts _) = show' ts True
        where show' [] _   = ""
              show' (s:ss) True  = show s ++ show' ss False
              show' (s:ss) False = " -> " ++ show s ++ show' ss False

-- Moduli of convergence are functions from natural numbers to natural numbers.
type Modulus = Int -> Int

-- Computably convergent reductions are reductions with an associated modulus.
data (Signature s, Variables v, RewriteSystem s v r) => CReduction s v r
    = CRCons (Reduction s v r) Modulus

-- A show function for computably convergent reductions.
instance (Show s, Show v, Signature s, Variables v, RewriteSystem s v r)
    => Show (CReduction s v r) where
    show s = show_terms (get_terms s) True
        where show_terms [] _         = ""
              show_terms (t:ts) True  = show t ++ show_terms ts False
              show_terms (t:ts) False = " -> " ++ show t ++ show_terms ts False

-- Get the terms that make up a computably convergent reductions.
--
-- The function detects whether more terms need to be shown based on the
-- modulus associated with the reduction. Note that this is not complete
-- termination detection, which cannot exist.
get_terms :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> [Term s v]
get_terms (CRCons (RCons [] _) _)       = error "Reduction without terms"
get_terms (CRCons (RCons (t:ts) _) phi) = t : get_terms' t ts 0 0
    where get_terms' s ss n d
              | less_height s d = []
              | otherwise       = fst_terms ++ lst_terms
                  where n' = max n (phi d)
                        fst_terms = take (n' - n) ss
                        lst_terms = get_terms' s_new rem_terms n' (d + 1)
                        rem_terms = drop (n' - n) ss
                        s_new
                            | null fst_terms = s
                            | otherwise      = last fst_terms

-- Get the modulus of the reduction
get_modulus :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Modulus
get_modulus (CRCons _ phi) = phi

-- Yield the initial term of a computably convergent reduction.
initial_term :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Term s v
initial_term (CRCons (RCons [] _) _)    = error "Reduction without terms"
initial_term (CRCons (RCons (x:_) _) _) = x

-- Yield the final term of a computably convergent reduction.
final_term :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Term s v
final_term (CRCons (RCons ts _) phi) = final_subterm [] (stable_terms 0 0 ts)
    where final_subterm p ss = construct_subterm top p (tail ss)
                  where top = get_symbol (head ss) p
          construct_subterm (FunctionSymbol f) p ss = function_term f s
                  where s = [final_subterm (p ++ [i]) ss | i <- [1..arity f]]
          construct_subterm (VariableSymbol x) _ _  = Variable x
          stable_terms d n ss = head ss' : stable_terms (d + 1) n' ss'
              where n'  = max n (phi d)
                    ss' = drop (n' - n) ss

-- Compute which steps from a finite reduction (represented by its steps) are
-- needed for a certain prefix-closed set of positions of the final term of
-- the reduction. The function yields both the needed steps and the needed
-- positions from the initial term of the reduction.
needed_steps' :: (Signature s, Variables v)
    => [Step s v] -> Positions -> ([Step s v], Positions)
needed_steps' [] qs             = ([], qs)
needed_steps' (p@(p', _):ps) qs = (ps_new, qs_new)
    where (ps', qs') = needed_steps' ps qs
          qs_new = origins_across p qs'
          ps_new
              | p' `elem` qs_new = p : ps'
              | otherwise        = ps'

-- Accumulate the needed steps of a reduction in case we are interested in the
-- positions up to a certain depth d in the final term of the reduction. The
-- function yields both the needed steps and the needed positions from the
-- initial term of the reduction.
accumulate :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Int -> ([Step s v], Positions)
accumulate (CRCons (RCons ts ps) phi) d
    = needed_steps' used_steps last_pos
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
needed_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Int -> [Step s v]
needed_steps s d = fst (accumulate s d)
