{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
             UndecidableInstances, ExistentialQuantification #-}
{-
Copyright (C) 2010, 2011 Jeroen Ketema and Jakob Grue Simonsen

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

-- This module defines computable reductions of arbitrary computable ordinal
-- length.
--
-- The final term of a reduction is not represented in case the reduction is
-- of limit ordinal length. The final term can be computed in case a modulus of
-- convergence is associated with the reduction; the term may be uncomputable
-- otherwise. As consequence, it for example suffices to employ a system of
-- notation for omega to denote convergent reductions of length omega (which
-- have omega + 1 terms).

module Reduction (
    TermSequence, StepSequence,
    Reduction(RCons), Modulus,
    CReduction(CRCons),
    get_terms, at_most_omega,
    initial_term, final_term,
    needed_positions, needed_steps
) where

import SignatureAndVariables
import Term
import PositionAndSubterm
import RuleAndSystem
import SystemOfNotation

-- Computable sequences of terms and rewrite steps are computable sequences.
class (Signature s, Variables v, ComputableSequence o (Term s v) ts)
    => TermSequence s v ts o

class (RewriteSystem s v r, ComputableSequence o (Step s v) ss)
    => StepSequence s v r ss o

instance (Signature s, Variables v, ComputableSequence o (Term s v) ts)
    => TermSequence s v ts o

instance (RewriteSystem s v r, ComputableSequence o (Step s v) ss)
    => StepSequence s v r ss o

-- Computable reductions are computable sequences of terms and rewrite steps.
data (TermSequence s v ts o, StepSequence s v r ss o) => Reduction s v r ts ss o
    = RCons ts ss

-- Helper function for show.
show_from :: (Show s, Show v, TermSequence s v ts o, StepSequence s v r ss o)
    => Reduction s v r ts ss o -> o -> String
show_from (RCons ts _) alpha = show' (get_from ts alpha) True
    where show' [] True      = error "Reduction without terms"
          show' [] False     = ""
          show' (term:terms) start = fst_term ++ lst_terms
                  where fst_term  = (if start then "" else " -> ") ++ show term
                        lst_terms = show' terms False

instance (Show s, Show v, TermSequence s v ts o, StepSequence s v r ss o)
    => Show (Reduction s v r ts ss o) where
    show reduction = show_from reduction ord_zero

-- Moduli of convergence are functions from limit ordinals to functions from
-- natural numbers to ordinals (where the ordinals come from a designated
-- system of notation).
type Modulus o = o -> Integer -> o

-- Computably convergent reductions are reductions with an associated modulus.
data RewriteSystem s v r => CReduction s v r
    = forall o ts ss. (TermSequence s v ts o, StepSequence s v r ss o)
          => CRCons (Reduction s v r ts ss o) (Modulus o)

-- A show function for computably convergent reductions.
instance (Show s, Show v, RewriteSystem s v r)
    => Show (CReduction s v r) where
    show reduction = show_terms (get_terms reduction) ""
        where show_terms [] _      = ""
              show_terms (x:xs) c  = c ++ show x ++ show_terms xs " -> "

-- Get the terms of a computably convergent reduction.
--
-- This is a helper function for show.
--
-- The function detects whether more terms exist based on (a) the height of the
-- last term computed and (b) the modulus associated with the reduction. Note
-- that this is not complete termination detection, which cannot exist.
get_terms :: RewriteSystem s v r
    => CReduction s v r -> [Term s v]
get_terms (CRCons (RCons ts _) phi) = fst_term : lst_terms
    where terms     = get_from ts ord_zero
          fst_term  = head terms
          lst_terms = get_terms' fst_term (tail terms) ord_zero 0
          get_terms' x xs a d
              | less_height x d      = []
              | modulus `ord_leq` a  = get_terms' x xs a (d + 1)
              | otherwise            = y : get_terms' y ys (ord_succ a) d
                  where modulus = phi ord_zero d
                        y:ys    = xs

-- May yield True in case the computably convergent reduction has length at most
-- omega.
at_most_omega :: RewriteSystem s v r
    => CReduction s v r -> Bool
at_most_omega (CRCons (RCons ts _) _) = omega_dom ts

-- Yield the initial term of a computably convergent reduction.
initial_term :: RewriteSystem s v r
    => CReduction s v r -> Term s v
initial_term (CRCons (RCons ts _) _) = get_elem ts ord_zero

-- Yield the final term of a computably convergent reduction.
final_term :: RewriteSystem s v r
    => CReduction s v r -> Term s v
final_term (CRCons (RCons ts _) phi) = final_term' (stable_terms ts phi)
    where final_term' xs
              = construct_term (root_symbol (head xs)) (tail xs)
          construct_term (FunctionSymbol f) xs
              = function_term f [final_term' (subterms i) | i <- [1..arity f]]
                  where subterms i = map (\x -> subterm x [i]) xs
          construct_term (VariableSymbol x) _
              = Variable x

-- Yield a list of terms that are stable with respect to a given modulus
--
-- This is a helper function for final_term.
stable_terms :: TermSequence s v ts o
    => ts -> Modulus o -> [Term s v]
stable_terms ts phi = select ts f (0, Just (phi ord_zero 0))
    where f (depth, alpha)
              | modulus `ord_leq` alpha = (depth + 1, Just alpha)
              | otherwise               = (depth + 1, Just modulus)
                  where modulus = phi ord_zero (depth + 1)

-- Compute which steps from a finite reduction (represented by its steps) are
-- needed for a certain prefix-closed set of positions of the final term of
-- the reduction. The function also yields the needed positions of the initial
-- term of the reduction.
acc_finite :: (Signature s, Variables v)
    => [Step s v] -> Positions -> ([Step s v], Positions)
acc_finite [] ps                  = ([], ps)
acc_finite (step@(p, _):steps) ps = (steps_new, ps_new)
    where (steps', ps') = acc_finite steps ps
          ps_new        = origins [step] ps'
          steps_new
              | p `elem` ps_new = step : steps'
              | otherwise       = steps'

-- Wrapper for acc_finite, which deals with already accumulated steps.
acc_wrap :: (Signature s, Variables v)
    => [Step s v] -> ([Step s v], Positions) -> ([Step s v], Positions)
acc_wrap steps (steps_acc, ps) = (steps_new ++ steps_acc, ps_new)
    where (steps_new, ps_new) = acc_finite steps ps

-- Compute the needed steps of a reduction for all positions up to a given depth
-- d of the final term of the reduction. The function also yields the needed
-- positions of the initial term of the reduction.
accumulate :: RewriteSystem s v r
    => CReduction s v r -> Positions -> ([Step s v], Positions)
accumulate (CRCons (RCons _ ss) phi) ps
    = accumulate' ([], ps) limit modulus (ord_kind limit)
        where modulus   = phi ord_zero (maximum (map pos_len ps))
              limit     = ord_lim_pred modulus
              accumulate' sp alpha beta ZeroOrdinal
                  = acc_wrap (get_range alpha beta) sp
              accumulate' _ _ _ SuccOrdinal
                  = error "Inconsistent system of notation"
              accumulate' sp alpha beta LimitOrdinal
                  = accumulate' sp' alpha' beta' (ord_kind alpha')
                      where sp'    = acc_wrap (get_range alpha beta) sp
                            alpha' = ord_lim_pred beta'
                            beta'  = phi alpha (maximum (map pos_len (snd sp')))
              get_range alpha beta = select ss f ((), Just alpha)
                  where f (_, kappa)
                            | beta `ord_leq` kappa_succ = ((), Nothing)
                            | otherwise                 = ((), Just kappa_succ)
                            where kappa_succ = ord_succ kappa

-- Yield the needed positions of the initial term of a reduction for a
-- prefix-closed subset of positions of the final term of the reduction.
needed_positions :: RewriteSystem s v r
    => CReduction s v r -> Positions -> Positions
needed_positions reduction positions = snd (accumulate reduction positions)

-- Yield the needed steps of a reduction for a prefix-closed subset of the
-- final term of the reduction.
needed_steps :: RewriteSystem s v r
    => CReduction s v r -> Positions -> [Step s v]
needed_steps reduction positions = fst (accumulate reduction positions)
