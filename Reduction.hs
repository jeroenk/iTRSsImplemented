{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs,
             MultiParamTypeClasses, UndecidableInstances #-}
{-
Copyright (C) 2010, 2011, 2012 Jeroen Ketema and Jakob Grue Simonsen

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
-- otherwise. As consequence, it suffices to employ a system of notation for
-- omega to denote a reduction of length omega (which has omega + 1 terms).

module Reduction (
    TermSequence, StepSequence,
    FiniteReduction, Reduction(RCons),
    Modulus, CReduction(CRCons),
    getTerms, atMostLengthOmega,
    initialTerm, finalTerm,
    origins, descendants,
    neededSteps, neededReduction
) where

import SignatureAndVariables
import Term
import PositionAndSubterm
import RuleAndSystem
import SystemOfNotation

import Prelude
import Data.List

-- Computable sequences of terms and rewrite steps are computable sequences.
class (Signature s, Variables v, ComputableSequence o (Term s v) ts)
    => TermSequence s v ts o

class (RewriteSystem s v r, ComputableSequence o (Step s v) ss)
    => StepSequence s v r ss o

instance (Signature s, Variables v, ComputableSequence o (Term s v) ts)
    => TermSequence s v ts o

instance (RewriteSystem s v r, ComputableSequence o (Step s v) ss)
    => StepSequence s v r ss o

-- Finite reductions are pairs consisting of a finite sequence of terms and a
-- finite sequence of rewrite steps.
type FiniteReduction s v r = ([Term s v], [Step s v])

-- Strongly convergent computable reductions are pairs consisting of a
-- computable sequence of terms and computable sequence of rewrite steps over
-- an ordinal o.
data Reduction s v r ts ss o where
    RCons :: (TermSequence s v ts o, StepSequence s v r ss o)
                 => ts -> ss -> Reduction s v r ts ss o

instance (Show s, Show v, TermSequence s v ts o, StepSequence s v r ss o)
    => Show (Reduction s v r ts ss o) where
    show reduction = showFrom reduction ordZero

-- Helper function for show above.
showFrom :: (Show s, Show v, TermSequence s v ts o, StepSequence s v r ss o)
    => Reduction s v r ts ss o -> o -> String
showFrom (RCons ts _) alpha = show' (getFrom ts alpha) True
    where show' [] True     = error "Reduction without terms"
          show' [] False    = ""
          show' (term:terms) start = fst_term ++ lst_terms
                  where fst_term  = (if start then "" else " -> ") ++ show term
                        lst_terms = show' terms False

-- Moduli of convergence are functions from limit ordinals to functions from
-- natural numbers to ordinals (where the ordinals come from a designated
-- system of notation).
type Modulus o = o -> Integer -> o

-- Computably strongly convergent reductions are strongly convergent reductions
-- with a modulus. Observe that the ordinal used to define such a reduction is
-- existentially quantified over and, hence, hidden.
data CReduction s v r where
    CRCons :: (RewriteSystem s v r,
                   TermSequence s v ts o, StepSequence s v r ss o)
                   => Reduction s v r ts ss o -> Modulus o -> CReduction s v r

-- A show function for computably strongly convergent reductions.
instance (Show s, Show v, RewriteSystem s v r)
    => Show (CReduction s v r) where
    show reduction = showSteps (getTerms reduction) ""
        where showSteps [] _      = ""
              showSteps (x:xs) c  = c ++ show x ++ showSteps xs " -> "

-- Get the terms of a computably strongly convergent reduction.
--
-- The function detects whether more terms exist based on (a) the height of the
-- last term computed and (b) the modulus associated with the reduction. Note
-- that this is not complete termination detection, which cannot exist.
getTerms :: RewriteSystem s v r
    => CReduction s v r -> [Term s v]
getTerms (CRCons (RCons ts _) phi) = fst_term : lst_terms
    where terms     = getFrom ts ordZero
          fst_term  = head terms
          lst_terms = getTerms' fst_term (tail terms) ordZero 0
          getTerms' x xs a d
              | x `heightLess` d    = []
              | modulus `ordLeq` a  = getTerms' x xs a (d + 1)
              | otherwise           = y : getTerms' y ys (ordSucc a) d
                  where modulus = phi ordZero d
                        y:ys    = xs

-- May yield True in case the computably strongly convergent reduction has
-- length at most omega.
atMostLengthOmega :: RewriteSystem s v r
    => CReduction s v r -> Bool
atMostLengthOmega (CRCons (RCons ts _) _) = hasOmegaDomain ts

-- Yield the initial term of a computably strongly convergent reduction.
initialTerm :: RewriteSystem s v r
    => CReduction s v r -> Term s v
initialTerm (CRCons (RCons ts _) _) = getElem ts ordZero

-- Yield a list of terms that are stable with respect to a given modulus.
--
-- This is a helper function for finalTerm.
stableTerms :: TermSequence s v ts o
    => ts -> Modulus o -> [Term s v]
stableTerms ts phi = select ts f (0, Just (phi ordZero 0))
    where f (depth, alpha)
              | modulus `ordLeq` alpha = (depth + 1, Just alpha)
              | otherwise              = (depth + 1, Just modulus)
                  where modulus = phi ordZero (depth + 1)

-- Yield the final term of a computably strongly convergent reduction.
finalTerm :: RewriteSystem s v r
    => CReduction s v r -> Term s v
finalTerm (CRCons (RCons ts _) phi) = finalTerm' $ stableTerms ts phi
    where finalTerm' xs
              = constructTerm (rootSymbol (head xs)) (tail xs)
          constructTerm (FunctionSymbol f) xs
              = functionTerm f [finalTerm' (subterms i) | i <- [1..arity f]]
                  where subterms i = map (\x -> subterm x [i]) xs
          constructTerm (VariableSymbol x) _
              = Variable x

-- Compute the origins and needed steps of a reduction for a finite, subset of
-- positions of the final term of a finite reduction (represented by its steps).
-- The yielded needed steps are only sensible in case the subset of positions
-- is prefix-closed.
accumulateFinite :: (Signature s, Variables v)
    => [Step s v] -> Positions -> (Positions, [Step s v])
accumulateFinite [] ps                  = (ps, [])
accumulateFinite (step@(p, _):steps) ps = (ps_new, steps_new)
    where (ps', steps') = accumulateFinite steps ps
          ps_new        = originsAcrossStep step ps'
          steps_new
              | p `elem` ps_new = step : steps'
              | otherwise       = steps'

-- Wrapper for accumulateFinite, which deals with accumulated needed steps.
accumulateWrap :: (Signature s, Variables v)
    => [Step s v] -> (Positions, [Step s v]) -> (Positions, [Step s v])
accumulateWrap steps (ps, steps_acc) = (ps_new, steps_new ++ steps_acc)
    where (ps_new, steps_new) = accumulateFinite steps ps

-- Compute the origins and needed steps of a reduction for a finite, subset of
-- positions of the final term of a reduction. The yielded needed steps are
-- only sensible in case the subset of positions is prefix-closed.
accumulate :: RewriteSystem s v r
    => CReduction s v r -> Positions -> (Positions, [Step s v])
accumulate (CRCons (RCons _ ss) phi) ps
    = accumulate' (ps, []) (ordKind limit) limit modulus
        where modulus = phi ordZero $ maximumLength ps
              limit   = ordLimitPred modulus
              accumulate' sp ZeroOrdinal alpha beta
                  = accumulateWrap (getRange alpha beta) sp
              accumulate' _ SuccOrdinal _ _
                  = error "Inconsistent system of notation"
              accumulate' sp LimitOrdinal alpha beta
                  = accumulate' sp' (ordKind alpha') alpha' beta'
                      where sp'    = accumulateWrap (getRange alpha beta) sp
                            alpha' = ordLimitPred beta'
                            beta'  = phi alpha $ maximumLength (fst sp')
              maximumLength qs    = maximum $ map positionLength qs
              getRange alpha beta = select ss f $ f' ((), alpha)
                  where f  (_, kappa)
                            = f' ((), ordSucc kappa)
                        f' (_, kappa)
                            | beta `ordLeq` kappa = ((), Nothing)
                            | otherwise           = ((), Just kappa)

-- Yield the origins in the initial term s of a reduction s ->> t for a finite
-- subset of positions of the final term t of s ->> t.
origins :: RewriteSystem s v r
    => CReduction s v r -> Positions -> Positions
origins reduction positions = fst (accumulate reduction positions)

-- Yield the needed steps of a reduction s ->> t for a finite, prefix-closed
-- subset of positions of the final term t of s ->> t.
neededSteps :: RewriteSystem s v r
    => CReduction s v r -> Positions -> [Step s v]
neededSteps reduction positions = snd (accumulate reduction positions)

-- Yield the descendants in the final term t of a reduction s ->> t for a
-- position function of the initial term s of s ->> t.
descendants :: RewriteSystem s v r
    => CReduction s v r -> PositionFunction -> PositionFunction
descendants reduction pf = map descendants' [0..]
    where descendants' d = genericIndex pf_d d
              where final = finalTerm reduction
                    pf_d  = descendantsAcrossSteps steps pf
                    steps = neededSteps reduction ps_d
                    ps_d  = posToDepth final d

-- Yield the needed reduction of a reduction s ->> t for a finite, prefix-closed
-- subset of positions of the final term of s ->> t.
neededReduction :: RewriteSystem s v r
    => CReduction s v r -> Positions -> FiniteReduction s v r
neededReduction reduction positions = (terms , steps)
    where steps = neededSteps reduction positions
          terms = rewriteSteps (initialTerm reduction) steps
