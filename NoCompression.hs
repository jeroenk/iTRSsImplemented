{-# LANGUAGE FlexibleContexts #-}
{-
Copyright (C) 2011, 2012 Jeroen Ketema

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

-- This module defines non-compressible reductions.

module NoCompression (
    constructReduction
) where

import Term
import RuleAndSystem
import SystemOfNotation
import Reduction
import NoCompressionSystem

import Prelude
import Data.Array hiding (inRange)

-- Three simple helper functions for ordinals derived from ordLeq.
ordLess :: UnivalentSystem o
    => o -> o -> Bool
ordLess alpha beta = (alpha `ordLeq` beta) && not (beta `ordLeq` alpha)

ordEq :: UnivalentSystem o
    => o -> o -> Bool
ordEq alpha beta = (alpha `ordLeq` beta) && (beta `ordLeq` alpha)

ordMax :: UnivalentSystem o
    => o -> o -> o
ordMax alpha beta
    | alpha `ordLess` beta = beta
    | otherwise            = alpha

-- Construction of terms in which the symbol k does not occur.
constructTerm :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o -> o
       -> Term Sigma Var
constructTerm inSet geqLub nu alpha beta = replaceC $ term' 0 alpha beta
    where term' d delta gamma
              | inSet d && inRange = f s c t
              | geqLub d || empty  = c
              | otherwise          = h (term' (d + 1) delta gamma)
                      where kappa   = nu d
                            inRange = delta `ordLeq` kappa
                                          && kappa `ordLess` gamma
                            empty   = not (delta `ordLess` gamma)
                            s = term' (d + 1) delta kappa
                            t = addPrime $ term' (d + 1) (ordSucc kappa) gamma

-- The next two functions are helper functions to locate the next redex, given
-- that it is known the next redex uses either the f-rule or one of the k-rules.
findStepF :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> o) -> o -> o -> Step Sigma Var
findStepF inSet nu alpha beta = (findStepF' 0, rule_f)
    where findStepF' d
              | beta `ordEq` alpha
                  = error "No step with requested index"
              | inSet d && nu d `ordEq` beta
                  = []
              | otherwise
                  = 1 : findStepF' (d + 1)

findStepK :: Term Sigma Var -> (Bool, Step Sigma Var)
findStepK term = (f_next, (position, rule))
    where (f_next, position, rule) = findStepK' term
          findStepK' (Function symbol ts)
              | symbol == kFun = chooseRule $ ts!1
              | otherwise      = (f_n, 1 : p, r)
                  where (f_n, p, r) = findStepK' $ ts!1
          findStepK' (Variable _)
              = error "Illegal symbol in derived term"
          chooseRule (Function symbol _)
              | symbol == fFun' = (False, [], rule_k_f')
              | symbol == hFun' = (False, [], rule_k_h')
              | symbol == hFun  = (True,  [], rule_k_h)
              | otherwise    = error "Illegal symbol in derived term"
          chooseRule (Variable _)
              = error "Illegal symbol in derived term"

-- Yield the beta-th term and beta-th step along the reduction.
--
-- The function establishes (ordLimitPred beta) and starts reducing from there
-- onwards until a sufficient number of terms and steps have been found.
--
-- In case of a limit ordinal the only valid term can be one in which the
-- function symbol k does not occur. Hence, in this case only an f-step is
-- possible. After the f-step, only a finite number of k-steps can occur, which
-- occur at depth at least equal to the preceeding f-step. The final k-step of
-- such a finite series will employ the rule k(h(x)) -> h(x), after which an
-- f-step will again occur.
--
-- The penultimate argument of construct counts the number of f-steps that
-- have occurred since the start of the reduction. The final argument indicates
-- whether the next step is an f-step (True) or a k-step (False).
constructTermsAndSteps :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o -> o
       -> (Term Sigma Var, Step Sigma Var)
constructTermsAndSteps inSet geqLub nu alpha beta
    = construct initial beta' beta' True
        where initial = constructTerm inSet geqLub nu beta' alpha
              beta'   = ordLimitPred beta
              construct t delta gamma True
                  | delta `ordEq` beta = (t, f_step)
                  | otherwise          = construct t' delta' gamma' False
                      where f_step = findStepF inSet nu alpha gamma
                            t'     = rewriteStep t f_step
                            delta' = ordSucc delta
                            gamma' = ordSucc gamma
              construct t delta gamma False
                  | delta `ordEq` beta = (t, k_step)
                  | otherwise          = construct t' delta' gamma f_next
                      where (f_next, k_step) = findStepK t
                            t'     = rewriteStep t k_step
                            delta' = ordSucc delta

-- Yield the computable sequences of terms and steps of which the reduction is
-- composed.
terms :: (UnivalentSystem o, TermSequence Sigma Var ts o)
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o
       -> ((o -> Term Sigma Var) -> ts) -> ts
terms inSet geqLub nu alpha construct = construct $ fst . terms_and_steps
    where terms_and_steps = constructTermsAndSteps inSet geqLub nu alpha

steps :: (UnivalentSystem o, StepSequence Sigma Var SystemNonLL ss o)
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o
       -> ((o -> Step Sigma Var) -> ss) -> ss
steps inSet geqLub nu alpha construct = construct $ snd . terms_and_steps
    where terms_and_steps = constructTermsAndSteps inSet geqLub nu alpha

-- Yield the modulus of the reduction.
--
-- Given the ordinal and depth of interest, the function establishes the last
-- step that occurs at or above the given depth. The last two arguments of the
-- function (beta and depth) are the two arguments of the computed modulus.
constructModulus :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o
       -> Modulus o
constructModulus inSet geqLub nu alpha beta depth
    | valid     = countSteps inSet geqLub nu alpha delta
    | otherwise = error "Illegal modulus"
            where valid = ordKind beta /= SuccOrdinal
                  delta = finalStepF inSet nu beta' depth
                  beta' = if ordKind beta == ZeroOrdinal then alpha else beta

-- Count the number of steps using logic identical to constructTermsAndSteps.
countSteps :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o -> o -> o
countSteps inSet geqLub nu alpha beta
    = count initial beta' beta' True
        where initial = constructTerm inSet geqLub nu beta' alpha
              beta'   = ordLimitPred beta
              count t delta gamma True
                  | gamma `ordEq` beta = delta
                  | otherwise          = count t' delta' gamma' False
                      where f_step = findStepF inSet nu alpha gamma
                            t'     = rewriteStep t f_step
                            delta' = ordSucc delta
                            gamma' = ordSucc gamma
              count t delta gamma False
                  = count t' delta' gamma f_next
                      where (f_next, k_step) = findStepK t
                            t'     = rewriteStep t k_step
                            delta' = ordSucc delta

-- Yield the final f-step that occurs at depth d or above. The result is the
-- index of the step in the subsequence of f-steps of the constructed reduction.
finalStepF :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> o) -> o -> Integer -> o
finalStepF inSet nu alpha depth
    | null ordinals = ordZero
    | otherwise     = ordSucc $ maxOrd ordinals
        where ordinals  = [nu d | d <- [0..depth], inSet d, inRange d]
              inRange d = nu d `ordLeq` alpha
              maxOrd os = foldl ordMax (head os) (tail os)

-- Yield a non-compressible reduction.
--
-- Constructor functions for the term and step sequences are explicitly passed
-- in, as we do not know how long the constructed reduction will be.
constructReduction :: (UnivalentSystem o, TermSequence Sigma Var ts o,
            StepSequence Sigma Var SystemNonLL ss o)
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o
       -> ((o -> Term Sigma Var) -> ts) -> ((o -> Step Sigma Var) -> ss)
       -> CReduction Sigma Var SystemNonLL
constructReduction inSet geqLub nu alpha constructTermSeq constructStepSeq
    = CRCons (RCons ts ss) phi
        where ts  = terms inSet geqLub nu alpha constructTermSeq
              ss  = steps inSet geqLub nu alpha constructStepSeq
              phi = constructModulus inSet geqLub nu alpha
