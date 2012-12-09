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

-- This module defines non-compressible reductions for a system with a
-- non-left-linear rule.

module NoCompression (
    Sigma, Var,
    SystemNonLL, systemNonLL,
    constructReduction
) where

import SignatureAndVariables
import Term
import RuleAndSystem
import SystemOfNotation
import Reduction

import Prelude
import Data.Array hiding (inRange)

-- Signature and variables.
data Sigma = SigmaCons String
data Var   = VarCons Char

instance Signature Sigma where
    arity (SigmaCons "c")  = 0
    arity (SigmaCons "f")  = 3
    arity (SigmaCons "f'") = 3
    arity (SigmaCons "h")  = 1
    arity (SigmaCons "h'") = 1
    arity (SigmaCons "k")  = 1
    arity  _ = error "Not a function symbol"

instance Eq Sigma where
    (SigmaCons s0) == (SigmaCons s1) = s0 == s1

instance Show Sigma where
    show (SigmaCons s) = s

instance Variables Var

instance Eq Var where
    (VarCons v0) == (VarCons v1) = v0 == v1

instance Show Var where
    show (VarCons v) = [v]

-- Some wrappers for variables and function symbols.
x :: Var
x = VarCons 'x'

y :: Var
y = VarCons 'y'

z :: Var
z = VarCons 'z'

c :: Sigma
c = SigmaCons "c"

f :: Sigma
f = SigmaCons "f"

f' :: Sigma
f' = SigmaCons "f'"

h :: Sigma
h = SigmaCons "h"

h' :: Sigma
h' = SigmaCons "h'"

k :: Sigma
k = SigmaCons "k"

-- Terms employed in the rewrite rules of the non-left-linear system.
f_x_x_y :: Term Sigma Var
f_x_x_y = functionTerm f [Variable x, Variable x, Variable y]

h_k_y :: Term Sigma Var
h_k_y = functionTerm h [k_y]
    where k_y = functionTerm k [Variable y]

k_f'_x_y_z :: Term Sigma Var
k_f'_x_y_z = functionTerm k [f'_x_y_z]
    where f'_x_y_z = functionTerm f' [Variable x, Variable y, Variable z]

f_k_x_y_z :: Term Sigma Var
f_k_x_y_z = functionTerm f [k_x, Variable y, Variable z]
    where k_x = functionTerm k [Variable x]

k_h'_x :: Term Sigma Var
k_h'_x = functionTerm k [h'_x]
    where h'_x = functionTerm h' [Variable x]

h_k_x :: Term Sigma Var
h_k_x = functionTerm h [k_x]
    where k_x = functionTerm k [Variable x]

k_h_x :: Term Sigma Var
k_h_x = functionTerm k [h_x]

h_x :: Term Sigma Var
h_x = functionTerm h [Variable x]

h_omega :: Term Sigma Var
h_omega = functionTerm h [h_omega]

rule_f :: RewriteRule Sigma Var
rule_f = Rule f_x_x_y h_k_y

rule_k_f' :: RewriteRule Sigma Var
rule_k_f' = Rule k_f'_x_y_z f_k_x_y_z

rule_k_h' :: RewriteRule Sigma Var
rule_k_h' = Rule k_h'_x h_k_x

rule_k_h :: RewriteRule Sigma Var
rule_k_h = Rule k_h_x h_x

-- The non-left-linear rewrite system.
--
-- The system has four rules:
--
--    f(x, x, y)     -> h(k(y))
--    k(f'(x, y, z)) -> f(k(x), y, z)
--    k(h'(x))       -> h(k(x))
--    k(h(x))        -> h(x)
--
type SystemNonLL = System Sigma Var

systemNonLL :: SystemNonLL
systemNonLL = SystemCons [rule_f, rule_k_f', rule_k_h', rule_k_h]

-- Two helper functions for ordinals derived from ordLeq.
ordLess :: UnivalentSystem o
    => o -> o -> Bool
ordLess alpha beta = (alpha `ordLeq` beta) && not (beta `ordLeq` alpha)

ordEq :: UnivalentSystem o
    => o -> o -> Bool
ordEq alpha beta = (alpha `ordLeq` beta) && (beta `ordLeq` alpha)

-- Construction of terms in which the symbol k does not occur.
constructTerm :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o -> o
       -> Term Sigma Var
constructTerm inSet geqLub nu alpha beta = replaceC (term' 0 alpha beta)
    where term' d delta gamma
              | inSet d && inRange
                  = functionTerm f [t_1, t_2, t_3]
              | geqLub d || emptyRange
                  = constant c
              | otherwise
                  = functionTerm h [term' (d + 1) delta gamma]
                      where kappa      = nu d
                            succ_kappa = ordSucc kappa
                            inRange    = delta `ordLeq` kappa
                                             && kappa `ordLess` gamma
                            emptyRange = not (delta `ordLess` gamma)
                            t_1 = term' (d + 1) delta kappa
                            t_2 = constant c
                            t_3 = rename (term' (d + 1) succ_kappa gamma)

rename :: Term Sigma Var -> Term Sigma Var
rename (Function symbol ts)
    | symbol == f = Function f' (ts // [(1, rename (ts!1))])
    | symbol == h = Function h' (ts // [(1, rename (ts!1))])
    | symbol == c = constant c
    | otherwise   = error "Illegal symbol in constructed term"
rename _
    = error "Illegal symbol in constructed term"

replaceC :: Term Sigma Var -> Term Sigma Var
replaceC (Function symbol ts)
    | symbol == c = h_omega
    | otherwise   = Function symbol (fmap replaceC ts)
replaceC (Variable v)
    = Variable v

-- The next two functions are helper functions to locate the next redex, given
-- it is known the next redex either employs the f-rule or one of the k-rules.
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
              | symbol == k = establishRule (ts!1)
              | otherwise   = (f_n, 1 : p, r)
                  where (f_n, p, r) = findStepK' (ts!1)
          findStepK' (Variable _)
              = error "Illegal symbol in derived term"
          establishRule (Function symbol _)
              | symbol == f' = (False, [], rule_k_f')
              | symbol == h' = (False, [], rule_k_h')
              | symbol == h  = (True, [], rule_k_h)
              | otherwise    = error "Illegal symbol in derived term"
          establishRule (Variable _)
              = error "Illegal symbol in derived term"

-- Yield the beta-th term and step along the reduction.
--
-- The function establishes (ordLimitPred beta) and starts reducing from there
-- until a sufficient number of terms and steps have been found.
--
-- In case of a limit ordinal the only valid term can be one in which the
-- function symbol k does not occur. Hence, in this case also, only an f-step
-- is possible. After the f-step, only a finite number of k-steps can occur,
-- which occur at depth at least equal to the preceeding f-step. The final
-- k-step of such a finite series will employ the rule k(h(x)) -> h(x), after
-- which an f-step should again occur.
constructTermsAndSteps :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o -> o
       -> (Term Sigma Var, Step Sigma Var)
constructTermsAndSteps inSet geqLub nu alpha beta
    = construct' initial beta' beta' True
        where initial = constructTerm inSet geqLub nu beta' alpha
              beta'   = ordLimitPred beta
              construct' t delta gamma False
                  | delta `ordEq` beta = (t, k_step)
                  | otherwise          = construct' t' delta' gamma f_next
                      where (f_next, k_step) = findStepK t
                            t'     = rewriteStep t k_step
                            delta' = ordSucc delta
              construct' t delta gamma True
                  | delta `ordEq` beta = (t, f_step)
                  | otherwise          = construct' t' delta' gamma' False
                      where f_step = findStepF inSet nu alpha gamma
                            t'     = rewriteStep t f_step
                            delta' = ordSucc delta
                            gamma' = ordSucc gamma

-- Yield the computable sequences of terms and steps of which the reduction is
-- composed.
terms :: (UnivalentSystem o, TermSequence Sigma Var ts o)
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o
       -> ((o -> Term Sigma Var) -> ts) -> ts
terms inSet geqLub nu alpha constr = constr (fst . terms_and_steps)
    where terms_and_steps = constructTermsAndSteps inSet geqLub nu alpha

steps :: (UnivalentSystem o, StepSequence Sigma Var SystemNonLL ss o)
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o
       -> ((o -> Step Sigma Var) -> ss) -> ss
steps inSet geqLub nu alpha constr = constr (snd . terms_and_steps)
    where terms_and_steps = constructTermsAndSteps inSet geqLub nu alpha

-- Yield the modulus of the reduction.
--
-- Given the ordinal and depth of interest, the function establishes the last
-- step that occurs at or above the given depth.
constructModulus :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o
       -> Modulus o
constructModulus inSet geqLub nu alpha beta depth
    | valid     = countSteps inSet geqLub nu alpha delta
    | otherwise = error "Illegal modulus"
            where valid = ordKind beta /= SuccOrdinal
                  delta = findLastOrdinal inSet nu beta' depth
                  beta' = if beta `ordEq` ordZero then alpha else beta

countSteps :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o -> o -> o
countSteps inSet geqLub nu alpha beta
    = count initial beta' beta' True
        where initial = constructTerm inSet geqLub nu beta' alpha
              beta'   = ordLimitPred beta
              count t delta gamma False
                  = count t' delta' gamma f_next
                      where (f_next, k_step) = findStepK t
                            t'     = rewriteStep t k_step
                            delta' = ordSucc delta
              count t delta gamma True
                  | gamma `ordEq` beta = delta
                  | otherwise          = count t' delta' gamma' False
                      where f_step = findStepF inSet nu alpha gamma
                            t'     = rewriteStep t f_step
                            delta' = ordSucc delta
                            gamma' = ordSucc gamma

findLastOrdinal :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> o) -> o -> Integer -> o
findLastOrdinal inSet nu alpha depth
    | null ordinals = ordZero
    | otherwise     = ordSucc (maxOrd (head ordinals) (tail ordinals))
        where ordinals  = [nu d | d <- [0..depth], inSet d, inRange d]
              inRange d = nu d `ordLeq` alpha
              maxOrd delta []
                  = delta
              maxOrd delta (gamma : os)
                  | delta `ordLess` gamma = maxOrd gamma os
                  | otherwise             = maxOrd delta os

-- Yield a non-compressible reduction.
constructReduction :: (UnivalentSystem o, TermSequence Sigma Var ts o,
            StepSequence Sigma Var SystemNonLL ss o)
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o
       -> ((o -> Term Sigma Var) -> ts) -> ((o -> Step Sigma Var) -> ss)
       -> CReduction Sigma Var SystemNonLL
constructReduction inSet geqLub nu alpha constrTermSeq constrStepSeq
    = CRCons (RCons ts ss) phi
        where ts  = terms inSet geqLub nu alpha constrTermSeq
              ss  = steps inSet geqLub nu alpha constrStepSeq
              phi = constructModulus inSet geqLub nu alpha
