{-# LANGUAGE FlexibleContexts #-}
{-
Copyright (C) 2011 Jeroen Ketema

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
    System_Non_LL, system_non_ll,
    construct_reduction
) where

import SignatureAndVariables
import Term
import RuleAndSystem
import SystemOfNotation
import Reduction

import Array

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
    arity  _ = error "Character not in signature"

instance Eq Sigma where
    (SigmaCons symbol_0) == (SigmaCons symbol_1) = symbol_0 == symbol_1

instance Show Sigma where
    show (SigmaCons symbol) = symbol

instance Variables Var

instance Eq Var where
    (VarCons variable_0) == (VarCons variable_1) = variable_0 == variable_1

instance Show Var where
    show (VarCons variable) = [variable]

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
f_x_x_y = function_term f [Variable x, Variable x, Variable y]

h_k_y :: Term Sigma Var
h_k_y = function_term h [k_y]
    where k_y = function_term k [Variable y]

k_f'_x_y_z :: Term Sigma Var
k_f'_x_y_z = function_term k [f'_x_y_z]
    where f'_x_y_z = function_term f' [Variable x, Variable y, Variable z]

f_k_x_y_z :: Term Sigma Var
f_k_x_y_z = function_term f [k_x, Variable y, Variable z]
    where k_x = function_term k [Variable x]

k_h'_x :: Term Sigma Var
k_h'_x = function_term k [h'_x]
    where h'_x = function_term h' [Variable x]

h_k_x :: Term Sigma Var
h_k_x = function_term h [k_x]
    where k_x = function_term k [Variable x]

k_h_x :: Term Sigma Var
k_h_x = function_term k [h_x]

h_x :: Term Sigma Var
h_x = function_term h [Variable x]

h_omega :: Term Sigma Var
h_omega = function_term h [h_omega]

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
type System_Non_LL = BasicSystem Sigma Var

system_non_ll :: System_Non_LL
system_non_ll = BasicSystemCons [rule_f, rule_k_f', rule_k_h', rule_k_h]

-- Two helper functions for ordinals derived from ord_leq.
ord_less :: UnivalentSystem o
    => o -> o -> Bool
ord_less alpha beta = alpha `ord_leq` beta && not (beta `ord_leq` alpha)

ord_eq :: UnivalentSystem o
    => o -> o -> Bool
ord_eq alpha beta = alpha `ord_leq` beta && beta `ord_leq` alpha

-- Construction of terms in which the symbol k does not occur.
construct_term :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o -> o
       -> Term Sigma Var
construct_term in_set geq_lub nu alpha beta = replace_c (term' 0 alpha beta)
    where term' d delta gamma
              | in_set d && in_range
                  = function_term f [t_1, t_2, t_3]
              | geq_lub d || empty_range
                  = constant c
              | otherwise
                  = function_term h [term' (d + 1) delta gamma]
                      where kappa       = nu d
                            succ_kappa  = ord_succ kappa
                            in_range    = delta `ord_leq` kappa
                                              && kappa `ord_less` gamma
                            empty_range = not (delta `ord_less` gamma)
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

replace_c :: Term Sigma Var -> Term Sigma Var
replace_c (Function symbol ts)
    | symbol == c = h_omega
    | otherwise   = Function symbol (fmap replace_c ts)
replace_c (Variable v)
    = Variable v

-- Two helper functions to locate the next redex, given it is known the next
-- redex either employs the f-rule or one of the k-rules.
find_f_step :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> o) -> o -> o -> Step Sigma Var
find_f_step in_set nu alpha beta = (find_f_step' 0, rule_f)
    where find_f_step' d
              | beta `ord_eq` alpha
                  = error "No step with requested index"
              | in_set d && nu d `ord_eq` beta
                  = []
              | otherwise
                  = 1 : find_f_step' (d + 1)

find_k_step :: Term Sigma Var -> (Bool, Step Sigma Var)
find_k_step term = (f_next, (position, rule))
    where (f_next, position, rule) = find_k_step' term
          find_k_step' (Function symbol ts)
              | symbol == k = establish_rule (ts!1)
              | otherwise   = (f_n, 1 : p, r)
                  where (f_n, p, r) = find_k_step' (ts!1)
          find_k_step' (Variable _)
              = error "Illegal symbol in derived term"
          establish_rule (Function symbol _)
              | symbol == f' = (False, [], rule_k_f')
              | symbol == h' = (False, [], rule_k_h')
              | symbol == h  = (True, [], rule_k_h)
              | otherwise    = error "Illegal symbol in derived term"
          establish_rule (Variable _)
              = error "Illegal symbol in derived term"

-- Yield the beta-th term and step along the reduction.
--
-- The function establishes (ord_lim_pred beta) and starts reducing from there
-- until a sufficient number of terms and steps have been found.
--
-- In case of a limit ordinal the only valid term can be one in which the
-- function symbol k does not occur. Hence, in this case also, only an f-step
-- is possible. After the f-step, only a finite number of k-steps can occur,
-- which occur at depth at least equal to the preceeding f-step. The final
-- k-step of such a finite series will employ the rule k(h(x)) -> h(x), after
-- which an f-step should again occur.
construct_terms_and_steps :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o -> o
       -> (Term Sigma Var, Step Sigma Var)
construct_terms_and_steps in_set geq_lub nu alpha beta
    = construct' term_initial beta' beta' True
        where term_initial = construct_term in_set geq_lub nu beta' alpha
              beta'        = ord_lim_pred beta
              construct' t delta gamma False
                  | delta `ord_eq` beta = (t, k_step)
                  | otherwise           = construct' t' delta' gamma f_next
                      where (f_next, k_step) = find_k_step t
                            t'     = rewrite_step t k_step
                            delta' = ord_succ delta
              construct' t delta gamma True
                  | delta `ord_eq` beta = (t, f_step)
                  | otherwise           = construct' t' delta' gamma' False
                      where f_step = find_f_step in_set nu alpha gamma
                            t'     = rewrite_step t f_step
                            delta' = ord_succ delta
                            gamma' = ord_succ gamma

-- Yield the computable sequences of terms and steps of which the reduction is
-- composed.
terms :: (UnivalentSystem o, TermSequence Sigma Var ts o)
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o
       -> ((o -> Term Sigma Var) -> ts) -> ts
terms in_set geq_lub nu alpha constr = constr (fst . terms_and_steps)
    where terms_and_steps = construct_terms_and_steps in_set geq_lub nu alpha

steps :: (UnivalentSystem o, StepSequence Sigma Var System_Non_LL ss o)
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o
       -> ((o -> Step Sigma Var) -> ss) -> ss
steps in_set geq_lub nu alpha constr = constr (snd . terms_and_steps)
    where terms_and_steps = construct_terms_and_steps in_set geq_lub nu alpha

-- Yield the modulus of the reduction.
--
-- Given the ordinal and depth of interest, the function establishes the last
-- step that occurs at or above the given depth.
construct_modulus :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o
       -> Modulus o
construct_modulus in_set geq_lub nu alpha beta depth
    | valid     = count_steps in_set geq_lub nu alpha delta
    | otherwise = error "Illegal modulus"
            where valid = ord_kind beta /= SuccOrdinal
                  delta = find_last_ordinal in_set nu beta' depth
                  beta' = if beta `ord_eq` ord_zero then alpha else beta

count_steps :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o -> o
       -> o
count_steps in_set geq_lub nu alpha beta
    = count term_initial beta' beta' True
        where term_initial = construct_term in_set geq_lub nu beta' alpha
              beta'        = ord_lim_pred beta
              count t delta gamma False
                  = count t' delta' gamma f_next
                      where (f_next, k_step) = find_k_step t
                            t'     = rewrite_step t k_step
                            delta' = ord_succ delta
              count t delta gamma True
                  | gamma `ord_eq` beta = delta
                  | otherwise           = count t' delta' gamma' False
                      where f_step = find_f_step in_set nu alpha gamma
                            t'     = rewrite_step t f_step
                            delta' = ord_succ delta
                            gamma' = ord_succ gamma

find_last_ordinal :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> o) -> o -> Integer -> o
find_last_ordinal in_set nu alpha depth
    | null ordinals = ord_zero
    | otherwise     = ord_succ (max_ord (head ordinals) (tail ordinals))
        where ordinals = [nu d | d <- [0..depth], in_set d, in_range d]
              in_range d = nu d `ord_leq` alpha
              max_ord delta []
                  = delta
              max_ord delta (gamma:os)
                  | delta `ord_less` gamma = max_ord gamma os
                  | otherwise              = max_ord delta os

-- Yield a non-compressible reduction.
construct_reduction :: (UnivalentSystem o, TermSequence Sigma Var ts o,
            StepSequence Sigma Var System_Non_LL ss o)
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o
       -> ((o -> Term Sigma Var) -> ts) -> ((o -> Step Sigma Var) -> ss)
       -> CReduction Sigma Var System_Non_LL
construct_reduction in_set geq_lub nu alpha constr_t constr_s
    = CRCons (RCons ts ss) phi
        where ts  = terms in_set geq_lub nu alpha constr_t
              ss  = steps in_set geq_lub nu alpha constr_s
              phi = construct_modulus in_set geq_lub nu alpha
