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

import SignatureAndVariables
import Term
import RuleAndSystem
import SystemOfNotation

import Array

import Omega

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
                            t_3 = rename (term' (d + 1) (succ_kappa) gamma)

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
    = (Variable v)

construct_terms_and_steps :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o
       -> o -> (Term Sigma Var, Step Sigma Var)
construct_terms_and_steps in_set geq_lub nu alpha beta
    = construct initial_term beta' beta' True
        where initial_term = construct_term in_set geq_lub nu beta' alpha
              beta'        = ord_lim_pred beta
              construct t delta gamma False
                  | delta `ord_eq` beta = (t, k_step)
                  | otherwise           = construct t' delta' gamma f_next
                      where (f_next, k_step) = find_k_step t
                            t'     = rewrite_step t k_step
                            delta' = ord_succ delta
              construct t delta gamma True
                  | delta `ord_eq` beta = (t, f_step)
                  | otherwise           = construct t' delta' gamma' False
                      where f_step = find_f_step in_set nu alpha gamma
                            t'     = rewrite_step t f_step
                            delta' = ord_succ delta
                            gamma' = ord_succ gamma

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

find_f_step :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> o) -> o -> o -> Step Sigma Var
find_f_step in_set nu alpha beta = (find_f_step' 0, rule_f)
    where find_f_step' d
              | beta `ord_eq` alpha
                  = error "No step with requested index"
              | in_set d && nu(d) `ord_eq` beta
                  = []
              | otherwise
                  = 1 : find_f_step' (d + 1)

-- Reductie stap:
-- * geen limiet ordinaal: zoek vorige en doe unieke stap
-- * wel limiet ordinaal of nul: bereken term en doe unieke stap
--            let op: we moeten wel weten of het een k stap of een f stap is,
--                    anders gaan we misschien zoeken in h_omega subterm
--
-- Modulus:
--    kijk of er nog latere stappen in de gevraagde range zitten die hoger
--    liggen dan nu^{-1}(d) (kan omdat we over een bijectie spreken en dus
--    iedere diepte maar een keer voor komt). We moeten we compenseren voor de
--    k-stappen, maar deze gebeuren altijd onder de nu^{-1}(d) stap die we
--    zoeken.

fin_in_set :: Integer -> Bool
fin_in_set n = n `elem` [1, 3, 5, 7]

fin_geq_lub :: Integer -> Bool
fin_geq_lub n = n >= 10

fin_nu :: Integer -> Omega
fin_nu 1 = OmegaElement 2
fin_nu 3 = OmegaElement 1
fin_nu 5 = OmegaElement 0
fin_nu 7 = OmegaElement 3
fin_nu _ = error "Impossible"

fin_term :: Term Sigma Var
fin_term = construct_term fin_in_set fin_geq_lub fin_nu (OmegaElement 0) (OmegaElement 4)

fin_ts :: Omega -> (Term Sigma Var, Step Sigma Var)
fin_ts = construct_terms_and_steps fin_in_set fin_geq_lub fin_nu (OmegaElement 4)
