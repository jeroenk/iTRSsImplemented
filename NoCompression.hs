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
import Substitution
import Term
import RuleAndSystem
import SystemOfNotation

import Array

data Sigma = SigmaCons String
data Var   = VarCons Char

type Symbol_Sigma_Var       = Symbol Sigma Var
type Term_Sigma_Var         = Term Sigma Var
type Substitution_Sigma_Var = Substitution Sigma Var
type Rule_Sigma_Var         = RewriteRule Sigma Var

instance Signature Sigma where
    arity (SigmaCons "c")  = 0
    arity (SigmaCons "f")  = 3
    arity (SigmaCons "f'") = 3
    arity (SigmaCons "h")  = 1
    arity (SigmaCons "h'") = 1
    arity (SigmaCons "k")  = 1
    arity  _ = error "Character not in signature"

instance Eq Sigma where
    (SigmaCons f) == (SigmaCons g) = f == g

instance Show Sigma where
    show (SigmaCons f) = f

instance Variables Var

instance Eq Var where
    (VarCons x) == (VarCons y) = x == y

instance Show Var where
    show (VarCons x) = [x]

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

f_x_x_y :: Term_Sigma_Var
f_x_x_y = function_term f [Variable x, Variable x, Variable y]

h_k_y :: Term_Sigma_Var
h_k_y = function_term h [k_y]
    where k_y = function_term k [Variable y]

k_f'_x_y_z :: Term_Sigma_Var
k_f'_x_y_z = function_term k [f'_x_y_z]
    where f'_x_y_z = function_term f' [Variable x, Variable y, Variable z]

f_k_x_y_z :: Term_Sigma_Var
f_k_x_y_z = function_term f [k_x, Variable y, Variable z]
    where k_x = function_term k [Variable x]

k_h'_x :: Term_Sigma_Var
k_h'_x = function_term k [h'_x]
    where h'_x = function_term h' [Variable x]

h_k_x :: Term_Sigma_Var
h_k_x = function_term h [k_x]
    where k_x = function_term k [Variable x]

k_h_x :: Term_Sigma_Var
k_h_x = function_term k [h_x]

h_x :: Term_Sigma_Var
h_x = function_term h [Variable x]

h_omega :: Term_Sigma_Var
h_omega = function_term h [h_omega]

rule_f :: Rule_Sigma_Var
rule_f = Rule f_x_x_y h_k_y

rule_k_f' :: Rule_Sigma_Var
rule_k_f' = Rule k_f'_x_y_z f_k_x_y_z

rule_k_h' :: Rule_Sigma_Var
rule_k_h' = Rule k_h'_x h_k_x

rule_k_h :: Rule_Sigma_Var
rule_k_h = Rule k_h_x h_x

term :: UnivalentSystem o
    => (Integer -> Bool) -> (Integer -> Bool) -> (Integer -> o) -> o -> o
       -> Term_Sigma_Var
term in_set geq_lub nu alpha beta = replace_c (term' 0 alpha beta)
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
                                          && succ_kappa `ord_leq` gamma
                        empty_range = (ord_succ delta) `ord_leq` gamma
                        t_1         = term' (d + 1) delta kappa
                        t_2         = constant c
                        t_3         = rename (term' (d + 1) (succ_kappa) gamma)

rename :: Term_Sigma_Var -> Term_Sigma_Var
rename (Function g ts)
    | g == f    = Function f' (ts // [(1, rename (ts!1))])
    | g == h    = Function h' (ts // [(1, rename (ts!1))])
    | g == c    = constant c
    | otherwise = error "Illegal symbol in constructed term"
rename _
    = error "Illegal symbol in constructed term"

replace_c :: Term_Sigma_Var -> Term_Sigma_Var
replace_c (Function g ts)
    | g == c    = h_omega
    | otherwise = Function g (fmap replace_c ts)
replace_c (Variable v)
    = (Variable v)

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

