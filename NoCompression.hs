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
import SystemOfNotation hiding (k)

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
f_x_x_y = function_term f [(1, Variable x), (2, Variable x), (3, Variable y)]

h_k_y :: Term_Sigma_Var
h_k_y = function_term h [(1, k_y)]
    where k_y = function_term k [(1, Variable y)]

k_f'_x_y_z :: Term_Sigma_Var
k_f'_x_y_z = function_term k [(1, f'_x_y_z)]
    where f'_x_y_z = function_term f' [(1, Variable x), (2, Variable y),
                                           (3, Variable z)]

f_k_x_y_z :: Term_Sigma_Var
f_k_x_y_z = function_term f [(1, k_x), (2, Variable y), (3, Variable z)]
    where k_x = function_term k [(1, Variable x)]

k_h'_x :: Term_Sigma_Var
k_h'_x = function_term k [(1, h'_x)]
    where h'_x = function_term h' [(1, Variable x)]

h_k_x :: Term_Sigma_Var
h_k_x = function_term h [(1, k_x)]
    where k_x = function_term k [(1, Variable x)]

k_h_x :: Term_Sigma_Var
k_h_x = function_term k [(1, h_x)]
    where h_x = function_term h [(1, Variable x)]

h_x :: Term_Sigma_Var
h_x = function_term h [(1, Variable x)]

h_omega :: Term_Sigma_Var
h_omega = function_term h [(1, h_omega)]

rule_f :: Rule_Sigma_Var
rule_f = Rule f_x_x_y h_k_y

rule_k_f' :: Rule_Sigma_Var
rule_k_f' = Rule k_f'_x_y_z f_k_x_y_z

rule_k_h' :: Rule_Sigma_Var
rule_k_h' = Rule k_h'_x h_k_x

rule_k_h :: Rule_Sigma_Var
rule_k_h = Rule k_h_x h_x

term :: (UnivalSystem o)
    => (Int -> Bool) -> (Int -> Bool) -> (Int -> o) -> o -> o -> Term_Sigma_Var
term in_set geq_lub nu alpha beta = replace_c (term' 0 alpha beta)
    where term' d delta gamma
              | in_set d && in_range
                  = function_term f [(1, t_1), (2, t_2), (3, t_3)]
              | geq_lub d || empty_range
                  = constant c
              | otherwise
                  = function_term h [(1, term' (d + 1) delta gamma)]
                  where kappa       = nu d
                        in_range    = delta `leq` kappa && suc kappa `leq` gamma
                        empty_range = (suc delta) `leq` gamma
                        t_1         = term' (d + 1) delta kappa
                        t_2         = constant c
                        t_3         = rename (term' (d + 1) (suc kappa) gamma)
          rename (Function g ts)
              | g == f    = Function f' (ts // [(1, rename (ts!1))])
              | g == h    = Function h' (ts // [(1, rename (ts!1))])
              | g == c    = constant c
              | otherwise = error "Illegal symbol in constructed term"
          rename _
              = error "Illegal symbol in constructed term"
          replace_c (Function symbol ts)
              | symbol == c = h_omega
              | otherwise   = Function symbol (fmap replace_c ts)
          replace_c (Variable v)
              = Variable v
