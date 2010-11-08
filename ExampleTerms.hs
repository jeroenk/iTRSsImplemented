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

-- This module defines a signature Sigma and some simple terms over Sigma.

module ExampleTerms (
    Sigma,
    Var,
    Term_Sigma_Var,
    Symbol_Sigma_Var,
    a, b, c, f_x, f_a, g_x,
    f_omega, g_omega, h_omega,
    h_x_omega, k_f_omega, f_k_omega
) where

import SignatureAndVariables
import Terms

type Sigma = Char
type Var   = Char

type Term_Sigma_Var = Term Sigma Var
type Symbol_Sigma_Var = Symbol Sigma Var

instance Signature Sigma where
    arity 'a' = 0
    arity 'b' = 0
    arity 'c' = 0
    arity 'f' = 1
    arity 'g' = 1
    arity 'h' = 2
    arity 'k' = 3
    arity _   = error "Character not in signature"

instance Variables Var

a :: Term_Sigma_Var
a = constant 'a'

b :: Term_Sigma_Var
b = constant 'b'

c :: Term_Sigma_Var
c = constant 'c'

f_x :: Term_Sigma_Var
f_x = function_term 'f' [(1, Variable 'x')]

f_a :: Term_Sigma_Var
f_a = function_term 'f' [(1, a)]

g_x :: Term_Sigma_Var
g_x = function_term 'g' [(1, Variable 'x')]

f_omega :: Term_Sigma_Var
f_omega = function_term 'f' [(1, f_omega)]

g_omega :: Term_Sigma_Var
g_omega = function_term 'g' [(1, g_omega)]

h_omega :: Term_Sigma_Var
h_omega = function_term 'h' [(1, h_omega), (2, h_omega)]

h_x_omega :: Term_Sigma_Var
h_x_omega = function_term 'h' [(1, Variable 'x'), (2, h_x_omega)]

k_f_omega :: Term_Sigma_Var
k_f_omega = function_term 'k' [(1, f_k_omega), (2, f_k_omega), (3, f_k_omega)]

f_k_omega :: Term_Sigma_Var
f_k_omega = function_term 'f' [(1, k_f_omega)]