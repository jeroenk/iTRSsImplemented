{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
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

module ExampleTermsAndSubstitutions (
    Sigma(SigmaCons), Var(VarCons),
    Term_Sigma_Var, Symbol_Sigma_Var,
    Substitution_Sigma_Var,
    a, b, c, f_a, g_a, f_f_a, g_f_a, g_g_a,
    f_x, g_x, h_x_x, h_x_f_x,
    f_omega, g_omega, h_omega,
    f_g_omega, g_f_omega,
    h_x_omega, k_f_omega, f_k_omega,
    sigma_simple, sigma_complex
) where

import SignatureAndVariables
import Substitutions
import Terms

data Sigma = SigmaCons Char
data Var   = VarCons Char

type Symbol_Sigma_Var       = Symbol Sigma Var
type Term_Sigma_Var         = Term Sigma Var
type Substitution_Sigma_Var = Substitution Sigma Var

instance Signature Sigma where
    arity (SigmaCons 'a') = 0
    arity (SigmaCons 'b') = 0
    arity (SigmaCons 'c') = 0
    arity (SigmaCons 'f') = 1
    arity (SigmaCons 'g') = 1
    arity (SigmaCons 'h') = 2
    arity (SigmaCons 'k') = 3
    arity  _  = error "Character not in signature"

instance Eq Sigma where
    (SigmaCons f) == (SigmaCons g) = f == g

instance Show Sigma where
    show (SigmaCons f) = [f]

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

a :: Term_Sigma_Var
a = constant (SigmaCons 'a')

b :: Term_Sigma_Var
b = constant (SigmaCons 'b')

c :: Term_Sigma_Var
c = constant (SigmaCons 'c')

f :: Sigma
f = SigmaCons 'f'

g :: Sigma
g = SigmaCons 'g'

h :: Sigma
h = SigmaCons 'h'

k :: Sigma
k = SigmaCons 'k'

f_a :: Term_Sigma_Var
f_a = function_term f [(1, a)]

g_a :: Term_Sigma_Var
g_a = function_term g [(1, a)]

f_f_a :: Term_Sigma_Var
f_f_a = function_term f [(1, f_a)]

g_f_a :: Term_Sigma_Var
g_f_a = function_term g [(1, f_a)]

g_g_a :: Term_Sigma_Var
g_g_a = function_term g [(1, g_a)]

f_x :: Term_Sigma_Var
f_x = function_term f [(1, Variable x)]

g_x :: Term_Sigma_Var
g_x = function_term g [(1, Variable x)]

h_x_x :: Term_Sigma_Var
h_x_x = function_term h [(1, Variable x), (2, Variable x)]

h_x_f_x :: Term_Sigma_Var
h_x_f_x = function_term h [(1, Variable x), (2, f_x)]

f_omega :: Term_Sigma_Var
f_omega = function_term f [(1, f_omega)]

g_omega :: Term_Sigma_Var
g_omega = function_term g [(1, g_omega)]

h_omega :: Term_Sigma_Var
h_omega = function_term h [(1, h_omega), (2, h_omega)]

f_g_omega :: Term_Sigma_Var
f_g_omega = function_term f [(1, g_f_omega)]

g_f_omega :: Term_Sigma_Var
g_f_omega = function_term g [(1, f_g_omega)]

h_x_omega :: Term_Sigma_Var
h_x_omega = function_term h [(1, Variable x), (2, h_x_omega)]

k_f_omega :: Term_Sigma_Var
k_f_omega = function_term k [(1, f_k_omega), (2, f_k_omega), (3, f_k_omega)]

f_k_omega :: Term_Sigma_Var
f_k_omega = function_term f [(1, k_f_omega)]

sigma_simple :: Substitution_Sigma_Var
sigma_simple = [(x, a)]

sigma_complex :: Substitution_Sigma_Var
sigma_complex = [(x, a), (y, f_a), (z, h_omega)]
