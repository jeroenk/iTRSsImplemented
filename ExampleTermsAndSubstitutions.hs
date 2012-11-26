{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
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

-- This module defines a signature Sigma and some simple terms over Sigma.

module ExampleTermsAndSubstitutions (
    Sigma(SigmaCons), Var(VarCons),
    f, g, h,
    a, b, c, f_a, g_a, f_f_a, g_f_a, g_g_a,
    f_x, g_x, h_x_x, h_x_f_x,
    f_omega, g_omega, h_omega,
    f_g_omega, g_f_omega,
    h_x_omega, k_f_omega, f_k_omega,
    sigma_simple, sigma_complex
) where

import SignatureAndVariables
import Substitution
import Term

import Prelude

data Sigma = SigmaCons Char
data Var   = VarCons Char

instance Signature Sigma where
    arity (SigmaCons 'a') = 0
    arity (SigmaCons 'b') = 0
    arity (SigmaCons 'c') = 0
    arity (SigmaCons 'f') = 1
    arity (SigmaCons 'g') = 1
    arity (SigmaCons 'h') = 2
    arity (SigmaCons 'k') = 3
    arity _  = error "Symbol not in signature"

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

a :: Term Sigma Var
a = constant (SigmaCons 'a')

b :: Term Sigma Var
b = constant (SigmaCons 'b')

c :: Term Sigma Var
c = constant (SigmaCons 'c')

f :: Sigma
f = SigmaCons 'f'

g :: Sigma
g = SigmaCons 'g'

h :: Sigma
h = SigmaCons 'h'

k :: Sigma
k = SigmaCons 'k'

f_a :: Term Sigma Var
f_a = functionTerm f [a]

g_a :: Term Sigma Var
g_a = functionTerm g [a]

f_f_a :: Term Sigma Var
f_f_a = functionTerm f [f_a]

g_f_a :: Term Sigma Var
g_f_a = functionTerm g [f_a]

g_g_a :: Term Sigma Var
g_g_a = functionTerm g [g_a]

f_x :: Term Sigma Var
f_x = functionTerm f [Variable x]

g_x :: Term Sigma Var
g_x = functionTerm g [Variable x]

h_x_x :: Term Sigma Var
h_x_x = functionTerm h [Variable x, Variable x]

h_x_f_x :: Term Sigma Var
h_x_f_x = functionTerm h [Variable x, f_x]

f_omega :: Term Sigma Var
f_omega = functionTerm f [f_omega]

g_omega :: Term Sigma Var
g_omega = functionTerm g [g_omega]

h_omega :: Term Sigma Var
h_omega = functionTerm h [h_omega, h_omega]

f_g_omega :: Term Sigma Var
f_g_omega = functionTerm f [g_f_omega]

g_f_omega :: Term Sigma Var
g_f_omega = functionTerm g [f_g_omega]

h_x_omega :: Term Sigma Var
h_x_omega = functionTerm h [Variable x, h_x_omega]

k_f_omega :: Term Sigma Var
k_f_omega = functionTerm k [f_k_omega, f_k_omega, f_k_omega]

f_k_omega :: Term Sigma Var
f_k_omega = functionTerm f [k_f_omega]

sigma_simple :: Substitution Sigma Var
sigma_simple = [(x, a)]

sigma_complex :: Substitution Sigma Var
sigma_complex = [(x, a), (y, f_a), (z, h_omega)]
