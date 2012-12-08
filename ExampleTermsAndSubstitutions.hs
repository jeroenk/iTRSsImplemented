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

-- This module defines a signature Sigma, some simple terms over Sigma, and
-- two substitutions over Sigma.

module ExampleTermsAndSubstitutions (
    Sigma(SigmaCons), Var(VarCons),
    a, b, c,
    f_a, f_b, g_a, g_b,
    f_f_a, g_f_a, g_g_a,
    f_x, g_x, h_x_x, h_x_f_x,
    f_omega, g_omega, h_omega,
    f_g_omega, g_f_omega, h_x_omega,
    h_f_f_omega, k_f_omega, f_k_omega,
    sigma_simple, sigma_complex
) where

import SignatureAndVariables
import Substitution
import Term

import Prelude

-- The elements of the signature and the set of variables are characters.
data Sigma = SigmaCons Char
data Var   = VarCons Char

-- The signature Sigma.
instance Signature Sigma where
    arity (SigmaCons 'a') = 0
    arity (SigmaCons 'b') = 0
    arity (SigmaCons 'c') = 0
    arity (SigmaCons 'f') = 1
    arity (SigmaCons 'g') = 1
    arity (SigmaCons 'h') = 2
    arity (SigmaCons 'k') = 3
    arity _  = error "Not a function symbol"

instance Eq Sigma where
    (SigmaCons f) == (SigmaCons g) = f == g

instance Show Sigma where
    show (SigmaCons f) = [f]

-- Variables.
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

-- Term constructors.
f :: Term Sigma Var -> Term Sigma Var
f s = functionTerm (SigmaCons 'f') [s]

g :: Term Sigma Var -> Term Sigma Var
g s = functionTerm (SigmaCons 'g') [s]

h :: Term Sigma Var ->  Term Sigma Var -> Term Sigma Var
h s t = functionTerm (SigmaCons 'h') [s, t]

k :: Term Sigma Var -> Term Sigma Var -> Term Sigma Var -> Term Sigma Var
k s t u = functionTerm (SigmaCons 'k') [s, t, u]

-- Terms.
a :: Term Sigma Var
a = constant (SigmaCons 'a')

b :: Term Sigma Var
b = constant (SigmaCons 'b')

c :: Term Sigma Var
c = constant (SigmaCons 'c')

f_a :: Term Sigma Var
f_a = f a

f_b :: Term Sigma Var
f_b = f b

g_a :: Term Sigma Var
g_a = g a

g_b :: Term Sigma Var
g_b = g b

f_f_a :: Term Sigma Var
f_f_a = f f_a

g_f_a :: Term Sigma Var
g_f_a = g f_a

g_g_a :: Term Sigma Var
g_g_a = g g_a

f_x :: Term Sigma Var
f_x = f (Variable x)

g_x :: Term Sigma Var
g_x = g (Variable x)

h_x_x :: Term Sigma Var
h_x_x = h (Variable x) (Variable x)

h_x_f_x :: Term Sigma Var
h_x_f_x = h (Variable x) f_x

f_omega :: Term Sigma Var
f_omega = f f_omega

g_omega :: Term Sigma Var
g_omega = g g_omega

h_omega :: Term Sigma Var
h_omega = h h_omega h_omega

f_g_omega :: Term Sigma Var
f_g_omega = f g_f_omega

g_f_omega :: Term Sigma Var
g_f_omega = g f_g_omega

h_x_omega :: Term Sigma Var
h_x_omega = h (Variable x) h_x_omega

h_f_f_omega :: Term Sigma Var
h_f_f_omega = h f_omega f_omega

k_f_omega :: Term Sigma Var
k_f_omega = k f_k_omega f_k_omega f_k_omega

f_k_omega :: Term Sigma Var
f_k_omega = f k_f_omega

-- Substitutions.
sigma_simple :: Substitution Sigma Var
sigma_simple = [(x, a)]

sigma_complex :: Substitution Sigma Var
sigma_complex = [(x, a), (y, f_a), (z, h_omega)]
