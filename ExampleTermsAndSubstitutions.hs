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
    x, y, z,
    a, b, c,
    f, g, h, k,
    f_a, f_f_a, g_b, h_a_a, h_b_a,
    f_x, g_x, h_x_f_x,
    f_omega, f_g_omega,
    h_omega, h_f_f_omega, h_x_omega,
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
    (SigmaCons s0) == (SigmaCons s1) = s0 == s1

instance Show Sigma where
    show (SigmaCons s) = [s]

-- Variables.
instance Variables Var

instance Eq Var where
    (VarCons v0) == (VarCons v1) = v0 == v1

instance Show Var where
    show (VarCons v) = [v]

xVar :: Var
xVar = VarCons 'x'

x :: Term Sigma Var
x = Variable xVar

yVar :: Var
yVar = VarCons 'y'

y :: Term Sigma Var
y = Variable yVar

zVar :: Var
zVar = VarCons 'z'

z :: Term Sigma Var
z = Variable zVar

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

g_b :: Term Sigma Var
g_b = g b

f_f_a :: Term Sigma Var
f_f_a = f f_a

h_a_a :: Term Sigma Var
h_a_a = h a a

h_b_a :: Term Sigma Var
h_b_a = h b a

f_x :: Term Sigma Var
f_x = f x

g_x :: Term Sigma Var
g_x = g x

h_x_f_x :: Term Sigma Var
h_x_f_x = h x f_x

f_omega :: Term Sigma Var
f_omega = f f_omega

h_omega :: Term Sigma Var
h_omega = h h_omega h_omega

f_g_omega :: Term Sigma Var
f_g_omega = f g_f_omega

g_f_omega :: Term Sigma Var
g_f_omega = g f_g_omega

h_f_f_omega :: Term Sigma Var
h_f_f_omega = h f_omega f_omega

h_x_omega :: Term Sigma Var
h_x_omega = h x h_x_omega

-- Substitutions.
sigma_simple :: Substitution Sigma Var
sigma_simple = [(xVar, a)]

sigma_complex :: Substitution Sigma Var
sigma_complex = [(xVar, a), (yVar, f_a), (zVar, h_omega)]
