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

-- This module defines a system with a non-left-linear rule which allows for
-- the definition of non-compressible reductions.
--
-- The system has four rules:
--
--    f(x, x, y)     -> h(k(y))
--    k(f'(x, y, z)) -> f(k(x), y, z)
--    k(h'(x))       -> h(k(x))
--    k(h(x))        -> h(x)
--

module NoCompressionSystem (
    Sigma, Var,
    cFun, fFun, fFun', hFun, hFun', kFun,
    c, f, f', h, h', k,
    addPrime, replaceC,
    rule_f, rule_k_f',
    rule_k_h', rule_k_h,
    SystemNonLL, systemNonLL
) where

import SignatureAndVariables
import Term
import RuleAndSystem

import Prelude
import Data.Array

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
xVar :: Var
xVar = VarCons 'x'

yVar :: Var
yVar = VarCons 'y'

zVar :: Var
zVar = VarCons 'z'

cFun :: Sigma
cFun = SigmaCons "c"

fFun :: Sigma
fFun = SigmaCons "f"

fFun' :: Sigma
fFun' = SigmaCons "f'"

hFun :: Sigma
hFun = SigmaCons "h"

hFun' :: Sigma
hFun' = SigmaCons "h'"

kFun :: Sigma
kFun = SigmaCons "k"

-- Term constructors.
x :: Term Sigma Var
x = Variable xVar

y :: Term Sigma Var
y = Variable yVar

z :: Term Sigma Var
z = Variable zVar

c :: Term Sigma Var
c = constant cFun

f :: Term Sigma Var -> Term Sigma Var -> Term Sigma Var -> Term Sigma Var
f s t u = functionTerm fFun [s, t, u]

f' :: Term Sigma Var -> Term Sigma Var -> Term Sigma Var -> Term Sigma Var
f' s t u = functionTerm fFun' [s, t, u]

h :: Term Sigma Var -> Term Sigma Var
h s = functionTerm hFun [s]

h' :: Term Sigma Var -> Term Sigma Var
h' s = functionTerm hFun' [s]

k :: Term Sigma Var -> Term Sigma Var
k s = functionTerm kFun [s]

-- The following two functions are simple helper functions used in construction
-- of the terms that occur in non-compressible reductions.

-- Add a prime to the root symbol of a term if this symbol is either f or h and
-- recurse into the left-most subterm.
addPrime :: Term Sigma Var -> Term Sigma Var
addPrime (Function symbol ts)
    | symbol == fFun = Function fFun' (ts // [(1, addPrime $ ts!1)])
    | symbol == hFun = Function hFun' (ts // [(1, addPrime $ ts!1)])
    | symbol == cFun = c
    | otherwise   = error "Illegal symbol in constructed term"
addPrime _
    = error "Illegal symbol in constructed term"

-- Replace the constant c by h^omega.
replaceC :: Term Sigma Var -> Term Sigma Var
replaceC (Function symbol ts)
    | symbol == cFun = h_omega
    | otherwise      = Function symbol (fmap replaceC ts)
replaceC (Variable v)
    = Variable v

-- Terms employed in the rewrite rules and h^omega.
f_x_x_y :: Term Sigma Var
f_x_x_y = f x x y

h_k_y :: Term Sigma Var
h_k_y = h (k y)

k_fp_x_y_z :: Term Sigma Var
k_fp_x_y_z = k (f' x y z)

f_k_x_y_z :: Term Sigma Var
f_k_x_y_z = f (k x) y z

k_hp_x :: Term Sigma Var
k_hp_x = k (h' x)

h_k_x :: Term Sigma Var
h_k_x = h (k x)

k_h_x :: Term Sigma Var
k_h_x = k (h x)

h_x :: Term Sigma Var
h_x = h x

h_omega :: Term Sigma Var
h_omega = h h_omega

-- The rewrite rules.
rule_f :: RewriteRule Sigma Var
rule_f = Rule f_x_x_y h_k_y

rule_k_f' :: RewriteRule Sigma Var
rule_k_f' = Rule k_fp_x_y_z f_k_x_y_z

rule_k_h' :: RewriteRule Sigma Var
rule_k_h' = Rule k_hp_x h_k_x

rule_k_h :: RewriteRule Sigma Var
rule_k_h = Rule k_h_x h_x

-- The non-left-linear rewrite system.
type SystemNonLL = System Sigma Var

systemNonLL :: SystemNonLL
systemNonLL = SystemCons [rule_f, rule_k_f', rule_k_h', rule_k_h]
