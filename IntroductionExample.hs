{-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-type-defaults #-}
{-
Copyright (C) 2012 Jeroen Ketema and Jakob Grue Simonsen

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

-- This file implements propositional Boolean logic, which is the introductory
-- example in "Rewriting with Infinite Terms and Infinite Reductions".

import SignatureAndVariables
import Term
import RuleAndSystem
import Reduction
import Omega2
import Compression

import Prelude hiding (and, or, not)

-- The elements of the signature and the set of variables are characters.
data Sigma = SigmaCons String
data V     = VarCons String

-- The signature Sigma.
instance Signature Sigma where
    arity (SigmaCons "true")  = 0
    arity (SigmaCons "false") = 0
    arity (SigmaCons "not")   = 1
    arity (SigmaCons "and")   = 2
    arity (SigmaCons "or")    = 2
    arity _ = error "Not a function symbol"

instance Eq Sigma where
    (SigmaCons f) == (SigmaCons g) = f == g

instance Show Sigma where
    show (SigmaCons f) = f

-- Variables.
instance Variables V

instance Eq V where
    (VarCons x) == (VarCons y) = x == y

instance Show V where
    show (VarCons x) = x

x :: Term Sigma V
x = Variable (VarCons "x")

y :: Term Sigma V
y = Variable (VarCons "y")

-- Terms and term constructors.
true :: Term Sigma V
true = constant (SigmaCons "true")

false :: Term Sigma V
false = constant (SigmaCons "false")

not :: Term Sigma V -> Term Sigma V
not s = functionTerm (SigmaCons "not") [s]

and :: Term Sigma V -> Term Sigma V -> Term Sigma V
and s t = functionTerm (SigmaCons "and") [s, t]

or :: Term Sigma V -> Term Sigma V -> Term Sigma V
or s t = functionTerm (SigmaCons "or") [s, t]

-- Simplification rules for Boolean logic.
ruleNot :: RewriteRule Sigma V
ruleNot = Rule (not true) false

ruleNotNot :: RewriteRule Sigma V
ruleNotNot = Rule (not (not x)) x

ruleAndTrue :: RewriteRule Sigma V
ruleAndTrue = Rule (true `and` x) x

ruleAndFalse :: RewriteRule Sigma V
ruleAndFalse = Rule (false `and` x) false

ruleOr :: RewriteRule Sigma V
ruleOr = Rule (x `or` y) (not ((not x) `and` (not y)))

-- The rewrite system for Boolean logic with the simplification rules.
type BooleanSystem = System Sigma V

booleanSystem :: BooleanSystem
booleanSystem = SystemCons [ruleNot, ruleNotNot, ruleAndTrue,
                                ruleAndFalse, ruleOr]

-- The infinite term (true /\ x1) \/ (true /\ x2) \/ (true /\ x3) \/ ...
infiniteTerm1 :: Term Sigma V
infiniteTerm1 = mT 1
    where  mT i = (aT i) `or` (mT (i + 1))
           aT i = true `and` (mV i)
           mV i = Variable (xi i)
           xi i = VarCons ('x' : show i)

-- The infinite term x1 \/ (true /\ x2) \/ x3 \/ (true /\ x4) \/ ...
infiniteTerm2 :: Term Sigma V
infiniteTerm2 = mT 1
    where  mT  i = (mV i) `or` (mT' (i + 1))
           mT' i = (aT i) `or` (mT  (i + 1))
           aT  i = true `and` (mV i)
           mV  i = Variable (xi i)
           xi  i = VarCons ('x' : show i)

-- The infinite reduction
--
-- (true /\ x1) \/ (true /\ x2) \/ (true /\ x3) \/ ...
--    ->> x1 \/ (true /\ x2) \/ x3 \/ (true /\ x4) \/ ...
--        ->> x1 \/ x2 \/ x3 \/ x4 \/ ...
--
reduction :: Omega2Reduction Sigma V BooleanSystem
reduction = RCons terms steps
    where  terms   = constructSequence terms_1 terms_2
           steps   = constructSequence steps_1 steps_2
           terms_1 = rewriteSteps infiniteTerm1 steps_1
           steps_1 = zip ps_1 rs_1
           ps_1 = iterate (\p -> 2 : 2 : p) [1]
           rs_1 = repeat ruleAndTrue
           terms_2 = rewriteSteps infiniteTerm2 steps_2
           steps_2 = zip ps_2 rs_2
           ps_2 = iterate (\p -> 2 : 2 : p) [2, 1]
           rs_2 = repeat ruleAndTrue

creduction :: CReduction Sigma V BooleanSystem
creduction = CRCons reduction phi
    where  phi (OmegaElement 0)   m  = Omega2Element  m
           phi (Omega2Element 0)  m  = OmegaElement   m
           phi _                  _  = error "Illegal modulus"

-- Compression of creduction.
--
-- To obtain the final term of the compressed redution input:
--
--     finalTerm $ compressedReduction
--
compressedReduction :: CReduction Sigma V BooleanSystem
compressedReduction = compression booleanSystem creduction
