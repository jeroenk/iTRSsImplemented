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

-- This file defines some reductions that can be tried with the Church-Rosser
-- algorithm.

import RuleAndSystem
import Reduction
import Omega
import ChurchRosser
import ExampleTermsAndSubstitutions
import ExampleRulesAndSystems

import Prelude

-- The combinations to try with the reductions below are the following:
--
-- fst $ churchRosser system_a_f_x [(cRed1a, cRed1b), (cRed1c, cRed1d)]
-- snd $ churchRosser system_a_f_x [(cRed1a, cRed1b), (cRed1c, cRed1d)]

--
-- a -> f(a) -> f^2(a) -> ... -> f^n(a) -> ...
--
red1a :: OmegaReduction Sigma Var System_a_f_x
red1a = RCons (constructSequence terms) (constructSequence steps)
    where terms = rewriteSteps a steps
          steps = zip ps rs
          ps = iterate (\p -> 1:p) []
          rs = repeat rule_a_to_f_a

cRed1a :: CReduction Sigma Var System_a_f_x
cRed1a = CRCons red1a (constructModulus phi)
    where phi x = x + 1

--
-- f^omega
--
red1b :: OmegaReduction Sigma Var System_a_f_x
red1b = RCons (constructSequence [f_omega]) (constructSequence [])

cRed1b :: CReduction Sigma Var System_a_f_x
cRed1b = CRCons red1b (constructModulus phi)
    where phi _ = 0

--
-- f^omega -> g(f^omega) -> g(f(g(f^omega))) -> ... -> (gf)^n(f^omega) -> ...
--
red1c :: OmegaReduction Sigma Var System_a_f_x
red1c = RCons (constructSequence terms) (constructSequence steps)
    where terms = rewriteSteps f_omega steps
          steps = zip ps rs
          ps = iterate (\p -> 1:1:p) []
          rs = repeat rule_f_x_to_g_x

cRed1c :: CReduction Sigma Var System_a_f_x
cRed1c = CRCons red1c (constructModulus phi)
    where phi x = x + 1

--
-- a -> f(a) -> g(a) -> g(f(a)) -> g(f(f(a))) -> g(f(g(a))) -> ...
--                         -> (gf)^n(a) -> (gf)^n(f(a)) -> (gf)^n(g(a)) -> ...
--
red1d :: OmegaReduction Sigma Var System_a_f_x
red1d = RCons (constructSequence terms) (constructSequence steps)
    where terms = rewriteSteps a steps
          steps = zip ps rs
          ps = [] : [] : [1] : map (\p -> 1:1:p) ps
          rs = rule_a_to_f_a : rule_f_x_to_g_x : rule_a_to_f_a : rs

cRed1d :: CReduction Sigma Var System_a_f_x
cRed1d = CRCons red1d (constructModulus phi)
    where phi x = e * 2 + o + 2
              where e = x `div` 2
                    o = x `div` 2 + x `mod` 2
