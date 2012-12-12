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

-- This file defines some reductions that can be tried with the confluence
-- algorithm.

import RuleAndSystem
import Reduction
import Omega
import Confluence
import ExampleTermsAndSubstitutions
import ExampleRulesAndSystems

import Prelude

-- The next three reductions start in f^omega. Interesting combinations to try
-- are:
--
--     fst $ confluence system_a_f_x (cRed1a, cRed1b)
--     snd $ confluence system_a_f_x (cRed1a, cRed1b)
--     finalTerm $ fst $ confluence system_a_f_x (cRed1b, cRed1c)
--     finalTerm $ snd $ confluence system_a_f_x (cRed1b, cRed1c)

--
-- f^omega -> g(f^omega) -> g^2(f^omega) -> .. -> g^n(f^omega) -> ...
--
red1a :: OmegaReduction Sigma Var System_a_f_x
red1a = RCons (constructSequence terms) (constructSequence steps)
    where terms = rewriteSteps f_omega steps
          steps = zip ps rs
          ps = iterate (\p -> 1 : p) []
          rs = repeat rule_f_x_to_g_x

cRed1a :: CReduction Sigma Var System_a_f_x
cRed1a = CRCons red1a (constructModulus phi)
    where phi n = n + 1

--
-- f^omega -> g(f^\omega) -> (gf)(g(f^\omega)) -> ... -> (gf)^n(f^\omega) -> ...
--
red1b :: OmegaReduction Sigma Var System_a_f_x
red1b = RCons (constructSequence terms) (constructSequence steps)
    where terms = rewriteSteps f_omega steps
          steps = zip ps rs
          ps = iterate (\p -> 1 : 1 : p) []
          rs = repeat rule_f_x_to_g_x

cRed1b :: CReduction Sigma Var System_a_f_x
cRed1b = CRCons red1b (constructModulus phi)
    where phi m = m + 1

--
-- f^omega -> (fg)(f^\omega) -> (fg)^2(f^\omega))) -> ...
--                                             -> (fg)^n(f^\omega) -> ...
--
red1c :: OmegaReduction Sigma Var System_a_f_x
red1c = RCons (constructSequence terms) (constructSequence steps)
    where terms = rewriteSteps f_omega steps
          steps = zip ps rs
          ps = iterate (\p -> 1 : 1 : p) [1]
          rs = repeat rule_f_x_to_g_x

cRed1c :: CReduction Sigma Var System_a_f_x
cRed1c = CRCons red1c (constructModulus phi)
    where phi m = m

-- The next two finite reductions start in f(a). These reductions demonstrate
-- that the confluence algorithm also applies in the finite case. The two
-- obvious combinations are:
--
--     fst $ confluence system_a_b_f_x (cRed2a, cRed2b)
--     snd $ confluence system_a_b_f_x (cRed2a, cRed2b)

--
-- f(a) -> h(a, f(a)) -> h(a, h(a, f(a))) -> h(a, h(a, h(a, f(a))))
--
red2a :: OmegaReduction Sigma Var System_a_b_f_x
red2a = RCons (constructSequence terms) (constructSequence steps)
    where terms = rewriteSteps f_a steps
          steps = zip ps rs
          ps = [[], [2], [2,2]]
          rs = [rule_f_x_to_h_x_f_x, rule_f_x_to_h_x_f_x, rule_f_x_to_h_x_f_x]

cRed2a :: CReduction Sigma Var System_a_b_f_x
cRed2a = CRCons red2a (constructModulus phi)
     where phi m = min 3 (m + 1)

--
-- f(a) -> f(b) -> f(c)
--
red2b :: OmegaReduction Sigma Var System_a_b_f_x
red2b = RCons (constructSequence terms) (constructSequence steps)
    where terms = rewriteSteps f_a steps
          steps = zip ps rs
          ps = [[1], [1]]
          rs = [rule_a_to_b, rule_b_to_c]

cRed2b :: CReduction Sigma Var System_a_b_f_x
cRed2b = CRCons red2b (constructModulus phi)
    where phi m = if m == 0 then 0 else 2

-- The next two reductions test for an edge case where the top-most function
-- symbol is not touched in either reduction.  The two
-- obvious combinations are:
--
--     fst $ confluence system_a_b_f_x (cRed3a, cRed3b)
--     snd $ confluence system_a_b_f_x (cRed3a, cRed3b)

--
-- f(f(a)) -> f(f(b))
--
red3a :: OmegaReduction Sigma Var System_a_b_f_x
red3a = RCons (constructSequence terms) (constructSequence steps)
    where terms = rewriteSteps f_f_a steps
          steps = zip ps rs
          ps = [[1, 1]]
          rs = [rule_a_to_b]

cRed3a :: CReduction Sigma Var System_a_b_f_x
cRed3a = CRCons red3a (constructModulus phi)
    where phi m = if m `elem` [0, 1] then 0 else 1

--
-- f(f(a)) -> f(g(a))
--
red3b :: OmegaReduction Sigma Var System_a_b_f_x
red3b = RCons (constructSequence terms) (constructSequence steps)
    where terms = rewriteSteps f_f_a steps
          steps = zip ps rs
          ps = [[1]]
          rs = [rule_f_x_to_g_x]

cRed3b :: CReduction Sigma Var System_a_b_f_x
cRed3b = CRCons red3b (constructModulus phi)
    where phi n = if n == 0 then 0 else 1

-- The next two reductions start in a. These reductions demonstrate that the
-- confluence algorithm can deal with rules that have infinite right-hand
-- sides. The obvious (although not very informative) combinations are:
--
--     finalTerm $ fst $ confluence system_a_f_x_omega (cRed4a, cRed4b)
--     finalTerm $ snd $ confluence system_a_f_x_omega (cRed4a, cRed4b)

--
-- a -> f(a) -> f^2(a) -> ... -> f^n(a) -> ...
--
red4a :: OmegaReduction Sigma Var System_a_f_x_omega
red4a = RCons (constructSequence terms) (constructSequence steps)
    where terms = rewriteSteps a steps
          steps = zip ps rs
          ps = iterate (\p -> 1 : p) []
          rs = repeat rule_a_to_f_a

cRed4a :: CReduction Sigma Var System_a_f_x_omega
cRed4a = CRCons red4a (constructModulus phi)
    where phi m = m + 1

--
-- a -> f(a) -> s = h(a, s)
--
red4b :: OmegaReduction Sigma Var System_a_f_x_omega
red4b = RCons (constructSequence terms) (constructSequence steps)
    where terms = rewriteSteps a steps
          steps = zip ps rs
          ps = [[], []]
          rs = [rule_a_to_f_a, rule_f_x_to_h_x_omega]

cRed4b :: CReduction Sigma Var System_a_f_x_omega
cRed4b = CRCons red4b (constructModulus phi)
    where phi _ = 2
