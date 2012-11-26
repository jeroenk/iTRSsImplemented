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

-- This file defines some reductions that can be tried with the compression
-- algorithm.

import RuleAndSystem
import Reduction
import Omega2
import Compression
import ExampleTermsAndSubstitutions
import ExampleRulesAndSystems

import Prelude

--
-- a -> f(a) -> f^2(a) -> ... -> f^n(a) -> ...
--    f^omega -> g(f^omega) -> g^2(f^omega) -> ... -> g^n(f^omega) -> ...
--
-- To obtain the compressed reduction input:
--
--     compression system_a_f_x cRed1
--
-- As can be seen, the compressed reduction alternates between a -> f(a) steps
-- and f(x) -> g(x) steps.
red1 :: Omega2Reduction Sigma Var System_a_f_x
red1 = RCons ts ss
    where ts = constructSequence terms_1 terms_2
          ss = constructSequence steps_1 steps_2
          terms_1 = rewriteSteps a steps_1
          steps_1 = zip ps_1 rs_1
          ps_1 = iterate (\p -> 1 : p) []
          rs_1 = repeat rule_a_to_f_a
          terms_2 = rewriteSteps f_omega steps_2
          steps_2 = zip ps_2 rs_2
          ps_2 = iterate (\p -> 1:p) []
          rs_2 = repeat rule_f_x_to_g_x

cRed1 :: CReduction Sigma Var System_a_f_x
cRed1 = CRCons red1 phi
    where phi (OmegaElement 0)  m = Omega2Element (m + 1)
          phi (Omega2Element 0) m = OmegaElement  (m + 1)
          phi _ _                 = error "Illegal modulus"

--
-- f^omega -> (fg)(f^\omega) -> (fg)^2(f^\omega))) -> ...
--                                             -> (fg)^n(f^\omega) -> ...
--    (fg)^omega -> g^2((fg)^omega) -> g^3((fg^omega)) -> ...
--                                                 -> g^(2n)((fg)^omega) -> ...
--
-- To obtain the final term of the compressed reduction input:
--
--     finalTerm $ compression system_a_f_x cRed2
--
red2 :: Omega2Reduction Sigma Var System_a_f_x
red2 = RCons ts ss
    where ts = constructSequence terms_1 terms_2
          ss = constructSequence steps_1 steps_2
          terms_1 = rewriteSteps f_omega steps_1
          steps_1 = zip ps_1 rs_1
          ps_1 = iterate (\p -> 1 : 1 : p) [1]
          rs_1 = repeat rule_f_x_to_g_x
          terms_2 = rewriteSteps f_g_omega steps_2
          steps_2 = zip ps_2 rs_2
          ps_2 = iterate (\p -> 1 : 1 : p) []
          rs_2 = repeat rule_f_x_to_g_x

cRed2 :: CReduction Sigma Var System_a_f_x
cRed2 = CRCons red2 phi
    where phi (OmegaElement 0)  m = Omega2Element (m + 1)
          phi (Omega2Element 0) m = OmegaElement   m
          phi _ _                 = error "Illegal modulus"

--
-- f(a) -> f(f(a)) -> g(f(a)) -> g(g(a))
--
-- Compression of following reduction demonstrates the compression algorithm
-- re-orders the redutions steps in such a way that the steps at least depth
-- are performed first. The compressed reduction is obtained with:
--
--     compression system_a_f_x cRed3
--
-- Observe that the system of notation used does not need to be as `tight' as
-- possible, but can contain many more odinals than there are steps in the
-- constructed reduction.
red3 :: Omega2Reduction Sigma Var System_a_f_x
red3 = RCons ts ss
    where ts = constructSequence terms []
          ss = constructSequence steps []
          terms = [f_a, f_f_a, g_f_a, g_g_a]
          steps = zip ps rs
          ps = [[1], [], [1]]
          rs = [rule_a_to_f_a, rule_f_x_to_g_x, rule_f_x_to_g_x]

cRed3 :: CReduction Sigma Var System_a_f_x
cRed3 = CRCons red3 phi
    where phi (OmegaElement 0) m = OmegaElement (if m == 0 then 2 else 3)
          phi _ _                = error "Illegal modulus"

--
-- f^omega
--
-- Compression of the reduction demonstrates an edge case. The compressed
-- reduction is obtained with:
--
--     compression system_a_f_x cRed4
--
red4 :: Omega2Reduction Sigma Var System_a_f_x
red4 = RCons (constructSequence [f_omega] []) (constructSequence [] [])

cRed4 :: CReduction Sigma Var System_a_f_x
cRed4 = CRCons red4 phi
    where phi (OmegaElement 0) _ = OmegaElement 0
          phi _ _                = error "Illegal modulus"

--
-- a -> f(a) -> f^2(a) -> ... -> f^n(a) -> ... f^omega -> s = h(f^omega, s)
--
-- Compression of reductions that employ rules with infinite right-hand sides.
-- The compressed reduction is obtained with:
--
--     compression system_a_f_x_omega cRed5
--
-- The final term is obtained with:
--
--     finalTerm $ compression system_a_f_x_omega cRed5
--
-- Observe that the third term of the compressed reduction is infinite and,
-- hence, the full reduction can never be shown.
red5 :: Omega2Reduction Sigma Var System_a_f_x_omega
red5 = RCons ts ss
    where ts = constructSequence terms_1 terms_2
          ss = constructSequence steps_1 steps_2
          terms_1 = rewriteSteps a steps_1
          steps_1 = zip ps_1 rs_1
          ps_1 = iterate (\p -> 1 : p) []
          rs_1 = repeat rule_a_to_f_a
          terms_2 = rewriteSteps f_omega steps_2
          steps_2 = [([], rule_f_x_to_h_x_omega)]

cRed5 :: CReduction Sigma Var System_a_f_x_omega
cRed5 = CRCons red5 phi
    where phi (OmegaElement 0)  _ = Omega2Element 1
          phi (Omega2Element 0) m = OmegaElement (m + 1)
          phi _ _                 = error "Illegal modulus"
