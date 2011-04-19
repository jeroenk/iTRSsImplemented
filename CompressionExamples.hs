{-
Copyright (C) 2010, 2011 Jeroen Ketema and Jakob Grue Simonsen

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
import TransfiniteReduction
import Omega2
import Compression
import ExampleTermsAndSubstitutions
import ExampleRulesAndSystems

-- a -> f(a) -> f^2(a) -> ... -> f^n(a) -> ...
--        f^omega -> g(f^omega) -> g^2(f^omega) -> ... -> g^n(f^omega) -> ...
--
-- The compressed reduction obtained through the compression algorithm can be
-- obtained through
--
--     compression System_a_f_x c_red_1
--
-- As can be seen the compressed reduction alternates between a -> f(a) steps
-- and f(x) -> g(x) steps.
red_1 :: Omega2Reduction Sigma Var System_a_f_x
red_1 = RCons ts ss
    where ts = construct_sequence terms_1 terms_2
          ss = construct_sequence steps_1 steps_2
          terms_1 = rewrite_steps a steps_1
          steps_1 = zip ps_1 rs_1
          ps_1 = iterate (\p -> 1:p) []
          rs_1 = repeat rule_a_to_f_a
          terms_2 = rewrite_steps f_omega steps_2
          steps_2 = zip ps_2 rs_2
          ps_2 = iterate (\p -> 1:p) []
          rs_2 = repeat rule_f_x_to_g_x

c_red_1 :: CReduction Sigma Var System_a_f_x
c_red_1 = CRCons red_1 phi
    where phi (OmegaElement 0) m  = Omega2Element (m + 1)
          phi (Omega2Element 0) m = OmegaElement (m + 1)
          phi _ _                 = error "Illegal modulus"

-- f^omega -> (fg)(f^\omega) -> (fg)^2(f^\omega))) -> ...
--                                             -> (fg)^n(f^\omega) -> ...
--    (fg)^omega -> g^2((fg)^omega) -> g^3((fg^omega)) -> ...
--                                                 -> g^(2n)((fg)^omega) -> ...
--
-- To obtain the final term of the compressed reduction peform
--
--     final_term (compression System_a_f_x c_red_2)
red_2 :: Omega2Reduction Sigma Var System_a_f_x
red_2 = RCons ts ss
    where ts = construct_sequence terms_1 terms_2
          ss = construct_sequence steps_1 steps_2
          terms_1 = rewrite_steps f_omega steps_1
          steps_1 = zip ps_1 rs_1
          ps_1 = iterate (\p -> 1:1:p) [1]
          rs_1 = repeat rule_f_x_to_g_x
          terms_2 = rewrite_steps f_g_omega steps_2
          steps_2 = zip ps_2 rs_2
          ps_2 = iterate (\p -> 1:1:p) []
          rs_2 = repeat rule_f_x_to_g_x

c_red_2 :: CReduction Sigma Var System_a_f_x
c_red_2 = CRCons red_2 phi
    where phi (OmegaElement 0) m  = Omega2Element (m + 1)
          phi (Omega2Element 0) m = OmegaElement m
          phi _ _                 = error "Illegal modulus"

-- f(a) -> f(f(a)) -> g(f(a)) -> g(g(a))
--
-- Compression of the following reduction demonstrates the compression
-- algorithm re-orders the redutions steps in such a way that the steps
-- at least depth are performed first.
red_3 :: Omega2Reduction Sigma Var System_a_f_x
red_3 = RCons ts ss
    where ts = construct_sequence terms []
          ss = construct_sequence steps []
          terms = [f_a, f_f_a, g_f_a, g_g_a]
          steps = zip ps rs
          ps = [[1], [], [1]]
          rs = [rule_a_to_f_a, rule_f_x_to_g_x, rule_f_x_to_g_x]

c_red_3 :: CReduction Sigma Var System_a_f_x
c_red_3 = CRCons red_3 phi
    where phi (OmegaElement 0) m = OmegaElement (if m == 0 then 2 else 3)
          phi _ _                = error "Illegal modulus"

-- f_omega
--
-- Compression of the following reduction demonstrates an edge case.
red_4 :: Omega2Reduction Sigma Var System_a_f_x
red_4 = RCons (construct_sequence [f_omega] []) (construct_sequence [] [])

c_red_4 :: CReduction Sigma Var System_a_f_x
c_red_4 = CRCons red_4 phi
    where phi (OmegaElement 0) _ = OmegaElement 0
          phi _ _                = error "Illegal modulus"
