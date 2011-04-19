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

-- This file defines some reductions that can be tried with the confluence
-- algorithm.

import RuleAndSystem
import Reduction
import Omega
import Confluence
import ExampleTermsAndSubstitutions
import ExampleRulesAndSystems

-- The next three reductions start in f^omega. Interesting combinations to try
-- are:
--
-- fst (confluence system_a_f_x (c_red_1a, c_red_1b))
-- snd (confluence system_a_f_x (c_red_1a, c_red_1b))
-- final_term (fst (confluence system_a_f_x (c_red_1b, c_red_1c)))
-- final_term (snd (confluence system_a_f_x (c_red_1b, c_red_1c)))

-- f^omega -> g(f^omega) -> g^2(f^omega) -> .. -> g^n(f^omega) -> ...
red_1a :: OmegaReduction Sigma Var System_a_f_x
red_1a = RCons (construct_sequence terms) (construct_sequence steps)
    where terms = rewrite_steps (f_omega) steps
          steps = zip ps rs
          ps = iterate (\p -> 1:p) []
          rs = repeat rule_f_x_to_g_x

c_red_1a :: CReduction Sigma Var System_a_f_x
c_red_1a = CRCons red_1a (construct_modulus phi)
    where phi x = x + 1

-- f^omega -> g(f^\omega) -> g(f(g(f^\omega))) -> ... -> (gf)^n(f^\omega) -> ...
red_1b :: OmegaReduction Sigma Var System_a_f_x
red_1b = RCons (construct_sequence terms) (construct_sequence steps)
    where terms = rewrite_steps f_omega steps
          steps = zip ps rs
          ps = iterate (\p -> 1:1:p) []
          rs = repeat rule_f_x_to_g_x

c_red_1b :: CReduction Sigma Var System_a_f_x
c_red_1b = CRCons red_1b (construct_modulus phi)
    where phi x = x + 1

-- f^omega -> (fg)(f^\omega) -> (fg)^2(f^\omega))) -> ...
--                                             -> (fg)^n(f^\omega) -> ...
red_1c :: OmegaReduction Sigma Var System_a_f_x
red_1c = RCons (construct_sequence terms) (construct_sequence steps)
    where terms = rewrite_steps f_omega steps
          steps = zip ps rs
          ps = iterate (\p -> 1:1:p) [1]
          rs = repeat rule_f_x_to_g_x

c_red_1c :: CReduction Sigma Var System_a_f_x
c_red_1c = CRCons red_1c (construct_modulus phi)
    where phi x = x

-- The next two finite reductions start in f(a). These reductions demonstrate
-- that the confluence algorithm also applies in the finite case. The two
-- obvious combinations are:
--
-- fst (confluence system_a_b_f_x (c_red_2a, c_red_2b))
-- snd (confluence system_a_b_f_x (c_red_2a, c_red_2b))

-- f(a) -> h(a, f(a)) -> h(a, h(a, f(a))) -> h(a, h(a, h(a, f(a))))
red_2a :: OmegaReduction Sigma Var System_a_b_f_x
red_2a = RCons (construct_sequence terms) (construct_sequence steps)
    where terms = rewrite_steps (f_a) steps
          steps = zip ps rs
          ps = [[], [2], [2,2]]
          rs = [rule_f_x_to_h_x_f_x, rule_f_x_to_h_x_f_x, rule_f_x_to_h_x_f_x]

c_red_2a :: CReduction Sigma Var System_a_b_f_x
c_red_2a = CRCons red_2a (construct_modulus phi)
     where phi x = min 3 (x + 1)

-- f(a) -> f(b) -> f(c)
red_2b :: OmegaReduction Sigma Var System_a_b_f_x
red_2b = RCons (construct_sequence terms) (construct_sequence steps)
    where terms = rewrite_steps f_a steps
          steps = zip ps rs
          ps = [[1], [1]]
          rs = [rule_a_to_b, rule_b_to_c]

c_red_2b :: CReduction Sigma Var System_a_b_f_x
c_red_2b = CRCons red_2b (construct_modulus phi)
    where phi x = if x == 0 then 0 else 2

-- The next two reductions test for an edge case where the top-most function
-- symbol is not touched in either reduction.  The two
-- obvious combinations are:
--
-- fst (confluence system_a_b_f_x (c_red_3a, c_red_3b))
-- snd (confluence system_a_b_f_x (c_red_3a, c_red_3b))

-- f(f(a)) -> f(f(b))
red_3a :: OmegaReduction Sigma Var System_a_b_f_x
red_3a = RCons (construct_sequence terms) (construct_sequence steps)
    where terms = rewrite_steps f_f_a steps
          steps = zip ps rs
          ps = [[1, 1]]
          rs = [rule_a_to_b]

c_red_3a :: CReduction Sigma Var System_a_b_f_x
c_red_3a = CRCons red_3a (construct_modulus phi)
    where phi x = if x == 0 || x == 1 then 0 else 1

-- f(f(a)) -> f(g(a))
red_3b :: OmegaReduction Sigma Var System_a_b_f_x
red_3b = RCons (construct_sequence terms) (construct_sequence steps)
    where terms = rewrite_steps f_f_a steps
          steps = zip ps rs
          ps = [[1]]
          rs = [rule_f_x_to_g_x]

c_red_3b :: CReduction Sigma Var System_a_b_f_x
c_red_3b = CRCons red_3b (construct_modulus phi)
    where phi x = if x == 0 then 0 else 1
