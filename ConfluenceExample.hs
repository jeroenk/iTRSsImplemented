{-
Copyright (C) 2010 Jeroen Ketema and Jakob Grue Simonsen

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

import MyShow
import RulesAndSystems
import OmegaReductions
import Confluence
import ExampleTermsAndSubstitutions
import ExampleRulesAndSystems

-- The following is needed to display the reductions.
instance MyShow Char where
    myshow x = [x]

-- f^omega -> g(f^omega) -> g^2(f^omega) -> .. -> g^n(f^omega) -> ...
red_1a :: Reduction Sigma Var System_a_f_x
red_1a = RConst ts (zip ps rs)
    where ps = (iterate (\ns -> 1:ns) [])
          rs = repeat rule_f_x_to_g_x
          ts = rewrite_steps (f_omega) (zip ps rs)

c_red_1a :: CReduction Sigma Var System_a_f_x
c_red_1a = CRConst red_1a (\x -> succ x)

-- f^omega -> g(f^\omega) -> g(f(g(f^\omega))) -> ... -> (gf)^n(f^\omega) -> ...
red_1b :: Reduction Sigma Var System_a_f_x
red_1b = RConst ts (zip ps rs)
    where ps = []:(map (\p -> 1:1:p) ps)
          rs = rule_f_x_to_g_x:rs
          ts = rewrite_steps f_omega (zip ps rs)

c_red_1b :: CReduction Sigma Var System_a_f_x
c_red_1b = CRConst red_1b (\x -> succ x)

-- f^omega -> (fg)(f^\omega) -> (fg)^2(f^\omega))) -> ...
--                                             -> (fg)^n(f^\omega) -> ...
red_1c :: Reduction Sigma Var System_a_f_x
red_1c = RConst ts (zip ps rs)
    where ps = [1]:(map (\p -> 1:1:p) ps)
          rs = rule_f_x_to_g_x:rs
          ts = rewrite_steps f_omega (zip ps rs)

c_red_1c :: CReduction Sigma Var System_a_f_x
c_red_1c = CRConst red_1c (\x -> x)

-- f(a) -> h(a, f(a)) -> h(a, h(a, f(a))) -> h(a, h(a, h(a, f(a))))
red_2a :: Reduction Sigma Var System_a_b_f_x
red_2a = RConst ts (zip ps rs)
    where ps = [[], [2], [2,2]]
          rs = [rule_f_x_to_h_x_f_x, rule_f_x_to_h_x_f_x, rule_f_x_to_h_x_f_x]
          ts = rewrite_steps (f_a) (zip ps rs)

c_red_2a :: CReduction Sigma Var System_a_b_f_x
c_red_2a = CRConst red_2a (\x -> min 3 (succ x))

-- f(a) -> f(b) -> f(c)
red_2b :: Reduction Sigma Var System_a_b_f_x
red_2b = RConst ts (zip ps rs)
    where ps = [[1], [1]]
          rs = [rule_a_to_b, rule_b_to_c]
          ts = rewrite_steps (f_a) (zip ps rs)

c_red_2b :: CReduction Sigma Var System_a_b_f_x
c_red_2b = CRConst red_2b (\x -> if x == 0 then 0 else 2)

-- f(f(a)) -> f(f(b))
red_3a :: Reduction Sigma Var System_a_b_f_x
red_3a = RConst ts (zip ps rs)
    where ps = [[1, 1]]
          rs = [rule_a_to_b]
          ts = rewrite_steps f_f_a (zip ps rs)

c_red_3a :: CReduction Sigma Var System_a_b_f_x
c_red_3a = CRConst red_3b (\x -> if x == 0 || x == 1 then 0 else 1)

-- f(f(a)) -> f(g(a))
red_3b :: Reduction Sigma Var System_a_b_f_x
red_3b = RConst ts (zip ps rs)
    where ps = [[1]]
          rs = [rule_f_x_to_g_x]
          ts = rewrite_steps f_f_a (zip ps rs)

c_red_3b :: CReduction Sigma Var System_a_b_f_x
c_red_3b = CRConst red_3b (\x -> if x == 0 then 0 else 1)

-- final_term (fst (confluence Sys1 (c_red_6, c_red_7)))
-- final_term (snd (confluence Sys1 (c_red_6, c_red_7)))
