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

-- f(a) -> f^2(a) -> f^3(a) -> ... -> f^n(a) -> ...
red_1 :: Reduction Sigma Var System_a_f_x
red_1 = RConst ts (zip ps rs)
    where ps = (iterate (\ns -> 1:ns) [1])
          rs = repeat rule_a_to_f_a
          ts = rewrite_steps (f_a) (zip ps rs)

cred_1 :: CReduction Sigma Var System_a_f_x
cred_1 = CRConst red_1 (\x -> succ x)

-- f^omega -> g(f^omega) -> g^2(f^omega) -> .. -> g^n(f^omega) -> ...
red_2 :: Reduction Sigma Var System_a_f_x
red_2 = RConst ts (zip ps rs)
    where ps = (iterate (\ns -> 1:ns) [])
          rs = repeat rule_f_x_to_g_x
          ts = rewrite_steps (f_omega) (zip ps rs)

cred_2 :: CReduction Sigma Var System_a_f_x
cred_2 = CRConst red_2 (\x -> succ x)

-- f^omega -> g(f^\omega) -> g(f(g(f^\omega))) -> ... -> (gf)^n(f^\omega) -> ...
red_6 :: Reduction Sigma Var System_a_f_x
red_6 = RConst ts (zip ps rs)
    where ps = []:(map (\p -> 1:1:p) ps)
          rs = rule_f_x_to_g_x:rs
          ts = rewrite_steps f_omega (zip ps rs)

cred_6 :: CReduction Sigma Var System_a_f_x
cred_6 = CRConst red_6 (\x -> succ x)

-- f^omega -> (fg)(f^\omega) -> (fg)^2(f^\omega))) -> ...
--                                             -> (fg)^n(f^\omega) -> ...
red_7 :: Reduction Sigma Var System_a_f_x
red_7 = RConst ts (zip ps rs)
    where ps = [1]:(map (\p -> 1:1:p) ps)
          rs = rule_f_x_to_g_x:rs
          ts = rewrite_steps f_omega (zip ps rs)

cred_7 :: CReduction Sigma Var System_a_f_x
cred_7 = CRConst red_7 (\x -> x)

-- a
red_8 :: Reduction Sigma Var System_a_f_x
red_8 = RConst [a] []

cred_8 :: CReduction Sigma Var System_a_f_x
cred_8 = CRConst red_8 (\_ -> 0)

-- f(a) -> h(a, f(a)) -> h(a, h(a, f(a))) -> h(a, h(a, h(a, f(a))))
red_4 :: Reduction Sigma Var System_a_b_f_x
red_4 = RConst ts (zip ps rs)
    where ps = [[], [2], [2,2]]
          rs = [rule_f_x_to_h_x_f_x, rule_f_x_to_h_x_f_x, rule_f_x_to_h_x_f_x]
          ts = rewrite_steps (f_a) (zip ps rs)

cred_4 :: CReduction Sigma Var System_a_b_f_x
cred_4 = CRConst red_4 (\x -> min 3 (succ x))

-- f(a) -> f(b) -> f(c)
red_5 :: Reduction Sigma Var System_a_b_f_x
red_5 = RConst ts (zip ps rs)
    where ps = [[1], [1]]
          rs = [rule_a_to_b, rule_b_to_c]
          ts = rewrite_steps (f_a) (zip ps rs)

cred_5 :: CReduction Sigma Var System_a_b_f_x
cred_5 = CRConst red_5 (\x -> if x == 0 then 0 else 2)

-- f(f(a)) -> f(f(b))
red_9 :: Reduction Sigma Var System_a_b_f_x
red_9 = RConst ts (zip ps rs)
    where ps = [[1, 1]]
          rs = [rule_a_to_b]
          ts = rewrite_steps f_f_a (zip ps rs)

cred_9 :: CReduction Sigma Var System_a_b_f_x
cred_9 = CRConst red_9 (\x -> if x == 0 || x == 1 then 0 else 1)

-- f(f(a)) -> f(g(a))
red_10 :: Reduction Sigma Var System_a_b_f_x
red_10 = RConst ts (zip ps rs)
    where ps = [[1]]
          rs = [rule_f_x_to_g_x]
          ts = rewrite_steps f_f_a (zip ps rs)

cred_10 :: CReduction Sigma Var System_a_b_f_x
cred_10 = CRConst red_10 (\x -> if x == 0 then 0 else 1)

-- final_term (fst (confluence Sys1 (cred_6, cred_7)))
-- final_term (snd (confluence Sys1 (cred_6, cred_7)))