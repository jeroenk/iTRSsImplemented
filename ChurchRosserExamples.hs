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

-- This file defines some reductions that can be tried with the Church-Rosser
-- algorithm.

import RuleAndSystem
import OmegaReduction
import ChurchRosser
import ExampleTermsAndSubstitutions
import ExampleRulesAndSystems

-- The combinations to try with the reductions below are the following:
--
-- fst (church_rosser System_a_f_x [(c_red_1a, c_red_1b), (c_red_1c, c_red_1d)])
-- snd (church_rosser System_a_f_x [(c_red_1a, c_red_1b), (c_red_1c, c_red_1d)])

-- a -> f(a) -> f^2(a) -> ... -> f^n(a) -> ...
red_1a :: Reduction Sigma Var System_a_f_x
red_1a = RCons ts (zip ps rs)
    where ps = iterate (\p -> 1:p) []
          rs = rule_a_to_f_a : rs
          ts = rewrite_steps a (zip ps rs)

c_red_1a :: CReduction Sigma Var System_a_f_x
c_red_1a = CRCons red_1a (\x -> x + 1)

-- f^\omega
red_1b :: Reduction Sigma Var System_a_f_x
red_1b = RCons [f_omega] []

c_red_1b :: CReduction Sigma Var System_a_f_x
c_red_1b = CRCons red_1b (\_ -> 0)

-- f^omega -> g(f^\omega) -> g(f(g(f^\omega))) -> ... -> (gf)^n(f^\omega) -> ...
red_1c :: Reduction Sigma Var System_a_f_x
red_1c = RCons ts (zip ps rs)
    where ps = iterate (\p -> 1:1:p) []
          rs = rule_f_x_to_g_x : rs
          ts = rewrite_steps f_omega (zip ps rs)

c_red_1c :: CReduction Sigma Var System_a_f_x
c_red_1c = CRCons red_1c (\x -> x + 1)

-- a -> f(a) -> g(a) -> g(f(a)) -> g(f(f(a))) -> g(f(g(a))) -> ... -> (gf)^n(a)
--        -> (gf)^n(f(a)) -> (gf)^n(g(a)) -> ...
red_1d :: Reduction Sigma Var System_a_f_x
red_1d = RCons ts (zip ps rs)
    where ps = [] : [] : [1] : (map (\p -> 1:1:p) ps)
          rs = rule_a_to_f_a : rule_f_x_to_g_x : rule_a_to_f_a : rs
          ts = rewrite_steps a (zip ps rs)

c_red_1d :: CReduction Sigma Var System_a_f_x
c_red_1d = CRCons red_1d modulus
    where modulus n = e * 2 + o + 2
              where e = n `div` 2
                    o = n `div` 2 + n `mod` 2
