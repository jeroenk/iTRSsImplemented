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

-- This file defines some reductions that can be tried with the Church-Rosser
-- algorithm.

import RuleAndSystem
import TransfiniteReduction
import Omega
import ChurchRosser
import ExampleTermsAndSubstitutions
import ExampleRulesAndSystems

-- The combinations to try with the reductions below are the following:
--
-- fst (church_rosser System_a_f_x [(c_red_1a, c_red_1b), (c_red_1c, c_red_1d)])
-- snd (church_rosser System_a_f_x [(c_red_1a, c_red_1b), (c_red_1c, c_red_1d)])

-- a -> f(a) -> f^2(a) -> ... -> f^n(a) -> ...
red_1a :: OmegaReduction Sigma Var System_a_f_x
red_1a = RCons (construct_sequence terms) (construct_sequence steps)
    where terms = rewrite_steps a steps
          steps = zip ps rs
          ps = iterate (\p -> 1:p) []
          rs = repeat rule_a_to_f_a

c_red_1a :: CReduction Sigma Var System_a_f_x
c_red_1a = CRCons red_1a (construct_modulus phi)
    where phi x = x + 1

-- f^\omega
red_1b :: OmegaReduction Sigma Var System_a_f_x
red_1b = RCons (construct_sequence [f_omega]) (construct_sequence [])

c_red_1b :: CReduction Sigma Var System_a_f_x
c_red_1b = CRCons red_1b (construct_modulus phi)
    where phi _ = 0

-- f^omega -> g(f^\omega) -> g(f(g(f^\omega))) -> ... -> (gf)^n(f^\omega) -> ...
red_1c :: OmegaReduction Sigma Var System_a_f_x
red_1c = RCons (construct_sequence terms) (construct_sequence steps)
    where terms = rewrite_steps f_omega steps
          steps = zip ps rs
          ps = iterate (\p -> 1:1:p) []
          rs = repeat rule_f_x_to_g_x

c_red_1c :: CReduction Sigma Var System_a_f_x
c_red_1c = CRCons red_1c (construct_modulus phi)
    where phi x = x + 1

-- a -> f(a) -> g(a) -> g(f(a)) -> g(f(f(a))) -> g(f(g(a))) -> ... -> (gf)^n(a)
--        -> (gf)^n(f(a)) -> (gf)^n(g(a)) -> ...
red_1d :: OmegaReduction Sigma Var System_a_f_x
red_1d = RCons (construct_sequence terms) (construct_sequence steps)
    where terms = rewrite_steps a steps
          steps = zip ps rs
          ps = [] : [] : [1] : (map (\p -> 1:1:p) ps)
          rs = rule_a_to_f_a : rule_f_x_to_g_x : rule_a_to_f_a : rs

c_red_1d :: CReduction Sigma Var System_a_f_x
c_red_1d = CRCons red_1d (construct_modulus phi)
    where phi x = e * 2 + o + 2
              where e = x `div` 2
                    o = x `div` 2 + x `mod` 2
