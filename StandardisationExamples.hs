{-
Copyright (C) 2012 Jeroen Ketema

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

-- This module defines some reductions that can be tried with the
-- standardisation algorithms.

module StandardisationExamples (
    cRed1, cRed2, cRed3,
    cRed4, cRed5, cRed6,
    cRed7, cRed8,
    compression, standardisation
) where

import RuleAndSystem
import Reduction
import Omega2
import Compression
import Standardisation
import ExampleTermsAndSubstitutions
import ExampleRulesAndSystems
import CompressionExamples

import Prelude

--
-- a -> f(a) -> f(b) -> g(b) -> c
--
--     compression system_a_a_f_x_g_b cRed
--     standardisation system_a_a_f_x_g_b cRed
--
red6 :: Omega2Reduction Sigma Var System_a_f_x_g_b_h_b_a
red6 = RCons ts ss
    where ts = constructSequence terms []
          ss = constructSequence steps []
          terms = rewriteSteps a steps
          steps = zip ps rs
          ps = [[], [1], [], []]
          rs = [rule_a_to_f_a, rule_a_to_b, rule_f_x_to_g_x, rule_g_b_to_c]

cRed6 :: CReduction Sigma Var System_a_f_x_g_b_h_b_a
cRed6 = CRCons red6 phi
    where phi (OmegaElement 0) _ = OmegaElement 4
          phi _ _                = error "Illegal modulus"

red7 :: Omega2Reduction Sigma Var System_a_f_x_g_b_h_b_a
red7 = RCons ts ss
    where ts = constructSequence terms []
          ss = constructSequence steps []
          terms = rewriteSteps h_a_a steps
          steps = zip ps rs
          ps = [[2], [2, 1], [1]]
          rs = [rule_a_to_f_a, rule_a_to_b, rule_a_to_b]

cRed7 :: CReduction Sigma Var System_a_f_x_g_b_h_b_a
cRed7 = CRCons red7 phi
    where phi (OmegaElement 0) _ = OmegaElement 3
          phi _ _                = error "Illegal modulus"

-- Demonstrates for parallel strategy that we works backwards to the needed
-- steps that were found.
-- Demonstrates for depth-left strategy that this works recursively.
red8 :: Omega2Reduction Sigma Var System_a_f_x_g_b_h_b_a
red8 = RCons ts ss
    where ts = constructSequence terms []
          ss = constructSequence steps []
          terms = rewriteSteps (h h_a_a h_a_a) steps
          steps = zip ps rs
          ps = [[2, 1], [1, 2], [1, 2, 1], [1, 1], [1, 2], [1], [1], [2], []]
          rs = [rule_a_to_b, rule_a_to_f_a, rule_a_to_b, rule_a_to_b, rule_f_x_to_a, rule_h_b_a_to_a, rule_a_to_b, rule_h_b_a_to_a, rule_h_b_a_to_a]

cRed8 :: CReduction Sigma Var System_a_f_x_g_b_h_b_a
cRed8 = CRCons red8 phi
    where phi (OmegaElement 0) _ = OmegaElement 9
          phi _ _                = error "Illegal modulus"
