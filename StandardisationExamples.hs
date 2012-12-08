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

-- This file defines some reductions that can be tried with the standardisation
-- algorithm.

import RuleAndSystem
import Reduction
import Omega2
import Compression
import Standardisation
import ExampleTermsAndSubstitutions
import ExampleRulesAndSystems

import Prelude

--
-- a -> f(a) -> f(b) -> g(b) -> c
--
--     compression system_a_a_f_x_g_b cRed
--     standardisation system_a_a_f_x_g_b cRed
--
red :: Omega2Reduction Sigma Var System_a_a_f_x_g_b
red = RCons ts ss
    where ts = constructSequence terms []
          ss = constructSequence steps []
          terms = [a, f_a, f_b, g_b, c]
          steps = zip ps rs
          ps = [[], [1], [], []]
          rs = [rule_a_to_f_a, rule_a_to_b, rule_f_x_to_g_x, rule_g_b_to_c]

cRed :: CReduction Sigma Var System_a_a_f_x_g_b
cRed = CRCons red phi
    where phi (OmegaElement 0) m = OmegaElement 4
          phi _ _                = error "Illegal modulus"
