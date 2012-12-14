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

-- This module defines some reductions that can be tried with the parallel and
-- depth-left standardisation algorithms.

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

-- The reductions cRed1 up until cRed5 originate from CompressionExamples. See
-- that module for the definitions of these reductions. In the context of
-- parallel standardisation, the following can be tried in combination with
-- these reductions.
--
--     standardisation Parallel system_a_f_x cRed1
--     finalTerm $ standardisation Parallel system_a_f_x cRed2
--     standardisation Parallel system_a_f_x cRed3
--     standardisation Parallel system_a_f_x cRed4
--     standardisation Parallel system_a_f_x_omega cRed5
--     finalTerm $ standardisation Parallel system_a_f_x_omega cRed5
--
-- Parallel can in each case be replaced by DepthLeft to obtain depth-left
-- standardisation. For example,
--
--     standardisation DepthLeft system_a_f_x cRed1
--

--
-- a -> f(a) -> f(b) -> g(b) -> c
--
-- To obtain the compressed and standard forms of this reduction input:
--
--     compression system_a_f_x_g_b_h_b_a cRed6
--     standardisation Parallel system_a_f_x_g_b_h_b_a cRed6
--     standardisation DepthLeft system_a_f_x_g_b_h_b_a cRed6
--
-- As can be seen, more re-ordering of reduction steps takes place in the case
-- of standardisation than in the case of compression. Note that there is no
-- difference between parallel and depth-left standardisation here.
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

--
-- h(a,a) -> h(a,f(a)) -> h(a,f(b)) -> h(b,f(b))
--
-- To obtain the parallel and depth-left standard forms of this reduction input:
--
--     standardisation Parallel system_a_f_x_g_b_h_b_a cRed7
--     standardisation DepthLeft system_a_f_x_g_b_h_b_a cRed7
--
-- As can be seen, depth-left standardisation gives preference to the left-most
-- redex at least depth, while parallel standardisation only gives preference
-- to redexes at least depth.
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

--
-- h(h(a,a),h(a,a)) -> h(h(a,a),h(b,a)) -> h(h(a,f(a)),h(b,a))
--     -> h(h(a,f(b)),h(b,a)) -> h(h(b,f(b)),h(b,a)) -> h(h(b,a),h(b,a))
--         -> h(a,h(b,a)) -> h(b,h(b,a)) -> h(b,a) -> a
--
-- To obtain the parallel and depth-left standard forms of this reduction input:
--
--     standardisation Parallel system_a_f_x_g_b_h_b_a cRed8
--     standardisation DepthLeft system_a_f_x_g_b_h_b_a cRed8
--
-- This (slightly involved) example demonstrates one property of each of the
-- standardisation algorithms:
--
-- * For parallel standardisation it demonstrates that the algorithm works
--   backwards through the needed steps it finds. Witness that all steps in
--   the subterm at position 2 are moved as far to the front of the reduction
--   as possible, because the penultimate step of cRed8 occurs at this position.
--
-- * For depth-left standardisation it demonstrates the recursion present in
--   the algorithm, not only reordering parallel steps in a depth-left order,
--   but also ensuring that each of the steps needed to create any one of these
--   parallel steps are ordered as such.
--
red8 :: Omega2Reduction Sigma Var System_a_f_x_g_b_h_b_a
red8 = RCons ts ss
    where ts = constructSequence terms []
          ss = constructSequence steps []
          terms = rewriteSteps (h h_a_a h_a_a) steps
          steps = zip ps rs
          ps = [[2, 1], [1, 2], [1, 2, 1], [1, 1], [1, 2], [1], [1], [2], []]
          rs = [rule_a_to_b, rule_a_to_f_a, rule_a_to_b, rule_a_to_b,
                    rule_f_x_to_a, rule_h_b_a_to_a, rule_a_to_b,
                    rule_h_b_a_to_a, rule_h_b_a_to_a]

cRed8 :: CReduction Sigma Var System_a_f_x_g_b_h_b_a
cRed8 = CRCons red8 phi
    where phi (OmegaElement 0) _ = OmegaElement 9
          phi _ _                = error "Illegal modulus"
