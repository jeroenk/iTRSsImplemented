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

-- This file defines some reductions that can be tried with the compression
-- algorithm.

import Term
import PositionAndSubterm
import SystemOfNotation
import TransfiniteReduction
import Compression
import ExampleTermsAndSubstitutions
import ExampleRulesAndSystems

-- Define an encoding of the ordinal omega.2 + 1 into natural numbers
--
-- The mapping is as follows:
--
-- 0 1 ...     n     ... omega (omega + 1) ... (omega + n) ... (omega.2)
-- | |         |           |        |               |              |
-- 2 4 ... (2.n + 2) ...   1        3      ...  (2.n + 1)  ...     0

data OmegaTwoPlusOne = OmegaTwoPlusOneElement Int

instance Show OmegaTwoPlusOne where
    show (OmegaTwoPlusOneElement n) = show n

instance SystemOfNotation OmegaTwoPlusOne where
    k (OmegaTwoPlusOneElement n)
        | n == 0    = LimitOrdinal  -- omega.2
        | n == 1    = LimitOrdinal  -- omega
        | n == 2    = ZeroOrdinal   -- 0
        | otherwise = SuccOrdinal   -- even: n; odd: omega + n
    p  (OmegaTwoPlusOneElement n)
        | n > 2     = OmegaTwoPlusOneElement (n - 2)
        | otherwise = error "Predecessor undefined"
    q  (OmegaTwoPlusOneElement n)
        | n == 0    = (\m -> OmegaTwoPlusOneElement ((2 * m) + 3))
        | n == 1    = (\m -> OmegaTwoPlusOneElement ((2 * m) + 2))
        | otherwise = error "Limit function undefined"
    to_int  (OmegaTwoPlusOneElement n)
        = n

instance UnivalSystem OmegaTwoPlusOne where
    leq  (OmegaTwoPlusOneElement m)  (OmegaTwoPlusOneElement n)
        | n == m                                   = True
        | n == 0                                   = True
        | n == 1 && m > 0              && (even m) = True
        |           m == 2                         = True
        | n > 2  && m > 2  && (odd n)  && (odd m)  = m <= n
        | n > 2  && m > 2  && (odd n)  && (even m) = True
        | n > 2  && m > 2  && (even n) && (even m) = m <= n
        | otherwise                                = False
    zer = OmegaTwoPlusOneElement 2
    suc (OmegaTwoPlusOneElement n)
       | n == 0    = error "omega.2 does not have a successor"
       | otherwise = OmegaTwoPlusOneElement (n + 2)

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

red_1 :: Reduction Sigma Var System_a_f_x OmegaTwoPlusOne
red_1 = RCons ts (zip ps rs) zer
    where ps = step 0
              where step :: Integer -> [Position]
                    step 0 = error "Undefined step" : step 1
                    step n
                        | even n = (ones ((n - 2) `div` 2)) : step (n + 1)
                        | odd n  = (ones ((n - 1) `div` 2)) : step (n + 1)
                            where ones 0 = []
                                  ones m = 1 : (ones (m - 1))
                    step _ = error "Undefined steps"
          rs = rule_a_to_f_a : rule_f_x_to_g_x : rs
          ts = term 0
              where term :: Integer -> [Term_Sigma_Var]
                    term 0 = error "Undefined term" : term 1
                    term n
                        | even n = f_n (n `div` 2 - 1) : term (n + 1)
                        | odd n  = g_n ((n - 1) `div` 2) : term (n + 1)
                            where f_n 0 = a
                                  f_n m = c_f (f_n (m - 1))
                                  g_n 0 = f_omega
                                  g_n m = c_g (g_n (m - 1))
                                  c_f t = function_term f [(1, t)]
                                  c_g t = function_term g [(1, t)]
                    term _ = error "Undefined terms"

c_red_1 :: CReduction Sigma Var System_a_f_x OmegaTwoPlusOne
c_red_1 = CRCons red_1 modulus
    where modulus (OmegaTwoPlusOneElement n)
              | n == 1 = (\m -> OmegaTwoPlusOneElement (4 + (m * 2)))
              | n == 2 = (\m -> OmegaTwoPlusOneElement (3 + (m * 2)))
              | otherwise = error "Invalid input to modulus"


-- f^omega -> (fg)(f^\omega) -> (fg)^2(f^\omega))) -> ...
--                                             -> (fg)^n(f^\omega) -> ...
--        (fg)^omega -> g^2((fg)^omega) -> ... -> g^(2n)((fg)^omega)
--
-- To obtain the final term of the compressed reduction peform
--
--     final_term (compression System_a_f_x c_red_2)

red_2 :: Reduction Sigma Var System_a_f_x OmegaTwoPlusOne
red_2 = RCons ts (zip ps rs) zer
    where ps = step 0
              where step :: Integer -> [Position]
                    step 0 = error "Undefined step" : step 1
                    step n
                        | even n = (1 : (ones ((n `div` 2) - 1))) : step (n + 1)
                        | odd n  = (ones ((n - 1) `div` 2)) : step (n + 1)
                            where ones 0 = []
                                  ones m = 1 : 1 : (ones (m - 1))
                    step _ = error "Undefined steps"
          rs = rule_f_x_to_g_x:rs
          ts = term 0
              where term :: Integer -> [Term_Sigma_Var]
                    term 0 = error "Undefined term" : term 1
                    term n
                        | even n = f_g_n ((n `div` 2) - 1) : term (n + 1)
                        | odd n  = g_g_n ((n - 1) `div` 2) : term (n + 1)
                            where f_g_n 0 = f_omega
                                  f_g_n m = (c_f (c_g (f_g_n (m - 1))))
                                  g_g_n 0 = f_g_omega
                                  g_g_n m = (c_g (c_g (g_g_n (m - 1))))
                                  c_f t = function_term f [(1, t)]
                                  c_g t = function_term g [(1, t)]
                    term _ = error "Undefined terms"

c_red_2 :: CReduction Sigma Var System_a_f_x OmegaTwoPlusOne
c_red_2 = CRCons red_2 modulus
    where modulus (OmegaTwoPlusOneElement n)
              | n == 1 = (\m -> OmegaTwoPlusOneElement (4 + (m * 2)))
              | n == 2 = (\m -> OmegaTwoPlusOneElement (3 + (m * 2)))
              | otherwise = error "Invalid input to modulus"

-- f(a) -> f(f(a)) -> g(f(a)) -> g(g(a))
--
-- Compression of the following reduction demonstrates the compression
-- algorithm re-orders the redutions steps in such a way that the steps
-- at least depth are performed first.

red_3 :: Reduction Sigma Var System_a_f_x Omega
red_3 = RCons ts (zip ps rs) zer
    where ts = [f_a, f_f_a, g_f_a, g_g_a]
          ps = [[1], [], [1]]
          rs = [rule_a_to_f_a, rule_f_x_to_g_x, rule_f_x_to_g_x]

c_red_3 :: CReduction Sigma Var System_a_f_x Omega
c_red_3 = CRCons red_3 modulus
    where modulus (OmegaElement n)
              | n == 0 = (\m -> OmegaElement (if m == 0 then 2 else 3))
              | otherwise = error "Invalid input to modulus"

-- f_omega
--
-- Compression of the following reduction demonstrates an edge case.

red_4 :: Reduction Sigma Var System_a_f_x Omega
red_4 = RCons [f_omega] [] zer

c_red_4 :: CReduction Sigma Var System_a_f_x Omega
c_red_4 = CRCons red_4 modulus
    where modulus (OmegaElement n)
              | n == 0 = (\_ -> zer)
              | otherwise = error "Invalid input to modulus"
