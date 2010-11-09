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

import MyShow
import Terms
import PositionsAndSubterms
import SystemsOfNotation
import TransfiniteReductions
import Compression
import ExampleTermsAndSubstitutions
import ExampleRulesAndSystems

-- Examples

instance MyShow Char where
    myshow x = [x]

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
        | otherwise = error("Predeccessor undefined")
    q  (OmegaTwoPlusOneElement n)
        | n == 0    = (\m -> OmegaTwoPlusOneElement ((2 * m) + 3))
        | n == 1    = (\m -> OmegaTwoPlusOneElement ((2 * m) + 2))
        | otherwise = error("Limit function undefined")
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
    zer
       = OmegaTwoPlusOneElement 2
    suc (OmegaTwoPlusOneElement n)
       | n == 0    = error("omega.2 does not have a successor")
       | n == 1    = OmegaTwoPlusOneElement 3
       | n == 2    = OmegaTwoPlusOneElement 4
       | otherwise = OmegaTwoPlusOneElement (n + 2)

red_1 :: Reduction Sigma Var System_a_f_x OmegaTwoPlusOne
red_1 = RConst ts (zip ps rs) zer
    where ps = step 0
              where step :: Integer -> [NatString]
                    step 0 = error "Undefined step" : step 1
                    step n
                        | even n = (1 : (ones ((n `div` 2) - 1))) : step (n + 1)
                        | odd n  = (ones ((n - 1) `div` 2)) : step (n + 1)
                            where ones 0 = []
                                  ones m = 1 : 1: (ones (m - 1))
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
                                  c_f t = function_term 'f' [(1, t)]
                                  c_g t = function_term 'g' [(1, t)]
                    term _ = error "Undefined terms"

red_2 :: Reduction Sigma Var System_a_f_x OmegaTwoPlusOne
red_2 = RConst ts (zip ps rs) zer
    where ps = step 0
              where step :: Integer -> [NatString]
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
                                  c_f t = function_term 'f' [(1, t)]
                                  c_g t = function_term 'g' [(1, t)]
                    term _ = error "Undefined terms"

red_3 :: Reduction Sigma Var System_a_f_x Omega
red_3 = RConst ts (zip ps rs) zer
    where ts = [a, f_a]
          ps = [[]]
          rs = [rule_a_to_f_a]

red_4 :: Reduction Sigma Var System_a_f_x Omega
red_4 = RConst [a] [] zer

cred_1 :: CReduction Sigma Var System_a_f_x OmegaTwoPlusOne
cred_1 = CRConst red_1 modulus
    where modulus (OmegaTwoPlusOneElement n)
              | n == 1 = (\m -> OmegaTwoPlusOneElement (4 + (m * 2)))
              | n == 2 = (\m -> OmegaTwoPlusOneElement (3 + (m * 2)))
              | otherwise = error("Invalid input to modulus")

cred_2 :: CReduction Sigma Var System_a_f_x OmegaTwoPlusOne
cred_2 = CRConst red_2 modulus
    where modulus (OmegaTwoPlusOneElement n)
              | n == 1 = (\m -> OmegaTwoPlusOneElement (4 + (m * 2)))
              | n == 2 = (\m -> OmegaTwoPlusOneElement (3 + (m * 2)))
              | otherwise = error("Invalid input to modulus")

cred_3 :: CReduction Sigma Var System_a_f_x Omega
cred_3 = CRConst red_3 modulus
    where modulus (OmegaElement n)
              | n == 0 = (\_ -> OmegaElement 1)
              | otherwise = error("Invalid input to modulus")

cred_4 :: CReduction Sigma Var System_a_f_x Omega
cred_4 = CRConst red_4 modulus
    where modulus (OmegaElement n)
              | n == 0 = (\_ -> zer)
              | otherwise = error("Invalid input to modulus")
