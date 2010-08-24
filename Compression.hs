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
import SignatureAndVariables
import Terms
import PositionsAndSubterms
import Substitutions
import RulesAndSystems
import SystemsOfNotation
import TransfiniteReductions

import Array

-- Compression

accumulate_essential :: (Signature s, Variables v, RewriteSystem s v r,
                         UnivalentSystem o)
    => CReduction s v r o -> Int -> [(Step s v, o)]
accumulate_essential s@(CRConst (RConst _ ps z) phi) d
    = needed_steps (pos_to_depth (final_term s) d) n (k n)
    where n = phi z d
          needed_steps qs n SuccOrdinal
              | leq n z   = []
              | otherwise = ss_new
                  where q@(q', _) = ps!!(to_int (p n))
                        qs_new = origins_across qs q
                        ss_new
                            | q' `elem` qs_new = ss' ++ [(q, p n)]
                            | otherwise        = ss'
                        ss' = needed_steps qs_new (p n) (k (p n))
          needed_steps qs n LimitOrdinal
              | leq n z   = []
              | otherwise = needed_steps qs n' (k n')
                  where n' = phi n (maximum (map length qs))
          needed_steps qs n ZeroOrdinal
              | leq n z   = []
              | otherwise = error("Greater than 0 while being equal or smaller")

filter_steps :: (Signature s, Variables v, UnivalentSystem o)
    => [(Step s v, o)] -> [(Step s v, o)] -> [Step s v]
filter_steps prev total = filter_steps' prev total []
    where filter_steps' [] left ss =  ss ++ (map fst left)
          filter_steps' prev@((s, n):prev') ((t, m):left') ss
              | (leq n m) && (leq m n)
                  = filter_steps' prev' left' (project_over [s] ss)
              | otherwise
                  = filter_steps' prev left' (ss ++ [t])
          project_over ss []
              = []
          project_over ss ((ps, r):qs)
              = ss_new ++ (project_over ss_new qs)
              where ps_add = descendants [ps] ss
                    ss_new = map (\p -> (p, r)) ps_add

compr_devel :: (Signature s, Variables v, RewriteSystem s v r,
                UnivalentSystem o)
    => CReduction s v r o -> [[Step s v]]
compr_devel s = (map fst initial) : (compr_devel' 1 initial)
    where initial
              = accumulate_essential s 0
          compr_devel' d prev
              = new : (compr_devel' (succ d) total)
                  where total = accumulate_essential s d
                        new   = filter_steps prev total

compr_steps :: (Signature s, Variables v, RewriteSystem s v r,
                UnivalentSystem o)
    => CReduction s v r o -> [Step s v]
compr_steps s = concat (compr_devel s)

compr_modulus :: (Signature s, Variables v, RewriteSystem s v r,
                  UnivalentSystem o)
    => CReduction s v r o -> (Modulus Omega)
compr_modulus s (OmegaElement n)
    | n == 0
        = (\m -> OmegaElement (length (concat (take (succ m) (compr_devel s)))))
    | otherwise
        = error("Modulus only defined for 0")

compression :: (Signature s, Variables v, RewriteSystem s v r,
                UnivalentSystem o)
    => r -> (CReduction s v r o) -> (CReduction s v r Omega)
compression r s = CRConst reduction modulus
    where reduction = RConst terms steps zer
          terms = (rewrite_steps (initial_term s) steps)
          steps = compr_steps s
          modulus = compr_modulus s

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

instance UnivalentSystem OmegaTwoPlusOne where
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

type Standard_Term         = Term Char Char
type Standard_Substitution = Substitution Char Char
type Standard_Rule         = RewriteRule Char Char

instance Signature Char where
    arity 'a' = 0
    arity 'b' = 0
    arity 'c' = 0
    arity 'f' = 1
    arity 'g' = 1
    arity 'h' = 2
    arity _   = error "Character not in signature"

instance Variables Char

a :: Standard_Term
a = constant 'a'

f_x :: Standard_Term
f_x = Function 'f' (array (1, 1) [(1, Variable 'x')])

g_x :: Standard_Term
g_x = Function 'g' (array (1, 1) [(1, Variable 'x')])

f_a :: Standard_Term
f_a = Function 'f' (array (1, 1) [(1, constant 'a')])

f_omega :: Standard_Term
f_omega = Function 'f' (array (1, 1) [(1, f_omega)])

f_g_omega :: Standard_Term
f_g_omega = Function 'f' (array (1, 1) [(1, g_f_omega)])

g_f_omega :: Standard_Term
g_f_omega = Function 'g' (array (1, 1) [(1, f_g_omega)])

rule_1 = Rule f_x g_x

rule_2 = Rule a f_a

data System_1 = Sys1

instance RewriteSystem Char Char System_1 where
    rules Sys1 = [rule_1]

data System_2 = Sys2

instance RewriteSystem Char Char System_2 where
    rules Sys2 = [rule_1, rule_2]

red_1 :: Reduction Char Char System_1 OmegaTwoPlusOne
red_1 = RConst ts (zip ps rs) zer
    where ps = step 0
              where step 0 = error("undefined step") : step 1
                    step n
                        | even n = (1 : (ones ((n `div` 2) - 1))) : step (n + 1)
                        | odd n  = (ones ((n - 1) `div` 2)) : step (n + 1)
                            where ones 0 = []
                                  ones n = 1 : 1: (ones (n - 1))
          rs = rule_1:rs
          ts = term 0
              where term 0 = error("Undefined term") : term 1
                    term n
                        | even n = f_g_n ((n `div` 2) - 1) : term (n + 1)
                        | odd n  = g_g_n ((n - 1) `div` 2) : term (n + 1)
                            where f_g_n 0 = f_omega
                                  f_g_n n = (c_f (c_g (f_g_n (n - 1))))
                                  g_g_n 0 = f_g_omega
                                  g_g_n n = (c_g (c_g (g_g_n (n - 1))))
                                  c_f t = Function 'f' (array (1, 1) [(1, t)])
                                  c_g t = Function 'g' (array (1, 1) [(1, t)])

red_2 :: Reduction Char Char System_2 OmegaTwoPlusOne
red_2 = RConst ts (zip ps rs) zer
    where ps = step 0
              where step 0 = error("undefined step") : step 1
                    step n
                        | even n = (ones ((n - 2) `div` 2)) : step (n + 1)
                        | odd n  = (ones ((n - 1) `div` 2)) : step (n + 1)
                            where ones 0 = []
                                  ones n = 1 : (ones (n - 1))
          rs = rule_2 : rule_1 : rs
          ts = term 0
              where term 0 = error("Undefined term") : term 1
                    term n
                        | even n = f_n (n `div` 2 - 1) : term (n + 1)
                        | odd n  = g_n ((n - 1) `div` 2) : term (n + 1)
                            where f_n 0 = a
                                  f_n n = c_f (f_n (n - 1))
                                  g_n 0 = f_omega
                                  g_n n = c_g (g_n (n - 1))
                                  c_f t = Function 'f' (array (1, 1) [(1, t)])
                                  c_g t = Function 'g' (array (1, 1) [(1, t)]) 

red_3 :: Reduction Char Char System_2 Omega
red_3 = RConst ts (zip ps rs) zer
    where ts = [a, f_a]
          ps = [[]]
          rs = [rule_2]

cred_1 = CRConst red_1 modulus
    where modulus (OmegaTwoPlusOneElement n)
              | n == 1 = (\m -> OmegaTwoPlusOneElement (4 + (m * 2)))
              | n == 2 = (\m -> OmegaTwoPlusOneElement (3 + (m * 2)))
              | otherwise = error("Invalid input to modulus")

cred_2 = CRConst red_2 modulus
    where modulus (OmegaTwoPlusOneElement n)
              | n == 1 = (\m -> OmegaTwoPlusOneElement (4 + (m * 2)))
              | n == 2 = (\m -> OmegaTwoPlusOneElement (3 + (m * 2)))
              | otherwise = error("Invalid input to modulus")

cred_3 = CRConst red_3 modulus
    where modulus (OmegaElement n)
              | n == 0 = (\m -> OmegaElement 1)
              | otherwise = error("Invalid input to modulus")

show_steps (CRConst (RConst _ s _) _) = s
