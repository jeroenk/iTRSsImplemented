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
import Substitutions
import RationalTerms
import RulesAndSystems
import OmegaReductions
import Confluence
import ExampleTerms

import Array

-- Examples

instance MyShow Char where
    myshow x = [x]

type Standard_Term         = Term Char Char
type Standard_Substitution = Substitution Char Char
type Standard_Rule         = RewriteRule Char Char

f_y :: Standard_Term
f_y = Function 'f' (array (1, 1) [(1, Variable 'y')])

f_b :: Standard_Term
f_b = Function 'f' (array (1, 1) [(1, constant 'b')])

f_f_a :: Standard_Term
f_f_a = Function 'f' (array (1, 1) [(1, Function 'f' (array (1, 1) [(1, constant 'a')]))])

h_x_x :: Standard_Term
h_x_x = Function 'h' (array (1, 2) [(1, Variable 'x'), (2, Variable 'x')])

h_a_f_b :: Standard_Term
h_a_f_b = Function 'h' (array (1, 2) [(1, constant 'a'), (2, f_b)])

f_h_a_f_b :: Standard_Term
f_h_a_f_b = Function 'f' (array (1, 1) [(1, h_a_f_b)])

h_x_f_y :: Standard_Term
h_x_f_y = Function 'h' (array (1, 2) [(1, Variable 'x'), (2, f_y)])

h_x_f_x :: Standard_Term
h_x_f_x = Function 'h' (array (1, 2) [(1, Variable 'x'), (2, f_x)])

h_a_x :: Standard_Term
h_a_x = Function 'h' (array (1, 2) [(1, constant 'a'), (2, Variable 'x')])

h_x_h_a_x :: Standard_Term
h_x_h_a_x = Function 'h' (array (1, 2) [(1, Variable 'x'), (2, h_a_x)])

sigma_1 :: Standard_Substitution
sigma_1 = [('x', f_a), ('y', constant 'a'), ('z', constant 'b')]

sigma_2 :: Standard_Substitution
sigma_2 = [('x', f_x)]

f_omega' :: Standard_Term
f_omega' = rational_term sigma_2 'x'

rule_1 :: RewriteRule Char Char
rule_1 = Rule f_x g_x

rule_2 :: RewriteRule Char Char
rule_2 = Rule (constant 'a') f_omega

rule_3 :: RewriteRule Char Char
rule_3 = Rule h_x_f_y (constant 'a')

rule_4 :: RewriteRule Char Char
rule_4 = Rule h_x_f_y f_x

rule_5 :: RewriteRule Char Char
rule_5 = Rule (constant 'a') f_a

rule_6 :: RewriteRule Char Char
rule_6 = Rule f_x h_x_h_a_x

rule_7 :: RewriteRule Char Char
rule_7 = Rule f_x h_x_x

rule_8 :: RewriteRule Char Char
rule_8 = Rule f_x (constant 'a')

rule_9 :: RewriteRule Char Char
rule_9 = Rule f_x h_x_f_x

rule_10 :: Standard_Rule
rule_10 = Rule (constant 'a') (constant 'b')

rule_11 :: Standard_Rule
rule_11 = Rule (constant 'b') (constant 'c')

data System_1 = Sys1

instance RewriteSystem Char Char System_1 where
    rules Sys1 = [rule_1, rule_2, rule_10]

data System_2 = Sys2

instance RewriteSystem Char Char System_2 where
    rules Sys2 = [rule_3, rule_4]

data System_3 = Sys3

instance RewriteSystem Char Char System_3 where
    rules Sys3 = [rule_5, rule_6, rule_7, rule_8, rule_9, rule_10, rule_11]

red_1 :: Reduction Char Char System_3
red_1 = RConst ts (zip ps rs)
    where ps = (iterate (\ns -> 1:ns) [1])
          rs = repeat rule_5
          ts = rewrite_steps (f_a) (zip ps rs)

red_2 :: Reduction Char Char System_1
red_2 = RConst ts (zip ps rs)
    where ps = (iterate (\ns -> 1:ns) [])
          rs = repeat rule_1
          ts = rewrite_steps (f_omega) (zip ps rs)

red_3 :: Reduction Char Char System_1
red_3 = RConst ts (zip ps rs)
    where ps = [[1], [1]]
          rs = [rule_4, rule_6]
          ts = rewrite_steps (f_h_a_f_b) (zip ps rs)

red_4 :: Reduction Char Char System_3
red_4 = RConst ts (zip ps rs)
    where ps = [[], [2], [2,2]]
          rs = [rule_9, rule_9, rule_9]
          ts = rewrite_steps (f_a) (zip ps rs)

red_5 :: Reduction Char Char System_3
red_5 = RConst ts (zip ps rs)
    where ps = [[1], [1]]
          rs = [rule_10, rule_11]
          ts = rewrite_steps (f_a) (zip ps rs)

red_6 :: Reduction Char Char System_1
red_6 = RConst ts (zip ps rs)
    where ps = []:(map (\p -> 1:1:p) ps)
          rs = rule_1:rs
          ts = rewrite_steps f_omega (zip ps rs)

red_7 :: Reduction Char Char System_1
red_7 = RConst ts (zip ps rs)
    where ps = [1]:(map (\p -> 1:1:p) ps)
          rs = rule_1:rs
          ts = rewrite_steps f_omega (zip ps rs)

red_8 :: Reduction Char Char System_1
red_8 = RConst [constant 'a'] []

red_9 :: Reduction Char Char System_1
red_9 = RConst ts (zip ps rs)
    where ps = [[1, 1]]
          rs = [rule_10]
          ts = rewrite_steps f_f_a (zip ps rs)

red_10 :: Reduction Char Char System_1
red_10 = RConst ts (zip ps rs)
    where ps = [[1]]
          rs = [rule_1]
          ts = rewrite_steps f_f_a (zip ps rs)

cred_1 :: CReduction Char Char System_3
cred_1 = CRConst red_1 (\x -> succ x)

cred_2 :: CReduction Char Char System_1
cred_2 = CRConst red_2 (\x -> succ x)

cred_3 :: CReduction Char Char System_1
cred_3 = CRConst red_3 (\_ -> 2)

cred_4 :: CReduction Char Char System_3
cred_4 = CRConst red_4 (\x -> min 3 (succ x))

cred_5 :: CReduction Char Char System_3
cred_5 = CRConst red_5 (\x -> if x == 0 then 0 else 2)

cred_6 :: CReduction Char Char System_1
cred_6 = CRConst red_6 (\x -> succ x)

cred_7 :: CReduction Char Char System_1
cred_7 = CRConst red_7 (\x -> x)

cred_8 :: CReduction Char Char System_1
cred_8 = CRConst red_8 (\_ -> 0)

cred_9 :: CReduction Char Char System_1
cred_9 = CRConst red_9 (\x -> if x == 0 || x == 1 then 0 else 1)

cred_10 :: CReduction Char Char System_1
cred_10 = CRConst red_10 (\x -> if x == 0 then 0 else 1)

-- show_steps (CRConst (RConst _ s) _) = s

-- show_phi (CRConst _ phi) = show_phi' 0
--     where show_phi' d = (show (phi d)) ++ (show_phi' (succ d))
