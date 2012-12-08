{-# LANGUAGE MultiParamTypeClasses #-}
{-
Copyright (C) 2010, 2011, 2012 Jeroen Ketema and Jakob Grue Simonsen

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

-- This module defines some simple rewrite rules over the example terms and
-- defines some rewrite systems over the defined rules.
--
-- Note that the defined rules are not all mutually orthogonal. Hence, we need
-- to be careful when defining rewrite systems.

module ExampleRulesAndSystems (
    rule_a_to_b, rule_b_to_c,
    rule_a_to_f_a, rule_a_to_f_omega,
    rule_f_x_to_a, rule_f_x_to_g_x,
    rule_f_x_to_h_x_f_x, rule_f_x_to_h_x_omega,
    System_a_f_x, system_a_f_x,
    System_a_b_f_x, system_a_b_f_x,
    System_a_f_x_omega, system_a_f_x_omega
) where

import RuleAndSystem
import ExampleTermsAndSubstitutions

import Prelude

-- Rules.
rule_a_to_b ::RewriteRule Sigma Var
rule_a_to_b = Rule a b

rule_b_to_c ::RewriteRule Sigma Var
rule_b_to_c = Rule b c

rule_a_to_f_a :: RewriteRule Sigma Var
rule_a_to_f_a = Rule a f_a

rule_a_to_f_omega :: RewriteRule Sigma Var
rule_a_to_f_omega = Rule a f_omega

rule_f_x_to_a :: RewriteRule Sigma Var
rule_f_x_to_a = Rule f_x a

rule_f_x_to_g_x :: RewriteRule Sigma Var
rule_f_x_to_g_x = Rule f_x g_x

rule_f_x_to_h_x_f_x :: RewriteRule Sigma Var
rule_f_x_to_h_x_f_x = Rule f_x h_x_f_x

rule_f_x_to_h_x_omega :: RewriteRule Sigma Var
rule_f_x_to_h_x_omega = Rule f_x h_x_omega

-- Systems.
type System_a_f_x = System Sigma Var

system_a_f_x :: System_a_f_x
system_a_f_x = SystemCons [rule_a_to_f_a, rule_f_x_to_g_x]

type System_a_b_f_x = System Sigma Var

system_a_b_f_x :: System_a_b_f_x
system_a_b_f_x = SystemCons [rule_a_to_b, rule_b_to_c, rule_f_x_to_h_x_f_x]

type System_a_f_x_omega = System Sigma Var

system_a_f_x_omega :: System_a_f_x_omega
system_a_f_x_omega = SystemCons [rule_a_to_f_a, rule_f_x_to_h_x_omega]
