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

-- This module defines rewrite rules and steps and rewrite system

module RulesAndSystems (
    RewriteRule(Rule),
    left_height,
    Step,
    rewrite_step, rewrite_steps,
    RewriteSystem
) where

import MyShow
import SignatureAndVariables
import Terms
import PositionsAndSubterms
import Substitutions

-- Rules consist of a left-hand and a right-hand side
data (Signature s, Variables v) => RewriteRule s v
    = Rule (Term s v) (Term s v)

instance (MyShow s, MyShow v, Signature s, Variables v)
    => Show (RewriteRule s v) where
    show (Rule l r) = show l ++ " -> " ++ show r

-- Calculate the height of the left-hand side (which is supposed to be finite)
left_height :: (Signature s, Variables v)
    => RewriteRule s v -> Int
left_height (Rule l _) = term_height l

-- Rewrite steps are (position, rewrite rule)-pairs
type Step s v = (NatString, RewriteRule s v)

-- Apply a rewrite rule to a term
rewrite_step :: (Signature s, Variables v)
    => Term s v -> Step s v -> Term s v
rewrite_step t (ns, Rule l r)
    | position_of_term t ns = replace_subterm t ns sigma_r
    | otherwise             = error "Rewriting at non-existing position"
        where sigma_r = substitute (match l (subterm t ns)) r

-- Apply multiple rewrite steps in sequence, yielding a list of terms 
rewrite_steps :: (Signature s, Variables v)
    => Term s v -> [Step s v] -> [Term s v]
rewrite_steps t ps = t:(rewrite_steps' t ps)
    where rewrite_steps' _ []     = []
          rewrite_steps' t (p:ps) = rewrite_steps (rewrite_step t p) ps

-- A rewrite system is a singleton set with an associated rule function
class (Signature s, Variables v) => RewriteSystem s v r where
    rules :: r -> [RewriteRule s v]
