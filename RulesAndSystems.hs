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
    descendants, origins_across,
    RewriteSystem(rules)
) where

import MyShow
import SignatureAndVariables
import Terms
import PositionsAndSubterms
import Substitutions

import Array
import List

-- Rules consist of a left-hand and a right-hand side.
data (Signature s, Variables v) => RewriteRule s v
    = Rule (Term s v) (Term s v)

instance (MyShow s, MyShow v, Signature s, Variables v)
    => Show (RewriteRule s v) where
    show (Rule l r) = show l ++ " -> " ++ show r

-- Calculate the height of the left-hand side (which should be finite).
left_height :: (Signature s, Variables v)
    => RewriteRule s v -> Int
left_height (Rule l _) = term_height l

-- Rewrite steps are (position, rewrite rule)-pairs
type Step s v = (Position, RewriteRule s v)

-- Apply a rewrite rule to a term.
rewrite_step :: (Signature s, Variables v)
    => Term s v -> Step s v -> Term s v
rewrite_step t (p, Rule l r)
    | position_of_term t p = replace_subterm t p sigma_r
    | otherwise            = error "Applying rewrite step at invalid position"
        where sigma_r = substitute (match l (subterm t p)) r

-- Apply multiple rewrite steps in sequence, yielding a list of terms.
rewrite_steps :: (Signature s, Variables v)
    => Term s v -> [Step s v] -> [Term s v]
rewrite_steps t ps = t : rewrite_steps' t ps
    where rewrite_steps' _ []     = []
          rewrite_steps' s (q:qs) = rewrite_steps (rewrite_step s q) qs

-- Helper function for descendants and origins. The function recurses a term
-- following a given position until a variable is found. Once a variable is
-- found the function yields the variable and the remainder of the position
-- beging recursed.
get_var_and_pos :: (Signature s, Variables v)
    => Term s v -> Position -> (v, Position)
get_var_and_pos (Function f ts) (n:p)
    | 1 <= n && n <= arity f = get_var_and_pos (ts!n) p
    | otherwise              = error "Asking for a variable at invalid position"
get_var_and_pos (Function _ _) []
    = error "Asking for a variable where a function symbol occurs"
get_var_and_pos (Variable x) p
    = (x, p)

-- Descendants across a rewrite step.
descendants_of_position :: (Signature s, Variables v)
    => Position -> Step s v -> Positions
descendants_of_position p (q, Rule l r)
    | not (is_prefix q p)       = [p]
    | p' `elem` (non_var_pos l) = []
    | otherwise                 = [q ++ q' ++ p'' | q' <- var_pos r x]
        where p' = drop (length q) p
              (x, p'') = get_var_and_pos l p'

descendants_across :: (Signature s, Variables v)
    => Positions -> Step s v -> Positions
descendants_across ps s
    = concat (map (\p -> descendants_of_position p s) ps)

-- Descendants across multiple steps.
descendants :: (Signature s, Variables v)
    => Positions -> [Step s v] -> Positions
descendants ps []     = ps
descendants ps (q:qs) = descendants (descendants_across ps q) qs

-- Origins across a rewrite step.
origins_of_position :: (Signature s, Variables v)
    => Position -> Step s v -> Positions
origins_of_position p (q, Rule l r)
    | not (is_prefix q p)     = [p]
    | p' `elem` non_var_pos r = [q ++ q' | q' <- non_var_pos l]
    | [] `elem` var_pos r x   = [q ++ q' | q' <- non_var_pos l]
                                      ++ [q ++ q' ++ p'' | q' <- var_pos l x]
    | otherwise               = [q ++ q' ++ p'' | q' <- var_pos l x]
        where p' = drop (length q) p
              (x, p'') = get_var_and_pos r p'

origins_across :: (Signature s, Variables v)
    => Positions -> Step s v -> Positions
origins_across ps s
    = nub (concat (map (\p -> origins_of_position p s) ps))

-- A rewrite system is a singleton set with an associated rule function.
class (Signature s, Variables v) => RewriteSystem s v r where
    rules :: r -> [RewriteRule s v]
