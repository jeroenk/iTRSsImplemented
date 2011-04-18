{-# LANGUAGE MultiParamTypeClasses #-}
{-
Copyright (C) 2010, 2011 Jeroen Ketema and Jakob Grue Simonsen

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

module RuleAndSystem (
    RewriteRule(Rule),
    left_height,
    Step,
    rewrite_step, rewrite_steps,
    descendants, origins_across,
    filter_steps,
    RewriteSystem(rules)
) where

import SignatureAndVariables
import Term
import PositionAndSubterm
import Substitution

import Array
import List

-- Rules consist of a left-hand and a right-hand side.
data (Signature s, Variables v) => RewriteRule s v
    = Rule (Term s v) (Term s v)

instance (Show s, Show v, Signature s, Variables v)
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
rewrite_steps t steps = t : rewrite_steps' t steps
    where rewrite_steps' _ []     = []
          rewrite_steps' s (x:xs) = rewrite_steps (rewrite_step s x) xs

-- Helper function for descendants and origins. The function recurses a term
-- following a given position until a variable is found. Once a variable is
-- found the function yields the variable and the remainder of the position
-- beging recursed.
get_var_and_pos :: (Signature s, Variables v)
    => Term s v -> Position -> (v, Position)
get_var_and_pos (Function f ss) (i:p)
    | 1 <= i && i <= arity f = get_var_and_pos (ss!i) p
    | otherwise              = error "No subterm at required position"
get_var_and_pos (Function _ _) []
    = error "Function symbol occurs at position"
get_var_and_pos (Variable x) p
    = (x, p)

-- Descendants across a rewrite step.
descendants_of_position :: (Signature s, Variables v)
    => Step s v -> Position -> Positions
descendants_of_position (p, Rule l r) q
    | not (is_prefix p q)       = [q]
    | q' `elem` (non_var_pos l) = []
    | otherwise                 = [p ++ p' ++ q'' | p' <- var_pos r x]
        where q' = drop (length p) q
              (x, q'') = get_var_and_pos l q'

descendants_across :: (Signature s, Variables v)
    => Step s v -> Positions -> Positions
descendants_across step ps
    = concat (map (descendants_of_position step) ps)

-- Descendants across multiple steps.
descendants :: (Signature s, Variables v)
    => [Step s v] -> Positions -> Positions
descendants [] ps           = ps
descendants (step:steps) ps = descendants steps (descendants_across step ps)

-- Origins across a rewrite step.
origins_of_position :: (Signature s, Variables v)
    => Step s v -> Position -> Positions
origins_of_position (p, Rule l r) q
    | not (is_prefix p q)     = [q]
    | q' `elem` non_var_pos r = [p ++ p' | p' <- non_var_pos l]
    | [] `elem` var_pos r x   = [p ++ p' | p' <- non_var_pos l]
                                      ++ [p ++ p' ++ q'' | p' <- var_pos l x]
    | otherwise               = [p ++ p' ++ q'' | p' <- var_pos l x]
        where q' = drop (length p) q
              (x, q'') = get_var_and_pos r q'

origins_across :: (Signature s, Variables v)
    => Step s v -> Positions -> Positions
origins_across step ps
    = nub (concat (map (origins_of_position step) ps))

-- Filter the steps from a reduction based on the steps found previously. It is
-- assumed that the steps found previously form a subsequence of the total
-- number of steps and that both sequences define a finite reduction beginning
-- from same term, where there exists a depth d with all previous steps and non
-- of the new steps needed.
filter_steps :: (Signature s, Variables v)
    => [Step s v] -> [Step s v] -> [Step s v]
filter_steps previous total = filter_steps' previous total []
    where filter_steps' [] left ss
              =  ss ++ left
          filter_steps' prev@(p@(p', _):prev') (q@(q', _):left') ss
              | p' == q'
                  = filter_steps' prev' left' (project_over p ss)
              | otherwise
                  = filter_steps' prev left' (ss ++ [q])
          filter_steps' _ _ _
              = error "All previous steps should be included in total"
          project_over _ []
              = []
          project_over p ((q, s):qs)
              = ss_new ++ (project_over p qs)
              where qs_add = descendants_across p [q]
                    ss_new = map (\q' -> (q', s)) qs_add

-- A rewrite system is a singleton set with an associated rule function.
class (Signature s, Variables v) => RewriteSystem s v r where
    rules :: r -> [RewriteRule s v]
