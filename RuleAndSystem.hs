{-# LANGUAGE FlexibleInstances, GADTs, MultiParamTypeClasses #-}
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

-- This module defines rewrite rules and steps and rewrite system

module RuleAndSystem (
    RewriteRule(Rule),
    left_height,
    Step,
    rewrite_step, rewrite_steps,
    descendants, origins,
    ParallelStep,
    filter_steps, parallel_needed_steps,
    RewriteSystem(rules),
    BasicSystem(BasicSystemCons)
) where

import SignatureAndVariables
import Term
import PositionAndSubterm
import Substitution

import Data.Array
import Data.List

-- Rules consist of a left-hand and a right-hand side.
data RewriteRule s v where
    Rule :: (Signature s, Variables v)
                => Term s v -> Term s v -> RewriteRule s v

instance (Show s, Show v, Signature s, Variables v)
    => Show (RewriteRule s v) where
    show (Rule l r) = show l ++ " -> " ++ show r

-- Calculate the height of the left-hand side (which should be finite).
left_height :: (Signature s, Variables v)
    => RewriteRule s v -> Integer
left_height (Rule l _) = term_height l

-- Rewrite steps are (position, rewrite rule)-pairs.
type Step s v = (Position, RewriteRule s v)

-- Apply a rewrite rule to a term.
rewrite_step :: (Signature s, Variables v)
    => Term s v -> Step s v -> Term s v
rewrite_step t (p, Rule l r)
    | p `pos_of` t = replace_subterm t sigma_r p
    | otherwise    = error "Rewrite step applied at invalid position"
        where sigma_r = substitute (match l (subterm t p)) r

-- Apply multiple rewrite steps in sequence, yielding a list of terms.
rewrite_steps :: (Signature s, Variables v)
    => Term s v -> [Step s v] -> [Term s v]
rewrite_steps t steps = t : rewrite_steps' t steps
    where rewrite_steps' _ []     = []
          rewrite_steps' s (x:xs) = rewrite_steps (rewrite_step s x) xs

-- Helper function for descendants and origins. The function recurses a term
-- following a given position until a variable is found. Once a variable is
-- found the function yields the variable and the remainder of the position.
get_var_and_pos :: (Signature s, Variables v)
    => Term s v -> Position -> (v, Position)
get_var_and_pos (Function f ts) (i:p)
    | 1 <= i && i <= arity f = get_var_and_pos (ts!i) p
    | otherwise              = error "No subterm at required position"
get_var_and_pos (Function _ _) []
    = error "Function symbol occurs at position"
get_var_and_pos (Variable x) p
    = (x, p)

-- Descendants across a rewrite step.
descendants_of_position :: (Signature s, Variables v)
    => Step s v -> Position -> PositionsPerDepth
descendants_of_position (p, Rule l r) q
    | not (p `prefix_of` q) = pos_to_dpos q
    | q' `fun_pos_of` l     = dpos_empty
    | otherwise             = dpos_add_empty (p_len + pos_len q'') pd_new
        where q'       = genericDrop (pos_len p) q
              p_len    = pos_len p
              pd_new   = [[p ++ p' ++ q'' | p' <- ps'] | ps' <- var_dpos r x]
              (x, q'') = get_var_and_pos l q'

merge :: (Signature s, Variables v)
    => Step s v -> [PositionsPerDepth] -> PositionsPerDepth
merge (_, Rule l _) pds = merge' (term_height l + 1) pds
    where merge' n qds = head start : merge' 2 (map tail (start : unused))
              where start  = dpos_merge (genericTake n qds)
                    unused = genericDrop n qds

descendants_across :: (Signature s, Variables v)
    => Step s v -> PositionsPerDepth -> PositionsPerDepth
descendants_across step pd
    = merge step $ map (dpos_merge . map descendants_across_step) pd
        where descendants_across_step = descendants_of_position step

-- Descendants across multiple steps.
descendants :: (Signature s, Variables v)
    => [Step s v] -> PositionsPerDepth -> PositionsPerDepth
descendants [] pd
    = pd
descendants (step:steps) pd
    = descendants steps (descendants_across step pd)

-- Origins across a rewrite step.
origins_of_position :: (Signature s, Variables v)
    => Step s v -> Position -> Positions
origins_of_position (p, Rule l r) q
    | not (p `prefix_of` q)  = [q]
    | q' `fun_pos_of` r      = [p ++ p' | p' <- non_var_pos l]
    | r `has_root_var` x     = [p ++ p' | p' <- non_var_pos l]
                                      ++ [p ++ p' ++ q'' | p' <- var_pos l x]
    | otherwise              = [p ++ p' ++ q'' | p' <- var_pos l x]
        where q'       = genericDrop (pos_len p) q
              (x, q'') = get_var_and_pos r q'

origins_across :: (Signature s, Variables v)
    => Step s v -> Positions -> Positions
origins_across step ps
    = nub (concatMap (origins_of_position step) ps)

origins :: (Signature s, Variables v)
    => [Step s v] -> Positions -> Positions
origins [] ps
    = ps
origins (step:steps) ps
    = origins_across step (origins steps ps)

-- Parallel steps contract a number of redexes at parallel positions, where
-- all redexes employ the same rewrite rule. The positions are encoded using
-- PositionsPerDepth, as also to encode that no steps occur at a certain depth.
type ParallelStep s v = (PositionsPerDepth, RewriteRule s v)

-- Filter the steps from a reduction based on the steps found previously. It is
-- assumed that the steps found previously form a subsequence of the total
-- number of steps and that both sequences define finite reductions starting
-- from same term, where there exists a depth d such that all previous steps
-- and non of the new steps are needed.
--
-- The rewrite steps relevant for a certain prefix-closed set of positions are
-- returned, as is a finite number of parallel steps that are irrelevant for
-- the provided prefix-closed set of positions. The argument psteps_prev can be
-- used to pass in parallel steps returned by a previous call to the function.
filter_steps :: (Signature s, Variables v)
    => [Step s v] -> [ParallelStep s v] -> [Step s v] -> Positions
       -> ([Step s v], [ParallelStep s v])
filter_steps steps_prev psteps_prev steps ps
    = parallel_needed_steps (psteps_prev ++ psteps') ps
        where psteps' = filter_steps' steps_prev steps []

filter_steps' :: (Signature s, Variables v)
    => [Step s v] -> [Step s v] -> [ParallelStep s v] -> [ParallelStep s v]
filter_steps' [] left psteps
    = psteps ++ lift left
        where lift []             = []
              lift ((p, rule):ss) = (pos_to_dpos p, rule) : lift ss
filter_steps' prev@(step_p@(p, _):prev') ((q, rule):left') psteps
    | p == q    = filter_steps' prev' left' (project_over step_p psteps)
    | otherwise = filter_steps' prev  left' (psteps ++ [pstep_new])
        where pstep_new = (pos_to_dpos q, rule)
              project_over _ []
                  = []
              project_over step ((pd, r):qsteps)
                  = (pd_new, r) : project_over step qsteps
                  where pd_new = descendants_across step pd
filter_steps' _ _ _
    = error "All previous steps should be included in total"

-- Yield the needed steps from a sequence of parallel steps for a prefix-closed
-- set of positions. Both the needed steps and a finite number of parallel
-- steps that are irrelevant for the provided prefix-closed set of positions
-- are returned.
parallel_needed_steps :: (Signature s, Variables v)
    => [ParallelStep s v] -> Positions -> ([Step s v], [ParallelStep s v])
parallel_needed_steps psteps ps = (needed_steps, psteps_new)
    where (needed_steps, psteps_new, _) = needed ps psteps
          needed qs []                  = ([], [], qs)
          needed qs ((qd, rule):qsteps) = (steps_new', qsteps_new, qs_new)
              where (steps', qsteps', qs') = needed qs qsteps
                    steps_new  = needed_from_parallel (qd, rule) qs'
                    steps_new' = steps_new ++ steps'
                    qsteps_new = (qd_new, rule) : qsteps'
                    qd_new     = descendants steps_new' qd
                    qs_new     = origins steps_new qs'

needed_from_parallel :: (Signature s, Variables v)
    => ParallelStep s v -> Positions -> [Step s v]
needed_from_parallel (pd, rule) ps = zip (needed_from pd ps) (repeat rule)
    where needed_from _  []     = []
          needed_from qd (q:qs) = nub (start ++ remainder)
              where start     = needed_for_position qd q
                    remainder = needed_from qd qs

needed_for_position :: PositionsPerDepth -> Position -> Positions
needed_for_position pd p = find_positions (pos_len p + 1) pd
    where find_positions 0 _  = []
          find_positions n qd = start ++ remainder
              where start     = filter is_prefix (head qd)
                    remainder = find_positions (n - 1) (tail qd)
                    is_prefix q = q `prefix_of` p

-- A rewrite system is a singleton set with an associated rule function.
class (Signature s, Variables v) => RewriteSystem s v r where
    rules :: r -> [RewriteRule s v]

data BasicSystem s v where
    BasicSystemCons :: (Signature s, Variables v)
                           => [RewriteRule s v] -> BasicSystem s v

instance (Signature s, Variables v)
    => RewriteSystem s v (BasicSystem s v) where
    rules (BasicSystemCons rs) = rs
