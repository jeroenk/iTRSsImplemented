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

-- This module defines parallel reductions.
--
-- The terms over which parallel reductions are defined are not included
-- in the representation, as this would only clutter the representation
-- and would not serve any purpose elsewhere in the implementation.

module ParallelReduction (
    ParallelStep, ParallelReduction,
    limitedPermute,
    filterSteps, parallelNeededSteps,
    filterNeededSteps,
    diamondProperty
) where

import SignatureAndVariables
import PositionAndSubterm
import RuleAndSystem

import Prelude
import Data.List

-- Parallel reduction steps contract a number of redexes at parallel positions,
-- where all redexes employ the same rewrite rule. The positions are encoded
-- using PositionFunction, as also to encode that no steps occur at a certain
-- depth.
type ParallelStep s v = (PositionFunction, RewriteRule s v)

-- Parallel reductions are finite sequences of parallel reduction steps.
type ParallelReduction s v = [ParallelStep s v]

-- Permute a parallel step and a rewrite step. It is assumed that no redex
-- in the parallel step either overlaps with or occurs at prefix position of the
-- rewrite step.
limitedPermute :: (Signature s, Variables v)
    => ParallelStep s v -> Step s v -> (Step s v, ParallelStep s v)
limitedPermute (pf, rule) step = (step, (pf', rule))
    where pf' = descendantsAcrossStep step pf

-- Permute a parallel step and a finite sequence of rewrite steps, with all
-- steps parallel to each other. It is assumed that no redex in the parallel
-- step either overlaps with or occurs at prefix position of any of the rewrite
-- steps in the sequence.
limitedPermutes :: (Signature s, Variables v)
    => ParallelStep s v -> [Step s v] -> ([Step s v], ParallelStep s v)
limitedPermutes pstep []
    = ([], pstep)
limitedPermutes pstep (step:steps)
    = (step':steps_new, pstep_new)
    where (step', pstep')        = limitedPermute pstep step
          (steps_new, pstep_new) = limitedPermutes pstep' steps

-- Filter the steps from a reduction based on the steps found previously. It is
-- assumed that the steps found previously form a subsequence of the total
-- number of steps and that both sequences define finite reductions starting
-- from same term, where there exists a depth d such that all previous steps
-- and non of the new steps are needed.
--
-- The function does not compute needed reductions itself to avoid duplicating
-- computation of these reductions, instead these reductions are passed in as
-- parameters.
filterSteps :: (Signature s, Variables v)
    => [Step s v] -> [Step s v] -> ParallelReduction s v
filterSteps steps_prev steps = filters steps_prev steps []
    where filters [] left psteps
              = psteps ++ lift left
              where lift []             = []
                    lift ((p, rule):ss) = (pos2PosFun p, rule) : lift ss
          filters prev@(step_p@(p, _):prev') ((q, rule):left') psteps
              | p == q    = filters prev' left' (projectOver step_p psteps)
              | otherwise = filters prev  left' (psteps ++ [pstep_new])
              where pstep_new = (pos2PosFun q, rule)
                    projectOver _ []
                        = []
                    projectOver step (qstep:qsteps)
                        = qstep_new : projectOver step qsteps
                        where qstep_new = snd $ limitedPermute qstep step
          filters _ _ _
              = error "All previous steps should be included in total"

-- Helper function for neededFromParallel that for a position p yields all
-- positions in a position function that occur at a prefix position of p.
neededForPosition :: Position -> PositionFunction -> Positions
neededForPosition p = findPositions (positionLength p + 1)
    where findPositions 0 _  = []
          findPositions n pf = start ++ remainder
              where start      = filter isPrefix (head pf)
                    remainder  = findPositions (n - 1) (tail pf)
                    isPrefix q = q `prefixOf` p

-- Helper function for parallelNeededSteps that extracts needed steps from
-- a parallel step.
neededFromParallel :: (Signature s, Variables v)
    => ParallelStep s v -> Positions -> [Step s v]
neededFromParallel (pf, rule) ps = zip (neededFrom pf ps) (repeat rule)
    where neededFrom _  []     = []
          neededFrom qf (q:qs) = nub (start ++ remainder)
              where start     = neededForPosition q qf
                    remainder = neededFrom qf qs

-- Given a parallel reduction s -||->* t and a finite, prefix-closed subset of
-- positions of t, yield the steps of a reduction s ->* t' and a parallel
-- reduction t' -||->* t, where s ->* t consist precisely of the steps from
-- s -||->* t needed for the prefix-closed subset.
parallelNeededSteps :: (Signature s, Variables v)
    => ParallelReduction s v -> Positions -> ([Step s v], ParallelReduction s v)
parallelNeededSteps psteps ps = (needed_steps, psteps_new)
    where (needed_steps, psteps_new, _) = needed ps psteps
          needed qs []             = ([], [], qs)
          needed qs (qstep:qsteps) = (steps_new', qsteps_new, qs_new)
              where (steps', qsteps', qs') = needed qs qsteps
                    steps_new  = neededFromParallel qstep qs'
                    steps_new' = steps_new ++ steps'
                    qsteps_new = qstep_new:qsteps'
                    qstep_new  = snd $ limitedPermutes qstep steps_new'
                    qs_new     = originsAcrossSteps steps_new qs'

-- Combination of filterSteps and parallelNeededSteps.
filterNeededSteps :: (Signature s, Variables v)
    => [Step s v] -> ParallelReduction s v -> [Step s v] -> Positions
       -> ([Step s v], ParallelReduction s v)
filterNeededSteps steps_prev psteps_prev steps ps
    = parallelNeededSteps (psteps_prev ++ psteps') ps
        where psteps' = filterSteps steps_prev steps

-- Restricted version of the diamond property for parallel steps in orthogonal
-- rewrite systems.
--
-- Observe that projection of the step over the parallel step could be achieved
-- by a case distinction with the step being (i) is not below any position or
-- (ii) below exactly one position from the parallel step. However, we obtain
-- more compact code by simply considering all positions from the parallel step
-- with length that allows it to be a prefix position of the rewrite step.
diamondProperty :: (Signature s, Variables v)
    => Step s v -> ParallelStep s v -> (ParallelStep s v, ParallelStep s v)
diamondProperty step@(p, srule) (qf, prule) = ((qf_new, prule), (pf_new, srule))
    where qf_new = descendantsAcrossStep step qf
          pf_new = descendantsAcrossSteps relevant_steps (pos2PosFun p)
              where relevant_pf    = genericTake (positionLength p + 1) qf
                    relevant_steps = zip (concat relevant_pf) (repeat prule)
