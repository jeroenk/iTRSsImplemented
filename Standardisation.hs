{-
Copyright (C) 2012 Jeroen Ketema

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

-- This module implements standardisation of transfinite reductions.

module Standardisation (
    StandardisationMethod(Parallel, DepthLeft),
    standardisation
) where

import SignatureAndVariables
import PositionAndSubterm
import RuleAndSystem
import Reduction
import ParallelReduction
import Omega

import Prelude
import Data.List
import Data.Ord

data StandardisationMethod
    = Parallel
    | DepthLeft

newtype WrappedPosition = Wrap Position

toLeft :: Position -> Position -> Bool
toLeft (p:ps) (q:qs)
    | p == q = toLeft ps qs
    | p < q  = True
    | p > q  = False
toLeft _ _
    = False

instance Eq WrappedPosition where
    (Wrap p) == (Wrap q) = p == q

instance Ord WrappedPosition where
    compare (Wrap p) (Wrap q)
        | p_len < q_len    = LT
        | p_len == q_len
          && p `toLeft` q  = LT
        | p == q           = EQ
        | otherwise        = GT
        where p_len = positionLength p
              q_len = positionLength q

redexPatternAndPrefixPos :: (Signature s, Variables v)
    => Step s v -> Positions
redexPatternAndPrefixPos (p, Rule l _) = prefix_pos ++ pattern_pos
    where prefix_pos  = [p' | p' <- inits p, p' /= p]
          pattern_pos = [p ++ p' | p' <- nonVarPos l]

extraStep :: (Signature s, Variables v)
    => Integer -> Step s v -> ParallelStep s v -> ([Step s v], ParallelStep s v)
extraStep d (p, _) pstep@(pf, rule)
    | d == d' && p `elem` ps = ([(p, rule)], (pf', rule))
    | otherwise              = ([], pstep)
    where d'  = positionLength p
          ps  = genericIndex pf d
          pf' = pf_b ++ [p' | p' <- ps, p' /= p] : tail pf_e
          (pf_b, pf_e) = genericSplitAt d pf

-- The steps returned by parallelNeededSteps will be parallel to each other and
-- psteps' will consist of precisely on parallel step.
stepPermutation :: (Signature s, Variables v)
    => Integer -> ParallelStep s v -> Step s v -> ([Step s v], ParallelStep s v)
stepPermutation d pstep step = (needed', qstep')
    where positions     = redexPatternAndPrefixPos step
          needed'       = needed_sorted ++ step' : extra
          needed_sorted = sortBy (comparing $ positionLength . fst) needed
          (needed, psteps') = parallelNeededSteps [pstep] positions
          (step', qstep)    = limitedPermute (head psteps') step
          (extra, qstep')   = extraStep d step qstep

reductionPermutation :: (Signature s, Variables v)
    => Integer -> [Step s v] -> ([Step s v], ParallelReduction s v)
reductionPermutation _ []
    = error "No reduction steps given"
reductionPermutation _ [step]
    = ([step], [])
reductionPermutation d ((p, rule) : steps)
    = (steps_new, pstep : psteps)
    where (steps', psteps)     = reductionPermutation d steps
          (steps_new, pstep)   = permute (pos2PosFun p, rule) steps'
          permute qstep []     = ([], qstep)
          permute qstep (s:ss) = (ss' ++ ss'', qstep'')
              where (ss', qstep')   = stepPermutation d qstep s
                    (ss'', qstep'') = permute qstep' ss

stepStandardFilter :: (Signature s, Variables v)
    => Integer -> ParallelReduction s v -> Step s v
       -> ([Step s v], ParallelReduction s v)
stepStandardFilter d psteps step = (steps, leftover ++ remaining')
    where ps = redexPatternAndPrefixPos step
          (needed, remaining) = parallelNeededSteps psteps ps
          (step', remaining') = lP (reverse remaining) step []
          (steps, leftover) = reductionPermutation d (needed ++ [step'])
          lP [] step''' done = (step''', done)
          lP (qstep:qsteps) step''' done = lP qsteps step'' (dp:done)
              where (step'', dp) = limitedPermute qstep step'''

standardFilter :: (Signature s, Variables v)
    => Integer -> ParallelReduction s v -> ([[Step s v]], ParallelReduction s v)
standardFilter d psteps = filters psteps []
    where filters [] prev
              = ([], reverse prev)
          filters (qstep@(qf, rule):qsteps) prev
              | null qs   = filters qsteps (qstep:prev)
              | otherwise = (steps : steps', qsteps')
              where qs = genericIndex qf d
                    (steps', qsteps') = filters qsteps_new []
                    qsteps_new = remaining ++ (qf', rule) : qsteps
                    qf' = qf_b ++ (tail qs) : tail qf_e
                    (qf_b, qf_e) = genericSplitAt d qf
                    q = head qs
                    prev' = reverse prev
                    (steps, remaining) = stepStandardFilter d prev' (q, rule)


gather_inner :: (Signature s, Variables v)
    => Integer -> ParallelReduction s v -> [[Step s v]]
gather_inner d psteps = steps_d' : gather_inner (d + 1) psteps_d
    where steps_d' = standardisationOrder DepthLeft steps_d
          (steps_d, psteps_d) = standardFilter d psteps

standard :: (Signature s, Variables v)
    => [Step s v] -> [Step s v]
standard []  = error "Cannot be empty"
standard [x] = [x]
standard steps = steps'' ++ [last steps]
    where steps'' = genericTake (genericLength begin) $ concat steps'
          steps' = gather_inner 0 (map makeParallel begin)
          makeParallel (p, rule) = (pos2PosFun p, rule)
          begin = init steps

standardisationOrder :: (Signature s, Variables v)
    => StandardisationMethod -> [[Step s v]] -> [Step s v]
standardisationOrder Parallel  steps = concat steps
standardisationOrder DepthLeft steps = concat steps'''
    where steps''' = map (standard . snd) steps''
          steps''  = sortBy (comparing fst) steps'
          steps'   = map finalPosition steps
          finalPosition step = (Wrap . fst $ last step, step)

-- depth, previous needed steps, and previous parallel steps
standardisationList :: RewriteSystem s v r
    => StandardisationMethod -> CReduction s v r -> [[Step s v]]
standardisationList method reduction = gather 0 [] []
    where final = finalTerm reduction
          gather d prev psteps = steps_d' : gather (d + 1) total psteps_d
              where steps_d' = standardisationOrder method steps_d
                    (steps_d, psteps_d) = standardFilter d (psteps ++ psteps')
                    psteps' = filterSteps prev total
                    total   = neededSteps reduction ps
                    ps      = posToDepth final d

-- Concatenate the lists produced by standardisationList to obtain all steps.
standardisationSteps :: RewriteSystem s v r
    => StandardisationMethod -> CReduction s v r -> [Step s v]
standardisationSteps method reduction = concat steps_list
    where steps_list = standardisationList method reduction

-- Compute the modulus using that the ith element of the list produced by
-- standardisationList contains only steps at depth at least i.
standardisationModulus :: RewriteSystem s v r
    => StandardisationMethod -> CReduction s v r -> Modulus Omega
standardisationModulus method reduction = constructModulus phi
    where phi n      = genericLength $ concat $ genericTake (n + 1) steps_list
          steps_list = standardisationList method reduction

-- Standardisation of reductions in left-linear rewrite systems.
standardisation :: RewriteSystem s v r
    => StandardisationMethod -> r -> CReduction s v r -> CReduction s v r
standardisation method _ reduction = CRCons (RCons ts ss) phi
        where ts    = constructSequence terms
              ss    = constructSequence steps
              phi   = standardisationModulus method reduction
              terms = rewriteSteps (initialTerm reduction) steps
              steps = standardisationSteps method reduction
