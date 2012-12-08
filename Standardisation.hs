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
{-
module Standardisation (
    standarisation
) where
-}
import SignatureAndVariables
import PositionAndSubterm
import RuleAndSystem
import ParallelReduction

import Prelude
import Data.List
import Data.Ord

extraStep :: (Signature s, Variables v)
    => Integer -> Position -> ParallelStep s v -> ([Step s v], ParallelStep s v)
extraStep d p pstep@(pf, rule)
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
stepPermutation d pstep step@(p, Rule l _) = (needed', qstep')
    where positions     = prefix_pos ++ pattern_pos
          prefix_pos    = [p' | p' <- inits p, p' /= p]
          pattern_pos   = [p ++ p' | p' <- nonVarPos l]
          needed'       = needed_sorted ++ step' : extra
          needed_sorted = sortBy (comparing $ length . fst) needed
          (needed, psteps') = parallelNeededSteps [pstep] positions
          (step', qstep)    = limitedPermute (head psteps') step
          (extra, qstep')   = extraStep d p qstep

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

