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

-- This module defines rewrite rules and steps and rewrite system.

module RuleAndSystem (
    RewriteRule(Rule), Step,
    rewriteStep, rewriteSteps,
    descendantsAcrossStep, descendantsAcrossSteps,
    originsAcrossStep, originsAcrossSteps,
    RewriteSystem(rules),
    System(SystemCons)
) where

import SignatureAndVariables
import Term
import PositionAndSubterm
import Substitution

import Prelude
import Data.List

-- Rules consist of a left-hand side and a right-hand side.
data RewriteRule s v where
    Rule :: (Signature s, Variables v)
                => Term s v -> Term s v -> RewriteRule s v

instance (Show s, Show v, Signature s, Variables v)
    => Show (RewriteRule s v) where
    show (Rule l r) = show l ++ " -> " ++ show r

-- Rewrite steps are (position, rewrite rule)-pairs.
type Step s v = (Position, RewriteRule s v)

-- Apply a rewrite rule l -> r to a term t at position p.
rewriteStep :: (Signature s, Variables v)
    => Term s v -> Step s v -> Term s v
rewriteStep t (p, Rule l r)
    | p `positionOf` t = replaceSubterm t sigma_r p
    | otherwise        = error "Rewrite step applied at invalid position"
        where sigma_r = substitute (match l $ subterm t p) r

-- Apply multiple rewrite steps in sequence, yielding a list of terms.
rewriteSteps :: (Signature s, Variables v)
    => Term s v -> [Step s v] -> [Term s v]
rewriteSteps t steps = t : rewriteSteps' t steps
    where rewriteSteps' _ []     = []
          rewriteSteps' s (x:xs) = rewriteSteps (rewriteStep s x) xs

-- Helper function for descendantsAcrossStep which computes the descendants
-- of a single position across a rewrite step.
descendantsOfPosition :: (Signature s, Variables v)
    => Step s v -> Position -> PositionFunction
descendantsOfPosition (p, Rule l r) q
    | not (p `prefixOf` q) = pos2PosFun q
    | q' `funPositionOf` l = posFunEmpty
    | otherwise            = posFunPad (p_len + positionLength q'') pf_new
        where q'       = genericDrop (positionLength p) q
              p_len    = positionLength p
              pf_new   = [[p ++ p' ++ q'' | p' <- ps'] | ps' <- varPosFun r x]
              (x, q'') = getVarAndPos l q'

-- Helper function for descendantsAcrossStep which merges a list of position
-- functions. The function assumes that all positions in the ith position
-- function of the list occur at positions >= i - (term_height l).
descendantsMerge :: (Signature s, Variables v)
    => Step s v -> [PositionFunction] -> PositionFunction
descendantsMerge (_, Rule l _) pfs = merge' (termHeight l + 1) pfs
    where merge' n qfs = head start : merge' 2 (map tail (start : unused))
              where start  = posFunMerge (genericTake n qfs)
                    unused = genericDrop n qfs

-- Descendants across a rewrite step.
descendantsAcrossStep :: (Signature s, Variables v)
    => Step s v -> PositionFunction -> PositionFunction
descendantsAcrossStep step pf
    = descendantsMerge step $ map (posFunMerge . map descendants) pf
        where descendants = descendantsOfPosition step

-- Descendants across a finite number of rewrite steps.
descendantsAcrossSteps :: (Signature s, Variables v)
    => [Step s v] -> PositionFunction -> PositionFunction
descendantsAcrossSteps steps pf
    = foldl (flip descendantsAcrossStep) pf steps

-- Helper function for originsAcrossStep which computes the origins of a
-- single position across a rewrite step.
originsOfPosition :: (Signature s, Variables v)
    => Step s v -> Position -> Positions
originsOfPosition (p, Rule l r) q
    | not (p `prefixOf` q)  = [q]
    | q' `funPositionOf` r  = [p ++ p' | p' <- nonVarPos l]
    | r `hasRootVariable` x = [p ++ p' | p' <- nonVarPos l]
                                     ++ [p ++ p' ++ q'' | p' <- varPos l x]
    | otherwise             = [p ++ p' ++ q'' | p' <- varPos l x]
        where q'       = genericDrop (positionLength p) q
              (x, q'') = getVarAndPos r q'

-- Origins across a rewrite step.
originsAcrossStep :: (Signature s, Variables v)
    => Step s v -> Positions -> Positions
originsAcrossStep step ps
    = nub (concatMap (originsOfPosition step) ps)

-- Origins across a finite number of rewrite steps.
originsAcrossSteps :: (Signature s, Variables v)
    => [Step s v] -> Positions -> Positions
originsAcrossSteps steps ps
    = foldr originsAcrossStep ps steps

-- A rewrite system is a singleton set with an associated rule function.
class (Signature s, Variables v) => RewriteSystem s v r where
    rules :: r -> [RewriteRule s v]

-- Default data type for a rewrite system.
data System s v where
    SystemCons :: (Signature s, Variables v) => [RewriteRule s v] -> System s v

instance (Signature s, Variables v)
    => RewriteSystem s v (System s v) where
    rules (SystemCons rs) = rs
