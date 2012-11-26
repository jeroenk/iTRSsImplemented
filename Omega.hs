{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances #-}
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

-- This module defines a system of notation for the ordinal omega, including
-- computable sequences of length at most omega.

module Omega (
    Omega(OmegaElement),
    OmegaSequence, constructSequence,
    OmegaTermSequence, OmegaStepSequence,
    OmegaReduction, constructModulus
) where

import Term
import RuleAndSystem
import SystemOfNotation
import Reduction

import Prelude
import Data.List

-- System of notation for the ordinal omega
data Omega = OmegaElement Integer

instance SystemOfNotation Omega where
    ordKind (OmegaElement n)
        | n == 0    = ZeroOrdinal
        | otherwise = SuccOrdinal
    ordPred (OmegaElement n)
        | n > 0     = OmegaElement (n - 1)
        | otherwise = error "Predeccessor undefined"
    ordLimit (OmegaElement _)
        = error "Limit function undefined" -- Omega has no limit ordinals
    ordLimitPred (OmegaElement _)
        = OmegaElement 0
    ord2Int (OmegaElement n)
        = n

instance UnivalentSystem Omega where
    ordLeq (OmegaElement m) (OmegaElement n)
        = m <= n
    ordZero
        = OmegaElement 0
    ordSucc (OmegaElement n)
        = OmegaElement (n + 1)

-- Computable sequences of length at most omega.
data OmegaSequence t = OmegaSequenceCons [t]

instance ComputableSequence Omega t (OmegaSequence t) where
    getElem (OmegaSequenceCons xs) (OmegaElement n)
        = genericIndex xs n
    getFrom (OmegaSequenceCons xs) (OmegaElement n)
        = genericDrop n xs
    select (OmegaSequenceCons xs) f alpha
        = select' xs 0 alpha
            where select' _  _ (_, Nothing)   = []
                  select' ys m (z, Just beta) = head ys' : continuation
                      where continuation   = select' ys' n next_elem
                            ys'            = genericDrop (n - m) ys
                            next_elem      = f (z, beta)
                            OmegaElement n = beta
    hasOmegaDomain _
        = True

-- Construct a computable sequence of length at most omega out of a list.
constructSequence :: [t] -> OmegaSequence t
constructSequence = OmegaSequenceCons

-- Reductions of length omega.
type OmegaTermSequence s v   = OmegaSequence (Term s v)
type OmegaStepSequence s v r = OmegaSequence (Step s v)

type OmegaReduction s v r
    = Reduction s v r (OmegaTermSequence s v) (OmegaStepSequence s v r) Omega

-- Construct a modulus out of a function on natural numbers.
constructModulus :: (Integer -> Integer) -> Modulus Omega
constructModulus f (OmegaElement 0) m
    = OmegaElement (f m)
constructModulus _ _ _
    = error "Modulus only defined for zero"
