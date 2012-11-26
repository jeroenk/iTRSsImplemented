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

-- This module defines a system of notation for the ordinal omega.2, including
-- computable sequences of length at most omega.2.

module Omega2 (
    Omega2(OmegaElement,Omega2Element),
    Omega2Sequence, constructSequence,
    Omega2TermSequence, Omega2StepSequence,
    Omega2Reduction
) where

import Term
import RuleAndSystem
import SystemOfNotation
import Reduction

import Prelude
import Data.List

-- System of notation for the ordinal omega.2
data Omega2
    = OmegaElement Integer
    | Omega2Element Integer

instance SystemOfNotation Omega2 where
    ordKind (OmegaElement n)
        | n == 0    = ZeroOrdinal
        | otherwise = SuccOrdinal
    ordKind (Omega2Element n)
        | n == 0    = LimitOrdinal
        | otherwise = SuccOrdinal
    ordPred (OmegaElement n)
        | n > 0     = OmegaElement (n - 1)
        | otherwise = error "Predeccessor undefined"
    ordPred (Omega2Element n)
        | n > 0     = Omega2Element (n - 1)
        | otherwise = error "Predeccessor undefined"
    ordLimit (Omega2Element 0)
        = \n -> OmegaElement n
    ordLimit _
        = error "Limit function undefined"
    ordLimitPred (OmegaElement _)
        = OmegaElement 0
    ordLimitPred (Omega2Element _)
        = Omega2Element 0

instance UnivalentSystem Omega2 where
    ordLeq (OmegaElement m) (OmegaElement n)
        = m <= n
    ordLeq (Omega2Element m) (Omega2Element n)
        = m <= n
    ordLeq (Omega2Element _) (OmegaElement _)
        = False
    ordLeq (OmegaElement _) (Omega2Element _)
        = True
    ordZero
        = OmegaElement 0
    ordSucc (OmegaElement n)
        = OmegaElement (n + 1)
    ordSucc (Omega2Element n)
        = Omega2Element (n + 1)

-- Computable sequences of length at most omega.2.
data Omega2Sequence t = Omega2SequenceCons [t] [t]

instance ComputableSequence Omega2 t (Omega2Sequence t) where
    getElem (Omega2SequenceCons xs _) (OmegaElement n)
        = genericIndex xs n
    getElem (Omega2SequenceCons _ xs) (Omega2Element n)
        = genericIndex xs n
    getFrom (Omega2SequenceCons xs _) (OmegaElement n)
        = genericDrop n xs
    getFrom (Omega2SequenceCons _ xs) (Omega2Element n)
        = genericDrop n xs
    select (Omega2SequenceCons xs ys) f alpha
        = select' xs 0 0 alpha
            where select' _ _ _ (_, Nothing) = []
                  select' zs m n (z, Just beta) = head zs' : continuation
                      where continuation  = select' zs' m' n' (f (z, beta))
                            (zs', m', n') = compute zs m n beta
                            compute ws k l (OmegaElement i)
                                = (genericDrop (i - k) ws, i, l)
                            compute _ _ 0 (Omega2Element i)
                                = (genericDrop i ys, 0, i)
                            compute ws _ l (Omega2Element i)
                                = (genericDrop (i - l) ws, 0, i)

-- Construct a computable sequence of length at most omega.2 out of a list.
constructSequence :: [t] -> [t] -> Omega2Sequence t
constructSequence = Omega2SequenceCons

-- Reductions of length omega.2.
type Omega2TermSequence s v   = Omega2Sequence (Term s v)
type Omega2StepSequence s v r = Omega2Sequence (Step s v)

type Omega2Reduction s v r
    = Reduction s v r (Omega2TermSequence s v) (Omega2StepSequence s v r) Omega2
