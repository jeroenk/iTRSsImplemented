{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances #-}
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

-- This module defines a system of notation for the ordinal omega.2, including
-- computable sequences of length at most omega.2.

module Omega2 (
    Omega2(OmegaElement,Omega2Element),
    Omega2Sequence, construct_sequence,
    Omega2TermSequence, Omega2StepSequence,
    Omega2Reduction
) where

import Term
import RuleAndSystem
import SystemOfNotation
import Reduction

import Data.List

-- System of notation for the ordinal omega.2
data Omega2
    = OmegaElement Integer
    | Omega2Element Integer

instance SystemOfNotation Omega2 where
    ord_kind (OmegaElement n)
        | n == 0    = ZeroOrdinal
        | otherwise = SuccOrdinal
    ord_kind (Omega2Element n)
        | n == 0    = LimitOrdinal
        | otherwise = SuccOrdinal
    ord_pred (OmegaElement n)
        | n > 0     = OmegaElement (n - 1)
        | otherwise = error "Predeccessor undefined"
    ord_pred (Omega2Element n)
        | n > 0     = Omega2Element (n - 1)
        | otherwise = error "Predeccessor undefined"
    ord_limit (Omega2Element 0)
        = \n -> OmegaElement n
    ord_limit _
        = error "Limit function undefined"
    ord_lim_pred (OmegaElement _)
        = OmegaElement 0
    ord_lim_pred (Omega2Element _)
        = Omega2Element 0

instance UnivalentSystem Omega2 where
    ord_leq (OmegaElement m) (OmegaElement n)
        = m <= n
    ord_leq (Omega2Element m) (Omega2Element n)
        = m <= n
    ord_leq (Omega2Element _) (OmegaElement _)
        = False
    ord_leq (OmegaElement _) (Omega2Element _)
        = True
    ord_zero
        = OmegaElement 0
    ord_succ (OmegaElement n)
        = OmegaElement (n + 1)
    ord_succ (Omega2Element n)
        = Omega2Element (n + 1)

-- Computable sequences of length at most omega.2.
data Omega2Sequence t = Omega2SequenceCons [t] [t]

instance ComputableSequence Omega2 t (Omega2Sequence t) where
    get_elem (Omega2SequenceCons xs _) (OmegaElement n)
        = genericIndex xs n
    get_elem (Omega2SequenceCons _ xs) (Omega2Element n)
        = genericIndex xs n
    get_from (Omega2SequenceCons xs _) (OmegaElement n)
        = genericDrop n xs
    get_from (Omega2SequenceCons _ xs) (Omega2Element n)
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
construct_sequence :: [t] -> [t] -> Omega2Sequence t
construct_sequence = Omega2SequenceCons

-- Reductions of length omega.2.
type Omega2TermSequence s v   = Omega2Sequence (Term s v)
type Omega2StepSequence s v r = Omega2Sequence (Step s v)

type Omega2Reduction s v r
    = Reduction s v r (Omega2TermSequence s v) (Omega2StepSequence s v r) Omega2
