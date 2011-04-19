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

import SignatureAndVariables
import Term
import RuleAndSystem
import SystemOfNotation
import Reduction

-- System of notation for the ordinal omega
data Omega2
    = OmegaElement Int
    | Omega2Element Int

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
    ord_eq (OmegaElement m) (OmegaElement n)
        = m == n
    ord_eq (Omega2Element m) (Omega2Element n)
        = m == n
    ord_eq _ _
        = False
    ord_zero
        = OmegaElement 0
    ord_succ (OmegaElement n)
        = OmegaElement (n + 1)
    ord_succ (Omega2Element n)
        = Omega2Element (n + 1)

-- Computable sequences of length at most omega.
data Omega2Sequence t = Omega2SequenceCons [t] [t]

instance ComputableSequence Omega2 t (Omega2Sequence t) where
    get_elem (Omega2SequenceCons xs _) (OmegaElement n)
        = xs!!n
    get_elem (Omega2SequenceCons _ xs) (Omega2Element n)
        = xs!!n
    get_from (Omega2SequenceCons xs _) (OmegaElement n)
        = drop n xs
    get_from (Omega2SequenceCons _ xs) (Omega2Element n)
        = drop n xs
    get_range (Omega2SequenceCons xs _) (OmegaElement m) (OmegaElement n)
        = take (n - m) (drop m xs)
    get_range (Omega2SequenceCons xs _) (OmegaElement m) (Omega2Element _)
        = drop m xs
    get_range (Omega2SequenceCons _ xs) (Omega2Element m) (Omega2Element n)
        = take (n - m) (drop m xs)
    get_range _ _ _
        = []
{-    select (Omega2SequenceCons xs ys) f alpha
        = select' xs 0 alpha
        where select' _  _ (_, Nothing)   = []
              select' ys m (z, Just beta) = head ys' : select' ys' n next_elem
                  where ys'            = drop (n - m) ys
                        next_elem      = f (z, beta)
                        OmegaElement n = beta
-}
-- Construct a computable sequence of length at most omega out of a list.
construct_sequence :: [t] -> [t] -> Omega2Sequence t
construct_sequence xs ys = Omega2SequenceCons xs ys

-- Computable sequences of terms and rewrite steps behave as they should.
type Omega2TermSequence s v   = Omega2Sequence (Term s v)
type Omega2StepSequence s v r = Omega2Sequence (Step s v)

instance (Signature s, Variables v)
    => TermSequence s v (Omega2TermSequence s v) Omega2

instance (RewriteSystem s v r)
    => StepSequence s v r (Omega2StepSequence s v r) Omega2

type Omega2Reduction s v r
    = Reduction s v r (Omega2TermSequence s v) (Omega2StepSequence s v r) Omega2
