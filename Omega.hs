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

-- This module defines a system of notation for the ordinal omega, including
-- computable sequences of length at most omega.

module Omega (
    Omega(OmegaElement),
    OmegaSequence, construct_sequence,
    OmegaTermSequence, OmegaStepSequence,
    OmegaReduction, construct_modulus
) where

import SignatureAndVariables
import Term
import RuleAndSystem
import SystemOfNotation
import Reduction

import List

-- System of notation for the ordinal omega
data Omega = OmegaElement Integer

instance SystemOfNotation Omega where
    ord_kind (OmegaElement n)
        | n == 0    = ZeroOrdinal
        | otherwise = SuccOrdinal
    ord_pred (OmegaElement n)
        | n > 0     = OmegaElement (n - 1)
        | otherwise = error "Predeccessor undefined"
    ord_limit (OmegaElement _)
        = error "Limit function undefined" -- Omega has no limit ordinals
    ord_lim_pred (OmegaElement _)
        = OmegaElement 0
    ord_to_int (OmegaElement n)
        = n

instance UnivalentSystem Omega where
    ord_leq (OmegaElement m) (OmegaElement n)
        = m <= n
    ord_eq (OmegaElement m) (OmegaElement n)
        = m == n
    ord_less (OmegaElement m) (OmegaElement n)
        = m < n
    ord_zero
        = OmegaElement 0
    ord_succ (OmegaElement n)
        = OmegaElement (n + 1)

-- Computable sequences of length at most omega.
data OmegaSequence t = OmegaSequenceCons [t]

instance ComputableSequence Omega t (OmegaSequence t) where
    get_elem (OmegaSequenceCons xs) (OmegaElement n)
        = genericIndex xs n
    get_from (OmegaSequenceCons xs) (OmegaElement n)
        = genericDrop n xs
    get_range (OmegaSequenceCons xs) (OmegaElement m) (OmegaElement n)
        = genericTake (n - m) (genericDrop m xs)
    select (OmegaSequenceCons xs) f alpha
        = select' xs 0 alpha
        where select' _  _ (_, Nothing)   = []
              select' ys m (z, Just beta) = head ys' : select' ys' n next_elem
                  where ys'            = genericDrop (n - m) ys
                        next_elem      = f (z, beta)
                        OmegaElement n = beta
    omega_dom _
        = True

-- Construct a computable sequence of length at most omega out of a list.
construct_sequence :: [t] -> OmegaSequence t
construct_sequence xs = OmegaSequenceCons xs

-- Computable sequences of terms and rewrite steps behave as they should.
type OmegaTermSequence s v   = OmegaSequence (Term s v)
type OmegaStepSequence s v r = OmegaSequence (Step s v)

instance (Signature s, Variables v)
    => TermSequence s v (OmegaTermSequence s v) Omega

instance (RewriteSystem s v r)
    => StepSequence s v r (OmegaStepSequence s v r) Omega

type OmegaReduction s v r
    = Reduction s v r (OmegaTermSequence s v) (OmegaStepSequence s v r) Omega

construct_modulus :: (Integer -> Integer) -> Modulus Omega
construct_modulus f (OmegaElement 0) m
    = OmegaElement (f m)
construct_modulus _ _ _
    = error "Modulus only defined for zero"
