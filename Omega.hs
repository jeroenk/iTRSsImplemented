{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
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
    OmegaSequence,
    construct_sequence
) where

import SignatureAndVariables
import Term
import RuleAndSystem
import SystemOfNotation
import TransfiniteReduction

-- System of notation for the ordinal omega
data Omega = OmegaElement Int

instance SystemOfNotation Omega where
    ord_kind (OmegaElement n)
        | n == 0    = ZeroOrdinal
        | otherwise = SuccOrdinal
    ord_pred  (OmegaElement n)
        | n > 0     = OmegaElement (n - 1)
        | otherwise = error "Predeccessor undefined"
    ord_limit  (OmegaElement _)
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
    from_omega _
        = True
    get_elem (OmegaSequenceCons xs) (OmegaElement n)
        = xs!!n
    get_from (OmegaSequenceCons xs) (OmegaElement n)
        = drop n xs
    get_range (OmegaSequenceCons xs) (OmegaElement m) (OmegaElement n)
        = take (n - m) (drop m xs)
    select (OmegaSequenceCons xs) f alpha
        = select' xs 0 alpha
        where select' _  _ (_, Nothing)   = []
              select' ys m (z, Just beta) = head ys' : select' ys' n next_elem
                  where ys'            = drop (n - m) ys
                        next_elem      = f (z, beta)
                        OmegaElement n = beta

-- Construct a computable sequence of length at most omega out of a list.
construct_sequence :: [t] -> OmegaSequence t
construct_sequence xs = OmegaSequenceCons xs

-- Computable sequences of terms and rewrite steps behave as they should.
instance (Signature s, Variables v)
    => TermSequence s v (OmegaSequence (Term s v)) Omega

instance (RewriteSystem s v r)
    => StepSequence s v r (OmegaSequence (Step s v)) Omega
