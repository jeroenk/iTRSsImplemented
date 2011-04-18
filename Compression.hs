{-# LANGUAGE FlexibleContexts #-}
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

-- This module implements compression of transfinite reductions.
--
-- Note that this module depends on the standard system of notation defined for
-- omega, which can be found in the Omega module.

module Compression (
    compression
) where

import RuleAndSystem
import TransfiniteReduction
import Omega

-- The function compr_devel computes the compressed reduction. The steps of the
-- reduction are returned as a list of lists of steps, where it is ensured for
-- the ith item in the list that all its steps occur at depth i.
compr_devel :: (TermSequence s v ts o, StepSequence s v r ss o)
    => CReduction s v r ts ss o -> [[Step s v]]
compr_devel reduction = compr_devel' 0 []
    where compr_devel' depth prev = steps_new : compr_devel' (depth + 1) total
              where total     = needed_steps reduction depth
                    steps_new = filter_steps prev total

-- Concatenate the lists produced by compr_devel to obtain all steps.
compr_steps :: (TermSequence s v ts o, StepSequence s v r ss o)
    => CReduction s v r ts ss o -> [Step s v]
compr_steps reduction = concat (compr_devel reduction)

-- Compute the modulus using that the ith element of the list produced by
-- compr_devel contains all steps at depth i.
compr_modulus :: (TermSequence s v ts o, StepSequence s v r ss o)
    => CReduction s v r ts ss o -> (Modulus Omega)
compr_modulus reduction (OmegaElement n)
    | n == 0    = \m -> OmegaElement (compute m)
    | otherwise = error "Modulus only defined for zero"
        where compute m = length (concat (take (m + 1) (compr_devel reduction)))

-- Compression of left-linear rewrite systems with finite right-hand sides.
compression :: (TermSequence s v ts o, StepSequence s v r ss o)
    => r -> CReduction s v r ts ss o -> OmegaCReduction s v r
compression _ reduction = CRCons (RCons ts ss) modulus
    where terms   = rewrite_steps (initial_term reduction) steps
          ts      = construct_sequence terms
          steps   = compr_steps reduction
          ss      = construct_sequence steps
          modulus = compr_modulus reduction
