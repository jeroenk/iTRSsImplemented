{-
Copyright (C) 2010 Jeroen Ketema and Jakob Grue Simonsen

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

-- This module implements Church-Rosser for reductions up to length omega.
--
-- A conversion is defined as a finite sequence of valleys, i.e. a sequence
-- of the form: s (->>.<<-)^+ t. The sequence is represented as a element
-- of the type [(CReduction s v r, CReduction s v r)], i.e. as a list of
-- valleys. Note that the list may not be empty, which would make it impossible
-- to output a pair of reductions, as we can no longer compute any initial
-- terms of the reductions.

module ChurchRosser (
    church_rosser
) where

import SignatureAndVariables
import PositionsAndSubterms
import RulesAndSystems
import OmegaReductions
import StripLemma
import Confluence

-- Drop the first n steps of a reduction. It is assumed that the reduction
-- has at least n steps.
drop_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => CReduction s v r -> Int -> CReduction s v r
drop_steps (CRConst (RConst ts ps) phi) n = CRConst (RConst ts' ps') phi'
    where ts' = drop n ts
          ps' = drop n ps
          phi' = \m -> (max (phi m) n) - n

-- Project a reduction over multiple steps by applying the Strip Lemma.
project_over :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> [Step s v] -> CReduction s v r
project_over r s []     = s
project_over r s (p:ps) = project_over r s' ps
    where s' = fst (strip_lemma r s p)

-- The function interleave_devel computes interleaving of a pair of reductions
-- that can be concatenated. The steps of the reduction are returned as a list
-- of lists of steps, where it is ensured for the ith item in the list that
-- all its steps occur at depth i.
interleave_devel :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> CReduction s v r -> [[Step s v]]
interleave_devel r s t = interleave_devel' s t 0
    where interleave_devel' s' t' d = steps : interleave_devel' s'' t'' (d + 1)
              where steps = ps ++ qs
                    ps = needed_steps s (needed_depth t d)
                    qs = needed_steps t d
                    s'' = project_over r s steps
                    t'' = drop_steps t (length qs)

-- Concatenate the lists produced by interleave_devel to obtain all steps.
interleave_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> CReduction s v r -> [Step s v]
interleave_steps r s t = concat (interleave_devel r s t)

-- Compute the modulus using that the ith element of the list produced by
-- interleave_devel contains all steps at depth i.
interleave_modulus :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> CReduction s v r -> Modulus
interleave_modulus r s t n = length (concat (take (n + 1) steps))
    where steps = interleave_devel r s t

-- Yield the interleaving of a pair of reductions that can be concatenated,
-- i.e. given s ->>.->> t a reduction s ->> t is returned.
interleave :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> CReduction s v r -> CReduction s v r -> CReduction s v r
interleave r s t = CRConst (RConst terms steps) modulus
    where terms = (rewrite_steps (initial_term s) steps)
          steps = interleave_steps r s t
          modulus = interleave_modulus r s t

-- Church-Rosser of orthogonal, non-collapsing rewrite systems with finite
-- right-hand sides. The function implements the classic proof except for
-- the concatenation of reductions which is replaced by an interleaving
-- scheme.
church_rosser ::  (Signature s, Variables v, RewriteSystem s v r)
    => r -> [(CReduction s v r, CReduction s v r)]
               -> (CReduction s v r, CReduction s v r)
church_rosser _ []
    = error "Conversion may not be empty"
church_rosser _ ((s, t):[])
    = (s, t)
church_rosser r ((s, t):(s', t'):cs)
    = church_rosser r ((s'', t''):cs)
    where s'' = interleave r s (fst confl)
          t'' = interleave r t (snd confl)
          confl = confluence r (t, s')
