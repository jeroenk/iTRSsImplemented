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

-- This module defines substitutions.

module Substitution (
    Substitution,
    match, substitute,
    inSubstitution
) where

import SignatureAndVariables
import Term

import Prelude
import Data.Array
import Data.List

-- Substitutions are finite lists of (variable, term)-pairs.
type Substitution s v = [(v, Term s v)]

-- Match a term s with instance t and yield the matching substitution.
--
-- The function requires a match exists, which suffices. Error detection is
-- (and can be) only partial.
match :: (Signature s, Variables v)
    => Term s v -> Term s v -> Substitution s v
match s t = nubBy (\(x, _) (y, _) -> x == y) (computeMatch s t)
    where computeMatch (Function f ss) (Function g ts)
              | f == g    = concat $ zipWith computeMatch (elems ss) (elems ts)
              | otherwise = error "Cannot match terms"
          computeMatch (Variable x) t'
              = [(x, t')]
          computeMatch _ _
              = error "Cannot match terms"

-- Helper function for substitute, which substitutes a term for a variable
-- if the variable occurs in the subtitution.
substituteVariable :: (Signature s, Variables v)
    => Substitution s v -> v -> Term s v
substituteVariable [] x
    = Variable x
substituteVariable ((y, t):sigma') x
    | x == y    = t
    | otherwise = substituteVariable sigma' x

-- Apply a substitution sigma to a term t.
substitute :: (Signature s, Variables v)
    => Substitution s v -> Term s v -> Term s v
substitute sigma (Function f ss)
    = Function f $ fmap (substitute sigma) ss
substitute sigma (Variable x)
    = substituteVariable sigma x

-- Establish if a variable occurs in a substitution.
inSubstitution :: (Signature s, Variables v)
    => Substitution s v -> v -> Bool
inSubstitution [] _
    = False
inSubstitution ((y, _):sigma') x
    | x == y    = True
    | otherwise = inSubstitution sigma' x
