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

-- This module defines substitutions.

module Substitution (
    Substitution,
    in_substitution,
    substitute,
    match
) where

import SignatureAndVariables
import Term

import Array
import List

-- Substitutions are finite(!) lists of (variable, term)-pairs.
type Substitution s v = [(v, Term s v)]

-- Establish if a variable occurs in a substitution.
in_substitution :: Variables v
    => Substitution s v -> v -> Bool
in_substitution [] _
    = False
in_substitution ((y, _):sigma') x
    | x == y    = True
    | otherwise =  in_substitution sigma' x

-- Substitute a variable (if possible).
substitute_variable :: Variables v
    => Substitution s v -> v -> Term s v
substitute_variable [] x
    = Variable x
substitute_variable ((y, t):sigma') x
    | x == y    = t
    | otherwise = substitute_variable sigma' x

-- Apply a substitution to a term.
substitute :: (Signature s, Variables v)
    => Substitution s v -> Term s v -> Term s v
substitute sigma (Function f ts)
    = Function f (fmap (substitute sigma) ts)
substitute sigma (Variable x)
    = substitute_variable sigma x

-- Match a term s with instance t and yield the matching substitution.
--
-- Note that this function only works poperly in case a match exists,
-- which suffices for our purposes.
match :: (Signature s, Variables v)
    => Term s v -> Term s v -> Substitution s v
match s t = nubBy (\(x, _) (y, _) -> x == y) (compute_match s t)
    where compute_match (Function f ss) (Function g ts)
              | f == g    = concat (zipWith compute_match (elems ss) (elems ts))
              | otherwise = error "Cannot match terms"
          compute_match (Variable x) t'
              = [(x, t')]
          compute_match _ _
              = error "Cannot match terms"
