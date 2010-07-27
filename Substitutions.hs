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

-- This module defines substitutions

module Substitutions (
    Substitution,
    in_substitution,
    substitute_variable,
    substitute,
    match
) where

import MyShow
import SignatureAndVariables
import Terms

import Array
import List

-- Substitutions are finite(!) lists of (variable, term)-pairs
type Substitution s v = [(v, Term s v)]

-- Establish if a variable occurs in a substitution
in_substitution :: Variables v
    => Substitution s v -> v -> Bool
in_substitution [] x
    = False
in_substitution ((y,t):sigma') x
    | x == y    = True
    | otherwise =  in_substitution sigma' x

-- Substitute a variable (if possible)
substitute_variable :: Variables v
    => Substitution s v -> v -> Term s v
substitute_variable [] x
    = Variable x
substitute_variable ((y, t):sigma') x
    | x == y    = t
    | otherwise = substitute_variable sigma' x

-- Apply a substitution to a term
substitute :: (Signature s, Variables v)
    => Substitution s v -> Term s v -> Term s v
substitute sigma (Function f xs)
    = Function f (xs // [(i, substitute sigma (xs!i)) | i <- indices xs])
substitute sigma (Variable x)
    = substitute_variable sigma x

-- 
match :: (Signature s, Variables v)
    => Term s v -> Term s v -> Substitution s v
match s t = nubBy equal_variables (compute_match s t)
    where compute_match (Function f xs) (Function g ys)
              | f == g    = concat (zipWith compute_match (elems xs) (elems ys))
              | otherwise = error "Cannot match terms"
          compute_match (Variable x) t
              = [(x, t)]
          equal_variables (x, s) (y, t)
              = x == y
