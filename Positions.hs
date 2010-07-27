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

-- This module defines strings of natural numbers and positions of terms

module Positions (
    NatString,
    is_prefix,
    position_of_term,
    pos,
    pos_to_depth,
    non_variable_pos,
    get_symbol
) where

import SignatureAndVariables
import Terms

import Array

-- Strings of natural numbers
type NatString = [Int]

-- Establish if one string is a prefix of another string
is_prefix :: NatString -> NatString -> Bool
is_prefix ns ms = ns == (take (length ns) ms)

-- Establish if a position occurs in a term
position_of_term :: (Signature s, Variables v)
    => Term s v -> NatString -> Bool
position_of_term _ []
    = True
position_of_term (Function f xs) (n:ns)
    | 1 <= n && n <= arity f = position_of_term (xs!n) ns
    | otherwise              = False
position_of_term (Variable _) (_:_)
    = False

-- Helper function for obtaining the positions of a term
--
-- The function processes an array of subterms based on a function f and
-- prefixes each of the positions returned by f with the appropriate
-- natural number (based on the location of the subterms in the array).
subterm_pos :: (Signature s, Variables v)
    => (Term s v -> [NatString]) -> Array Int (Term s v) -> [NatString]
subterm_pos f ts = concat (prefix (map f (elems ts)) 1)
    where prefix [] _     = []
          prefix (x:xs) n = (map (prefix_pos n) x) : (prefix xs (succ n))
              where prefix_pos n ns = n:ns

-- All positions
pos :: (Signature s, Variables v)
    => Term s v -> [NatString]
pos (Function _ ts) = [] : subterm_pos pos ts
pos (Variable _)    = [[]]

-- Positions up to and including a certain depth
pos_to_depth :: (Signature s, Variables v)
    => Term s v -> Int -> [NatString]
pos_to_depth _ 0               = [[]]
pos_to_depth (Function _ ts) d = [] : subterm_pos pos_to_depth' ts
    where pos_to_depth' t = pos_to_depth t (pred d)
pos_to_depth (Variable _) _    = [[]]

-- Non-variable positions
non_variable_pos :: (Signature s, Variables v)
    => Term s v -> [NatString]
non_variable_pos (Function _ ts) = [] : subterm_pos non_variable_pos ts
non_variable_pos (Variable _)    = []

-- Yield the symbol at a certain position
get_symbol :: (Signature s, Variables v)
    => Term s v -> NatString -> Symbol s v
get_symbol (Function f _) []
    = FunctionSymbol f
get_symbol (Function f xs) (n:ns)
    | 1 <= n && n <= arity f = get_symbol (xs!n) ns
    | otherwise              = error "Getting symbol at a non-existing position"
get_symbol (Variable x) []
    = VariableSymbol x
get_symbol (Variable _) _
    = error "Getting symbol at a non-existing position"
