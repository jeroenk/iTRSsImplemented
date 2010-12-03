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

-- This module defines positions of terms and the subterm that occur at those
-- postitions.
--
-- As usual, positions are represented by lists of natural numbers.

module PositionsAndSubterms (
    Position, Positions,
    is_prefix,
    position_of_term,
    pos, pos_to_depth, non_var_pos, var_pos,
    get_symbol,
    subterm, replace_subterm
) where

import SignatureAndVariables
import Terms

import Array

-- Positions are sequences of natural numbers.
type Position  = [Int]

-- Sets of positions
type Positions = [Position]

-- Establish if one position is a prefix of another position.
is_prefix :: Position -> Position -> Bool
is_prefix p q = p == take (length p) q

-- Establish if a position occurs in a term.
position_of_term :: (Signature s, Variables v)
    => Term s v -> Position -> Bool
position_of_term _ []
    = True
position_of_term (Function f ts) (n:p)
    | 1 <= n && n <= arity f = position_of_term (ts!n) p
    | otherwise              = False
position_of_term (Variable _) (_:_)
    = False

-- Helper function for obtaining the positions of a term.
--
-- The function processes a list of subterms based on a function f and
-- prefixes each of the positions returned by f with the appropriate
-- natural number (based on the location of the subterms in the list).
subterm_pos :: (Signature s, Variables v)
    => (Term s v -> Positions) -> [Term s v] -> Positions
subterm_pos f ts = concat (prefix (map f ts) 1)
    where prefix [] _     = []
          prefix (p:ps) n = map (prefix_pos n) p : prefix ps (n + 1)
              where prefix_pos m q = m : q

-- All positions.
pos :: (Signature s, Variables v)
    => Term s v -> Positions
pos (Function _ ts) = [] : subterm_pos pos (elems ts)
pos (Variable _)    = [[]]

-- Positions up to and including a certain depth.
pos_to_depth :: (Signature s, Variables v)
    => Term s v -> Int -> Positions
pos_to_depth _ 0               = [[]]
pos_to_depth (Function _ ts) d = [] : subterm_pos pos_to_depth' (elems ts)
    where pos_to_depth' t = pos_to_depth t (d - 1)
pos_to_depth (Variable _) _    = [[]]

-- Non-variable positions.
non_var_pos :: (Signature s, Variables v)
    => Term s v -> Positions
non_var_pos (Function _ ts) = [] : subterm_pos non_var_pos (elems ts)
non_var_pos (Variable _)    = []

-- Positions at which a specific variable occurs.
var_pos :: (Signature s, Variables v)
    => Term s v -> v -> Positions
var_pos (Function _ ts) x = subterm_pos (\t -> var_pos t x) (elems ts)
var_pos (Variable y) x    = if x == y then [[]] else []

-- Yield the symbol at a position.
get_symbol :: (Signature s, Variables v)
    => Term s v -> Position -> Symbol s v
get_symbol (Function f _) []
    = FunctionSymbol f
get_symbol (Function f ts) (n:p)
    | 1 <= n && n <= arity f = get_symbol (ts!n) p
    | otherwise              = error "Asking for symbol at a invalid position"
get_symbol (Variable x) []
    = VariableSymbol x
get_symbol (Variable _) _
    = error "Asking for symbol at a invalid position"

-- Yield the subterm at a position.
subterm :: (Signature s, Variables v)
    => Term s v -> Position -> Term s v
subterm s []
    = s
subterm (Function f ts) (n:p)
    | 1 <= n && n <= arity f = subterm (ts!n) p
    | otherwise              = error "Asking for subterm at invalid position"
subterm (Variable _) _
    = error "Asking for subterm at invalid position"

-- Replace a subterm at a certain position.
replace_subterm :: (Signature s, Variables v)
    => Term s v -> Position -> Term s v -> Term s v
replace_subterm _ [] t
    = t
replace_subterm (Function f ts) (n:p) t
    | 1 <= n && n <= arity f = Function f subterms
    | otherwise              = error "Replacing subterm at invalid position"
        where subterms = ts // [(n, replace_subterm (ts!n) p t)]
replace_subterm (Variable _) _ _
    = error "Replacing subterm at invalid position"
