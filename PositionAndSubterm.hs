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

-- This module defines positions of terms and the subterm that occur at those
-- postitions.
--
-- As usual, positions are represented by lists of natural numbers.

module PositionAndSubterm (
    Position, Positions, PositionsPerDepth,
    pos_len, prefix_of, pos_of, fun_pos_of,
    dpos_empty, dpos_add_empty, pos_to_dpos, dpos_merge,
    pos_to_depth, non_var_pos, var_pos, var_dpos,
    subterm, replace_subterm
) where

import SignatureAndVariables
import Term

import Array
import List

-- Positions are sequences of natural numbers.
type Position  = [Int]

-- Sets of positions
type Positions = [Position]

-- A list of positions per depth. The list is ordered starting at depth 0; all
-- depths are assumed to occur, as such also the absence of positions at a
-- encoded. Remark that elements of PositionsPerDepth are by definition
-- infinite lists.
type PositionsPerDepth = [Positions]

-- Yield the length of a position
pos_len :: Position -> Integer
pos_len = genericLength

-- Establish if one position is a prefix of another position.
prefix_of :: Position -> Position -> Bool
prefix_of = isPrefixOf

-- Establish if a position occurs in a term.
pos_of :: (Signature s, Variables v)
    => Position -> Term s v -> Bool
pos_of [] _
    = True
pos_of (i:p) (Function f ts)
    | 1 <= i && i <= arity f = pos_of p (ts!i)
    | otherwise              = False
pos_of (_:_) (Variable _)
    = False

-- Establish if a position is position of a function symbol.
fun_pos_of :: (Signature s, Variables v)
    => Position -> Term s v -> Bool
fun_pos_of [] (Function _ _)
    = True
fun_pos_of (i:p) (Function f ts)
    | 1 <= i && i <= arity f  = fun_pos_of p (ts!i)
    | otherwise               = False
fun_pos_of _ (Variable _)
    = False

-- Positions per depth where no position occurs at any depth.
dpos_empty :: PositionsPerDepth
dpos_empty = repeat []

-- Yield positions per depth given that the positions per depth up to a finite
-- depth are given.
dpos_add_empty :: Integer -> PositionsPerDepth -> PositionsPerDepth
dpos_add_empty 0 pd = pd
dpos_add_empty d pd = [] : dpos_add_empty (d - 1) pd

-- Yield positions per depth given a single position.
pos_to_dpos :: Position -> PositionsPerDepth
pos_to_dpos p = dpos_add_empty (pos_len p) ([p] : dpos_empty)

-- Merge a list of positions per depth.
dpos_merge :: [PositionsPerDepth] -> PositionsPerDepth
dpos_merge []           = dpos_empty
dpos_merge (pd:[])      = pd
dpos_merge (pd:pd':pds) = dpos_merge (merge' pd pd' : pds)
    where merge' xs ys = zipWith (++) xs ys

-- Helper function for obtaining the positions of a term.
--
-- The function processes a list of subterms based on a function f and
-- prefixes each of the positions returned by f with the appropriate
-- natural number (based on the location of the subterms in the list).
subterm_pos :: (Signature s, Variables v)
    => (Term s v -> Positions) -> [Term s v] -> Positions
subterm_pos f ts = concat (prefix (map f ts))
    where prefix ps = zipWith (map . (:)) [1..length ts] ps

subterm_dpos :: (Signature s, Variables v)
    => (Term s v -> PositionsPerDepth) -> [Term s v] -> PositionsPerDepth
subterm_dpos _ [] = dpos_empty
subterm_dpos f ts = dpos_merge (prefix (map f ts))
    where prefix pds = zipWith (map . map . (:)) [1..length ts] pds

-- Positions up to and including a certain depth.
pos_to_depth :: (Signature s, Variables v)
    => Term s v -> Integer -> Positions
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
var_pos (Variable y)    x = if x == y then [[]] else []

var_dpos :: (Signature s, Variables v)
    => Term s v -> v -> PositionsPerDepth
var_dpos (Function _ ts) x = [] : subterm_dpos (\t -> var_dpos t x) (elems ts)
var_dpos (Variable y)    x = (if x == y then [[]] else []) : dpos_empty

-- Yield the subterm at a position.
subterm :: (Signature s, Variables v)
    => Term s v -> Position -> Term s v
subterm s []
    = s
subterm (Function f ts) (i:p)
    | 1 <= i && i <= arity f = subterm (ts!i) p
    | otherwise              = error "No subterm at required position"
subterm (Variable _) _
    = error "No subterm at required position"

-- Replace a subterm at a certain position.
replace_subterm :: (Signature s, Variables v)
    => Term s v -> Term s v -> Position -> Term s v
replace_subterm _ t []
    = t
replace_subterm (Function f ss) t (i:p)
    | 1 <= i && i <= arity f = Function f subterms
    | otherwise              = error "No subterm at required position"
        where subterms = ss // [(i, replace_subterm (ss!i) t p)]
replace_subterm (Variable _) _ _
    = error "No subterm are required position"
