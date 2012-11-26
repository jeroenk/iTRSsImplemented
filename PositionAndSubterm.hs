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

-- This module defines positions of terms and the subterm that occur at those
-- postitions.
--
-- As usual, positions are represented by lists of natural numbers.

module PositionAndSubterm (
    Position, Positions,
    positionLength, prefixOf, positionOf, funPositionOf,
    getVarAndPos, posToDepth, nonVarPos, varPos,
    subterm, replaceSubterm,
    PositionFunction,
    posFunEmpty, posFunPad, pos2PosFun, posFunMerge, varPosFun
) where

import SignatureAndVariables
import Term

import Prelude
import Data.Array
import Data.List

-- Positions are lists of natural numbers.
type Position  = [Int]

-- Sets of positions.
type Positions = [Position]

-- Yield the length of a position
positionLength :: Position -> Integer
positionLength = genericLength

-- Establish if a position p is a prefix of a position q.
prefixOf :: Position -> Position -> Bool
prefixOf = isPrefixOf

-- Establish if a position p occurs in a term t.
positionOf :: (Signature s, Variables v)
    => Position -> Term s v -> Bool
positionOf [] _
    = True
positionOf (i:p) (Function f ts)
    | i `inArity` f = p `positionOf` (ts!i)
    | otherwise     = False
positionOf (_:_) (Variable _)
    = False

-- Establish if a position p is position of a function symbol in a term t.
funPositionOf :: (Signature s, Variables v)
    => Position -> Term s v -> Bool
funPositionOf [] (Function _ _)
    = True
funPositionOf (i:p) (Function f ts)
    | i `inArity` f  = p `funPositionOf` (ts!i)
    | otherwise      = error "No subterm at prefix of position"
funPositionOf _ (Variable _)
    = False

-- Recurse a term following a given position until a variable is found. Once a
-- variable is found the function yields the variable and the remainder of the
-- position.
getVarAndPos :: (Signature s, Variables v)
    => Term s v -> Position -> (v, Position)
getVarAndPos (Function f ts) (i:p)
    | i `inArity` f = getVarAndPos (ts!i) p
    | otherwise     = error "No subterm at prefix of position"
getVarAndPos (Function _ _) []
    = error "Function symbol occurs at position"
getVarAndPos (Variable x) p
    = (x, p)

-- Helper function for obtaining the positions of a term.
--
-- The function processes a list of subterms based on a function f and
-- prefixes each of the positions returned by f with the appropriate
-- natural number (based on the location of the subterms in the list).
subPos :: (Signature s, Variables v)
    => (Term s v -> Positions) -> [Term s v] -> Positions
subPos f ts = concat (prefix (map f ts))
    where prefix = zipWith (map . (:)) [1..length ts]

-- Positions of a term t up to and including a certain depth d.
posToDepth :: (Signature s, Variables v)
    => Term s v -> Integer -> Positions
posToDepth _ 0               = [[]]
posToDepth (Function _ ts) d = [] : subPos posToDepth' (elems ts)
    where posToDepth' t = posToDepth t (d - 1)
posToDepth (Variable _) _   = [[]]

-- Positions at which a specific variable occurs.
varPos :: (Signature s, Variables v)
    => Term s v -> v -> Positions
varPos (Function _ ts) x = subPos varPos' (elems ts)
    where varPos' t = varPos t x
varPos (Variable y)    x = [[] | x == y]

-- Non-variable positions of a term.
nonVarPos :: (Signature s, Variables v)
    => Term s v -> Positions
nonVarPos (Function _ ts) = [] : subPos nonVarPos (elems ts)
nonVarPos (Variable _)    = []

-- Yield the subterm of a term t at a position p.
subterm :: (Signature s, Variables v)
    => Term s v -> Position -> Term s v
subterm t []
    = t
subterm (Function f ts) (i:p)
    | i `inArity` f = subterm (ts!i) p
    | otherwise     = error "No subterm at required position"
subterm (Variable _) _
    = error "No subterm at required position"

-- Replace a subterm at a position p by t.
replaceSubterm :: (Signature s, Variables v)
    => Term s v -> Term s v -> Position -> Term s v
replaceSubterm _ t []
    = t
replaceSubterm (Function f ss) t (i:p)
    | i `inArity` f = Function f $ ss // [(i, replaceSubterm (ss!i) t p)]
    | otherwise     = error "No subterm at required position"
replaceSubterm (Variable _) _ _
    = error "No subterm are required position"

-- A depth-finite position function is represented by a list of positions per
-- depth. The list is ordered starting at depth 0; all depths are assumed to
-- occur, as such also the absence of positions at a encoded. Remark that
-- the elements of PositionFunction are by definition finite lists.
type PositionFunction = [Positions]

-- Yield an empty position function.
posFunEmpty :: PositionFunction
posFunEmpty = repeat []

-- Yield a position function given a natural numnber d and a function f from
-- natual numbers to sets of positions such that f(i) is a set of positions of
-- length i + d.
posFunPad :: Integer -> PositionFunction -> PositionFunction
posFunPad 0 f = f
posFunPad d f = [] : posFunPad (d - 1) f

-- Yield position function with a single position p.
pos2PosFun :: Position -> PositionFunction
pos2PosFun p = posFunPad (positionLength p) ([p] : posFunEmpty)

-- Merge position functions.
posFunMerge :: [PositionFunction] -> PositionFunction
posFunMerge []           = posFunEmpty
posFunMerge (pf:[])      = pf
posFunMerge (pf:pf':pfs) = posFunMerge (merge' pf pf' : pfs)
    where merge' = zipWith (++)

-- Helper function for obtaining the variable positions of a term.
--
-- The function processes a list of subterms based on a function f and
-- prefixes each of the positions returned by f with the appropriate
-- natural number (based on the location of the subterms in the list).
subPosFun :: (Signature s, Variables v)
    => (Term s v -> PositionFunction) -> [Term s v] -> PositionFunction
subPosFun _ [] = posFunEmpty
subPosFun f ts = posFunMerge (prefix (map f ts))
    where prefix = zipWith (map . map . (:)) [1..length ts]

-- Yield position function of positions at which a variable x occurs.
varPosFun :: (Signature s, Variables v)
    => Term s v -> v -> PositionFunction
varPosFun (Function _ ts) x = [] : subPosFun varPosFun' (elems ts)
    where varPosFun' t = varPosFun t x
varPosFun (Variable y)    x = [[] | x == y] : posFunEmpty
