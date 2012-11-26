{-# LANGUAGE GADTs #-}
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

-- This module defines (finite and infinite) terms.

module Term (
    Term(Function, Variable),
    constant, functionTerm,
    termHeight, heightLess,
    rootSymbol, hasRootVariable
) where

import SignatureAndVariables

import Prelude hiding (and, foldl)
import Data.Array
import Data.Foldable

-- Subterms below function symbols are packaged in arrays for efficiency.
type Subterms s v = Array Int (Term s v)

-- Terms consist of function symbols and variables.
data Term s v where
    Function :: (Signature s, Variables v) => s -> Subterms s v -> Term s v
    Variable :: (Signature s, Variables v) => v -> Term s v

instance (Show s, Show v, Signature s, Variables v)
    => Show (Term s v) where
    show (Function f ss)
        | arity f == 0  = show f
        | otherwise     = show f ++ show' (elems ss) "("
            where show' [] _     = ")"
                  show' (x:xs) c = c ++ show x ++ show' xs ","
    show (Variable v)   = show v

-- Helper function for defining terms which are constants.
constant :: (Signature s, Variables v)
    => s -> Term s v
constant c
    | arity c == 0 = Function c (array (1,0) [])
    | otherwise    = error "Symbol is not a constant"

-- Helper function for defining terms with a function symbol at the root and
-- a number of subterms. The subterms should be given as a list with the
-- elements representing subterms in order of occurence from left to right.
functionTerm :: (Signature s, Variables v)
    => s -> [Term s v] -> Term s v
functionTerm f ss
    | ss `hasLength` a = Function f $ listArray (1, a) ss
    | otherwise        = error "Number subterms does not match arity"
        where a = arity f
              hasLength [] 0     = True
              hasLength [] _     = False
              hasLength (_:_)  0 = False
              hasLength (_:xs) n = hasLength xs (n - 1)

-- The height of a term t: max {|p| : p in Pos(t) /\ t|_p in Sigma}.
termHeight :: (Signature s, Variables v)
    => Term s v -> Integer
termHeight (Function _ ss) = foldl max 0 $ fmap termHeight' ss
    where termHeight' t = 1 + termHeight t
termHeight (Variable _)    = 0

-- Establish if a term t is of height less than n.
heightLess :: (Signature s, Variables v)
    => Term s v -> Integer -> Bool
heightLess (Function _ ss) n
    | n > 0     = and $ fmap heightLess' ss
    | otherwise = False
        where heightLess' t = heightLess t (n - 1)
heightLess (Variable _) n
    | n > 0     = True
    | otherwise = False

-- Yield the root symbol of a term t.
rootSymbol :: (Signature s, Variables v)
    => Term s v -> Symbol s v
rootSymbol (Function f _) = FunctionSymbol f
rootSymbol (Variable x)   = VariableSymbol x

-- Establish if a certain variable occurs at the root of a term
hasRootVariable :: (Signature s, Variables v)
    => Term s v -> v -> Bool
hasRootVariable t x = rootSymbol t == VariableSymbol x
