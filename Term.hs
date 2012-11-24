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
    constant, function_term,
    term_height, less_height,
    root_symbol, has_root_var
) where

import SignatureAndVariables

import Prelude hiding (foldl, and)
import Data.Array
import Data.Foldable

-- Terms consist of function symbols and variables, with subterms as arrays.
type Subterms s v = Array Int (Term s v)

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

-- Wrapper for the definition of terms which are constants.
constant :: (Signature s, Variables v)
    => s -> Term s v
constant c
    | arity c == 0 = Function c (array (1,0) [])
    | otherwise    = error "Symbol is not a constant"

-- Wrapper for the definition of terms with a function symbol at the root and
-- a number of subterms. The subterms should be given in order of occurence
-- from left to right.
function_term :: (Signature s, Variables v)
    => s -> [Term s v] -> Term s v
function_term f ss
    | has_length a ss = Function f $ listArray (1, a) ss
    | otherwise       = error "Number subterms does not match arity"
        where a = arity f
              has_length 0 []     = True
              has_length _ []     = False
              has_length n (_:xs) = has_length (n - 1) xs

-- The height of a term: height(t) = max {|p| : p in Pos(t)}.
term_height :: (Signature s, Variables v)
    => Term s v -> Integer
term_height (Function _ ss) = foldl max 0 $ fmap term_height' ss
    where term_height' t = 1 + term_height t
term_height (Variable _)    = 0

-- Establish if a term t is of height less than n.
less_height :: (Signature s, Variables v)
    => Term s v -> Integer -> Bool
less_height (Function _ ss) n
    | n > 0     = and $ fmap less_height' ss
    | otherwise = False
        where less_height' t = less_height t (n - 1)
less_height (Variable _) n
    | n > 0     = True
    | otherwise = False

-- Yield the root symbol of a term.
root_symbol :: (Signature s, Variables v)
    => Term s v -> Symbol s v
root_symbol (Function f _) = FunctionSymbol f
root_symbol (Variable x)   = VariableSymbol x

-- Establish if a certain variable occurs at the root of a term
has_root_var :: (Signature s, Variables v)
    => Term s v -> v -> Bool
has_root_var t x = root_symbol t == VariableSymbol x
