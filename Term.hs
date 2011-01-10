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

-- This module defines (finite and infinite) terms.

module Term (
    Term(Function, Variable),
    constant, function_term,
    term_height, less_height
) where

import SignatureAndVariables

import Array

-- Terms consist of function symbols and variables.
data (Signature s, Variables v) => Term s v
    = Function s (Array Int (Term s v))
    | Variable v

instance (Show s, Show v, Signature s, Variables v)
    => Show (Term s v) where
    show (Function f ts)
        | arity f == 0  = show f
        | otherwise     = show f ++ "(" ++ show' (elems ts) True ++ ")"
            where show' [] _         = ""
                  show' (x:xs) True  = show x ++ show' xs False
                  show' (x:xs) False = "," ++ show x ++ show' xs False
    show (Variable v)   = show v

-- Wrapper for the definition of terms which are constants.
constant :: (Signature s, Variables v)
    => s -> Term s v
constant c
    | arity c == 0 = Function c (array (1,0) [])
    | otherwise    = error "Input is not a constant"

-- Wrapper for the definition of a terms with a function symbol at the root and
-- a number of subterms.
function_term :: (Signature s, Variables v)
    => s -> [(Int, Term s v)] -> Term s v
function_term f ts
    | has_length a ts = Function f (array (1, a) ts)
    | otherwise       = error "Number of provided subterms not matching arity"
        where a = arity f
              has_length 0 []     = True
              has_length _ []     = False
              has_length n (_:xs) = has_length (n - 1) xs

-- The height of a term: height(t) = max {|p| : p in Pos(t)}.
term_height :: (Signature s, Variables v)
    => Term s v -> Int
term_height (Function _ ts)
    = foldl max 0 (map term_height' (elems ts))
    where term_height' t = 1 + term_height t
term_height (Variable _)
    = 0

-- Establish if a term t is of height less than n.
less_height :: (Signature s, Variables v)
    => Term s v -> Int -> Bool
less_height (Function _ ts) n
    | n > 0     = and (map less_height' (elems ts))
    | otherwise = False
        where less_height' t = less_height t (n - 1)
less_height (Variable _) n
    | n > 0     = True
    | otherwise = False
