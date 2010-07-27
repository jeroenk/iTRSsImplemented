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

-- This module defines (finite and infinite) terms

module Terms (
    Term(Function, Variable),
    constant,
    term_height,
    less_height
) where

import MyShow
import SignatureAndVariables

import Array

-- Terms consist of function symbols and variables

data (Signature s, Variables v) => Term s v
    = Function s (Array Int (Term s v))
    | Variable v

instance (MyShow s, MyShow v, Signature s, Variables v)
    => Show (Term s v) where
    show (Function f xs)
        | arity f == 0  = myshow f
        | otherwise     = myshow f ++ "(" ++ (show' (elems xs) True) ++ ")"
            where show' [] _         = ""
                  show' (x:xs) True  = show x ++ show' xs False
                  show' (x:xs) False = "," ++ show x ++ show' xs False
    show (Variable v)   = myshow v

-- Wrapper for the definition of constant terms

constant :: (Signature s, Variables v)
    => s -> Term s v
constant c
    | arity c == 0 = Function c (array (1,0) [])
    | otherwise    = error "Input is not a constant"

-- The height of a term: height(t) = max {|p| : p in Pos(t)}

term_height :: (Signature s, Variables v)
    => Term s v -> Int
term_height (Function _ xs)
    = foldl max 0 (map (\x -> 1 + term_height x) (elems xs))
term_height (Variable _)
    = 0

-- Establish if a term t is of height less than n

less_height :: (Signature s, Variables v)
    => Term s v -> Int -> Bool
less_height (Function _ xs) n
    | n > 0     = and (map (\x -> less_height x (pred n)) (elems xs))
    | otherwise = False
less_height (Variable _) n
    | n > 0     = True
    | otherwise = False
