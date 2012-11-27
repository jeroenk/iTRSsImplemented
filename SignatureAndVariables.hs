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

-- This module defines signatures and variable sets.

module SignatureAndVariables (
    Signature(arity, inArity), Variables,
    Symbol(FunctionSymbol, VariableSymbol)
) where

import Prelude

-- A signature is a set with an equality operator and an arity function. The
-- inArity function can be used to check if an index is within the range of
-- the arity.
class Eq s => Signature s where
    arity   :: s -> Int
    inArity :: Int -> s -> Bool

    -- Default implementation of inArity
    inArity i f = 1 <= i && i <= arity f

-- A set of variables comes with an equality operator.
class Eq v => Variables v

-- Symbols (in terms) are either from the signature or the set of variables.
data Symbol s v where
    FunctionSymbol :: (Signature s, Variables v) => s -> Symbol s v
    VariableSymbol :: (Signature s, Variables v) => v -> Symbol s v

instance (Signature s, Variables v)
    => Eq (Symbol s v) where
    FunctionSymbol f == FunctionSymbol g = f == g
    VariableSymbol x == VariableSymbol y = x == y
    _ == _                               = False

instance (Show s, Show v, Signature s, Variables v)
    => Show (Symbol s v) where
    show (FunctionSymbol f) = show f
    show (VariableSymbol x) = show x
