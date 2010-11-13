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

-- This module defines signatures and variable sets.

module SignatureAndVariables (
    Signature(arity),
    DynamicSigma(DynamicFun),
    Variables,
    DynamicVar(DynamicVar),
    Symbol(FunctionSymbol, VariableSymbol)
) where

import MyShow

-- A signature is a set with an comparison operator and an arity function.
class Eq s => Signature s where
    arity :: s -> Int

-- A "dynamic" signature: the arity is encoded in the function symbol, where
-- the actual function symbol is represented by a string.
data DynamicSigma = DynamicFun String Int

instance MyShow DynamicSigma where
    myshow (DynamicFun f _) = f

instance Eq DynamicSigma where
    (DynamicFun f a) == (DynamicFun g b) = (f == g) && (a == b)

instance Signature DynamicSigma where
    arity (DynamicFun _ a) = a

-- A set of variables has a comparison operator.
class Eq v => Variables v

-- A "dynamic" variable set: variables are represented by strings.
data DynamicVar = DynamicVar String

instance MyShow DynamicVar where
    myshow (DynamicVar x) = x

instance Eq DynamicVar where
    (DynamicVar x) == (DynamicVar y) = x == y

instance Variables DynamicVar

-- Symbols are either from the signature or from the set of variables.
data (Signature s, Variables v) => Symbol s v
    = FunctionSymbol s
    | VariableSymbol v

instance (Signature s, Variables v)
    => Eq (Symbol s v) where
    FunctionSymbol f == FunctionSymbol g = f == g
    VariableSymbol x == VariableSymbol y = x == y
    _ == _                               = False

instance (MyShow s, MyShow v, Signature s, Variables v)
    => Show (Symbol s v) where
    show (FunctionSymbol f) = myshow f
    show (VariableSymbol x) = myshow x
