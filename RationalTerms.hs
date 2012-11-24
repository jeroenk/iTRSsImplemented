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

-- This module defines rational terms as a finite system of regular equations.
--
-- Remark that a finite system of regular equations is a substitution where
-- the terms are not allowed to be variables.

module RationalTerms (
    RegularSystem,
    rational_term
) where

import SignatureAndVariables
import Term
import Substitution

-- A regular system is a substitution.
type RegularSystem s v = Substitution s v

-- Rational terms are constructed in the standard way using an initial variable.
rational_term :: (Signature s, Variables v)
    => RegularSystem s v -> v -> Term s v
rational_term sigma x = rational (Variable x)
    where rational (Function f ss)
              = Function f (fmap rational ss)
          rational t@(Variable y)
              | in_substitution sigma y = rational (substitute sigma t)
              | otherwise               = t
