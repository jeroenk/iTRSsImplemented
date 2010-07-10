import Array

-- Plumbing

class MyShow a where
    myshow :: a -> String

instance MyShow Char where
    myshow x = [x]

-- Systems of notation

data OrdinalType
    = ZeroOrdinal
    | SuccessorOrdinal
    | LimitOrdinal

class SystemOfNotation s where
    k :: s -> OrdinalType
    p :: s -> s
    q :: s -> (s -> s)

get_limit_pred :: (SystemOfNotation s) => s -> s
get_limit_pred n = get_limit_pred' (k n) n
    where get_limit_pred' ZeroOrdinal n      = n
          get_limit_pred' SuccessorOrdinal n = get_limit_pred (p n)
          get_limit_pred' LimitOrdinal n     = n

class SystemOfNotation s => UnivalentSystem s where
    leq :: s -> s -> Bool

-- Signatures and variables

class Signature s where
    arity :: s -> Int

class Eq v => Variables v

data (Signature s, Variables v) => Symbol s v
    = FunctionSymbol s
    | VariableSymbol v

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (Symbol s v) where
    show (FunctionSymbol f) = myshow f
    show (VariableSymbol x) = myshow x

-- Terms

data (Signature s, Variables v) => Term s v
    = Function s (Array Int (Term s v))
    | Variable v

constant :: (Signature s, Variables v) => s -> Term s v
constant c | arity c == 0 = Function c (array (1,0) [])
           | otherwise    = error "Input is not a constant"

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (Term s v) where
    show (Function f xs)
        | arity f == 0  = myshow f
        | otherwise     = myshow f ++ "(" ++ (show' (elems xs) True) ++ ")"
            where show' [] _         = ""
                  show' (x:xs) True  = show x ++ show' xs False
                  show' (x:xs) False = "," ++ show x ++ show' xs False
    show (Variable v)   = myshow v

-- Strings of natural numbers

data NatString = NatStr [Int]

instance Eq NatString where
    (NatStr ns) == (NatStr ms) = ns == ms

instance Show NatString where
    show (NatStr ns) = show ns

-- Substitutions

data Substitution s v = Subst [(v, Term s v)]

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (Substitution s v) where
    show (Subst xs) = "{" ++ show' xs True ++ "}"
        where show' [] _
                  = ""
              show' ((x, t):ss) True
                  = "(" ++ myshow x ++ ", " ++ show t ++ ")" ++ show' ss False
              show' ((x, t):ss) False
                  = ", (" ++ myshow x ++ ", " ++ show t ++ ")" ++ show' ss False

-- Rewrite rules and systems

data (Signature s, Variables v) => RewriteRule s v
    = Rule (Term s v) (Term s v)

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (RewriteRule s v) where
    show (Rule l r) = show l ++ " -> " ++ show r

type Step s v = (NatString, RewriteRule s v)

class (Signature s, Variables v) => RewriteSystem s v r where
    rules :: r -> [RewriteRule s v]

-- Reductions
--
-- Remark that we do not represent the final term of a reduction. In case the
-- reduction is of limit ordinal length, the term might be uncomputable.
--
-- We assume the steps and terms in reductions to be indexed starting from 0.

-- Examples

type OmegaTwoPlusOne = Int

instance SystemOfNotation OmegaTwoPlusOne where
    k n
       | n == 0    = LimitOrdinal      -- omega.2
       | n == 1    = LimitOrdinal      -- omega
       | n == 2    = ZeroOrdinal       -- 0
       | otherwise = SuccessorOrdinal  -- even: n; odd: omega + n
    p n
       | n > 2     = n - 2
       | otherwise = error("Predeccessor undefined")
    q n
       | n == 0    = (\m -> (2 * m) + 3)
       | n == 1    = (\m -> (2 * m) + 2)
       | otherwise = error("Limit function undefined")

instance UnivalentSystem OmegaTwoPlusOne where
    leq m n
        | n == m                                   = True
        | n == 0                                   = True
        | n == 1 && m > 0              && (even m) = True
        |           m == 2                         = True
        | n > 2  && m > 2  && (odd n)  && (odd m)  = m <= n
        | n > 2  && m > 2  && (odd n)  && (even m) = True
        | n > 2  && m > 2  && (even n) && (even m) = m <= n
        | otherwise                                = False
