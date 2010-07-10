import Array
import List

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

class SystemOfNotation o where
    k :: o -> OrdinalType
    p :: o -> o
    q :: o -> (o -> o)
    to_int :: o -> Int

get_limit_pred :: (SystemOfNotation o) => o -> o
get_limit_pred n = get_limit_pred' (k n) n
    where get_limit_pred' ZeroOrdinal n      = n
          get_limit_pred' SuccessorOrdinal n = get_limit_pred (p n)
          get_limit_pred' LimitOrdinal n     = n

class SystemOfNotation o => UnivalentSystem o where
    leq  :: o -> o -> Bool
    zero :: o      -- Existence follows by univalence
    suco :: o -> o -- Existence follows by univalence

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

position_of_term :: (Signature s, Variables v) => Term s v -> NatString -> Bool
position_of_term _ (NatStr [])
    = True
position_of_term (Function f xs) (NatStr (n:ns))
    | n < 1 || n > arity f = False
    | otherwise            = position_of_term (xs!n) (NatStr ns)
position_of_term (Variable _) (NatStr (_:_))
    = False

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

substitute_variable :: Variables v => Substitution s v -> v -> Term s v
substitute_variable (Subst []) x
    = Variable x
substitute_variable (Subst ((y, t):ss)) x
    = if x == y then t else substitute_variable (Subst ss) x

substitute :: (Signature s, Variables v)
    => Substitution s v -> Term s v -> Term s v
substitute sigma (Function f xs)
    = Function f (xs // [(i, (substitute sigma (xs!i))) | i <- indices xs])
substitute sigma (Variable x)
    = substitute_variable sigma x

compute_substitution :: (Signature s, Variables v)
    => Term s v -> Term s v -> Substitution s v
compute_substitution s t = Subst (nubBy same_variable (compute s t))
    where compute (Function f xs) (Function g ys)
              = concat (zipWith compute (elems xs) (elems ys))
          compute t (Variable x)
              = [(x, t)]
          same_variable (x, s) (y, t)
              = x == y

-- Subterms

subterm :: (Signature s, Variables v) => Term s v -> NatString -> Term s v
subterm s (NatStr [])
    = s
subterm (Function f xs) (NatStr (n:ns))
    | 1 <= n && n <= arity f = subterm (xs!n) (NatStr ns)
    | otherwise              = error "Getting non-existing subterm"

replace_subterm :: (Signature s, Variables v)
    => Term s v -> Term s v -> NatString -> Term s v
replace_subterm _ t (NatStr [])
    = t
replace_subterm (Function f xs) t (NatStr (n:ns))
    | 1 <= n && n <= arity f = Function f subterms
    | otherwise              = error "Replacing non-existing subterm"
        where subterms = xs // [(n, replace_subterm (xs!n) t (NatStr ns))]
replace_subterm (Variable x) t _
    = (Variable x)

-- Rewrite rules and systems

data (Signature s, Variables v) => RewriteRule s v
    = Rule (Term s v) (Term s v)

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (RewriteRule s v) where
    show (Rule l r) = show l ++ " -> " ++ show r

type Step s v = (NatString, RewriteRule s v)

rewrite_step :: (Signature s, Variables v)
    => Term s v -> Step s v -> Term s v
rewrite_step t (p, Rule l r)
    | valid_position = replace_subterm t sigma_r p
    | otherwise      = error "Rewriting at non-existing position"
        where valid_position = position_of_term t p
              sigma = compute_substitution (subterm t p) l
              sigma_r = substitute sigma r

rewrite_steps :: (Signature s, Variables v)
    => Term s v -> [Step s v] -> [Term s v]
rewrite_steps t ps = t:(rewrite_steps' t ps)
    where rewrite_steps' _ []     = []
          rewrite_steps' t (p:ps) = rewrite_steps (rewrite_step t p) ps

class (Signature s, Variables v) => RewriteSystem s v r where
    rules :: r -> [RewriteRule s v]

-- Reductions
--
-- Remark that we do not represent the final term of a reduction. In case the
-- reduction is of limit ordinal length, the term might be uncomputable.
--
-- We assume the steps and terms in reductions to be indexed starting from 0.

data (Signature s, Variables v, RewriteSystem s v r, UnivalentSystem o)
     => Reduction s v r o
    = Red [Term s v] [Step s v]

show_reduction_from :: (MyShow s, MyShow v, Signature s, Variables v,
                        RewriteSystem s v r, UnivalentSystem o)
                       => (Reduction s v r o) -> o -> String
show_reduction_from (Red ss _) n = show' n True
    where show' n True
              | indexof n' ss = show (ss!!n') ++ show' (suco n) False
              | otherwise    = ""
                  where n' = to_int n
          show' n False
              | indexof n' ss = " -> " ++ show (ss!!n') ++ show' (suco n) False
              | otherwise    = ""
                  where n' = to_int n
          indexof n []     = False
          indexof 0 _      = True
          indexof n (_:ss) = indexof (n - 1) ss

instance (MyShow s, MyShow v, Signature s, Variables v, RewriteSystem s v r,
          UnivalentSystem o)
         => Show (Reduction s v r o) where
    show ss = show_reduction_from ss zero

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
    to_int n
        = n

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
    zero
       = 2
    suco n
       | n == 0    = error("omega.2 does not have a successor")
       | n == 1    = 3
       | n == 2    = 4
       | otherwise = n + 2

type Standard_Term         = Term Char Char
type Standard_Substitution = Substitution Char Char
type Standard_Rule         = RewriteRule Char Char

instance Signature Char where
    arity 'a' = 0
    arity 'b' = 0
    arity 'c' = 0
    arity 'f' = 1
    arity 'g' = 1
    arity 'h' = 2
    arity _   = error "Character not in signature"

instance Variables Char

f_x :: Standard_Term
f_x = Function 'f' (array (1, 1) [(1, Variable 'x')])

g_x :: Standard_Term
g_x = Function 'g' (array (1, 1) [(1, Variable 'x')])

f_omega :: Standard_Term
f_omega = Function 'f' (array (1, 1) [(1, f_omega)])

f_g_omega :: Standard_Term
f_g_omega = Function 'f' (array (1, 1) [(1, g_f_omega)])

g_f_omega :: Standard_Term
g_f_omega = Function 'g' (array (1, 1) [(1, f_g_omega)])

rule_1 = Rule f_x g_x

data System_1 = Sys1

instance RewriteSystem Char Char System_1 where
    rules Sys1 = [rule_1]

red_1 :: Reduction Char Char System_1 OmegaTwoPlusOne
red_1 = Red ts (zip ps rs)
    where ps = step 0
              where step 0 = error("undefined step") : step 1
                    step n
                        | even n = NatStr (1 : (ones ((n `div` 2) - 1)))
                                   : step (n + 1)
                        | odd n  = NatStr (ones ((n - 1) `div` 2))
                                   : step (n + 1)
                            where ones 0 = []
                                  ones n = 1 : 1: (ones (n - 1))
          rs = rule_1:rs
          ts = term 0
              where term 0 = error("Undefined term") : term 1
                    term n
                        | even n = f_g_n ((n `div` 2) - 1) : term (n + 1)
                        | odd n  = g_g_n ((n - 1) `div` 2) : term (n + 1)
                            where f_g_n 0 = f_omega
                                  f_g_n n = (c_f (c_g (f_g_n (n - 1))))
                                  g_g_n 0 = f_g_omega
                                  g_g_n n = (c_g (c_g (g_g_n (n - 1))))
                                  c_f t = Function 'f' (array (1, 1) [(1, t)])
                                  c_g t = Function 'g' (array (1, 1) [(1, t)])

show_steps (Red _ s) = s
