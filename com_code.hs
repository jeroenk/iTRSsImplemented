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
    | SuccOrdinal
    | LimitOrdinal

instance Eq OrdinalType where
    ZeroOrdinal == ZeroOrdinal   = True
    SuccOrdinal == SuccOrdinal   = True
    LimitOrdinal == LimitOrdinal = True
    _ == _                       = False

class SystemOfNotation o where
    k :: o -> OrdinalType
    p :: o -> o
    q :: o -> (Int -> o)
    to_int :: o -> Int

get_limit_pred :: (SystemOfNotation o) => o -> o
get_limit_pred n = get_limit_pred' (k n) n
    where get_limit_pred' ZeroOrdinal n  = n
          get_limit_pred' SuccOrdinal n  = get_limit_pred (p n)
          get_limit_pred' LimitOrdinal n = n

class SystemOfNotation o => UnivalentSystem o where
    leq  :: o -> o -> Bool
    zero :: o      -- Existence follows by univalence
    suc  :: o -> o -- Existence follows by univalence

data Omega = OmegaElement Int

instance SystemOfNotation Omega where
    k (OmegaElement n)
        | n == 0    = ZeroOrdinal
        | otherwise = SuccOrdinal
    p  (OmegaElement n)
        | n > 0     = OmegaElement (n - 1)
        | otherwise = error("Predeccessor undefined")
    q  (OmegaElement n)
        = error("Limit function undefined")
    to_int  (OmegaElement n)
        = n

instance UnivalentSystem Omega where
    leq (OmegaElement m)  (OmegaElement n)
        = m <= n
    zero
        = OmegaElement 0
    suc (OmegaElement n)
        = OmegaElement (n + 1)

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

string_length :: NatString -> Int
string_length (NatStr ns) = length ns

prefix_position :: Int -> NatString -> NatString
prefix_position n (NatStr ns) = NatStr (n:ns)

is_prefix :: NatString -> NatString -> Bool
is_prefix (NatStr ns) (NatStr ms) = is_prefix' ns ms
    where is_prefix' [] _          = True
          is_prefix' (_:_) []      = False
          is_prefix' (n:ns) (m:ms) = if n == m then is_prefix' ns ms else False

position_of_term :: (Signature s, Variables v) => Term s v -> NatString -> Bool
position_of_term _ (NatStr [])
    = True
position_of_term (Function f xs) (NatStr (n:ns))
    | n < 1 || n > arity f = False
    | otherwise            = position_of_term (xs!n) (NatStr ns)
position_of_term (Variable _) (NatStr (_:_))
    = False

pos_to_depth :: (Signature s, Variables v) => Term s v -> Int -> [NatString]
pos_to_depth (Function _ xs) d
    | d == 0    = [NatStr []]
    | otherwise = NatStr [] : concat (prefix_positions (map ptd (elems xs)) 1)
    where prefix_positions [] _
              = []
          prefix_positions (x:xs) n
              = (map (prefix_position n) x):(prefix_positions xs (succ n))
          ptd t = pos_to_depth t (d - 1)
pos_to_depth (Variable _) d
    = [NatStr []]

non_variable_pos :: (Signature s, Variables v) => Term s v -> [NatString]
non_variable_pos (Function _ xs)
    = NatStr [] : concat (prefix_positions (map non_variable_pos (elems xs)) 1)
    where prefix_positions [] _
              = []
          prefix_positions (x:xs) n
              = (map (prefix_position n) x):(prefix_positions xs (succ n))
non_variable_pos (Variable _)
    = []

get_symbol :: (Signature s, Variables v) => Term s v -> NatString -> Symbol s v
get_symbol (Function f _) (NatStr [])
    = FunctionSymbol f
get_symbol (Function f xs) (NatStr (n:ns))
    | 1 <= n && n <= arity f = get_symbol (xs!n) (NatStr ns)
    | otherwise              = error "Getting symbol at non-existing position"
get_symbol (Variable x) (NatStr [])
    = VariableSymbol x

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
-- The initial index of terms and steps should be equal and given explicitly.

data (Signature s, Variables v, RewriteSystem s v r, UnivalentSystem o)
     => Reduction s v r o
    = Red [Term s v] [Step s v] o

show_reduction_from :: (MyShow s, MyShow v, Signature s, Variables v,
                        RewriteSystem s v r, UnivalentSystem o)
                       => (Reduction s v r o) -> o -> String
show_reduction_from (Red ss _ _) n = show' n True
    where show' n True
              | indexof n' ss = show (ss!!n') ++ show' (suc n) False
              | otherwise    = ""
                  where n' = to_int n
          show' n False
              | indexof n' ss = " -> " ++ show (ss!!n') ++ show' (suc n) False
              | otherwise    = ""
                  where n' = to_int n
          indexof n []     = False
          indexof 0 _      = True
          indexof n (_:ss) = indexof (n - 1) ss

instance (MyShow s, MyShow v, Signature s, Variables v, RewriteSystem s v r,
          UnivalentSystem o)
         => Show (Reduction s v r o) where
    show ss@(Red _ _ z) = show_reduction_from ss z

type Modulus o = o -> Int -> o

data (Signature s, Variables v, RewriteSystem s v r, UnivalentSystem o)
     => ComputReduction s v r o
    = CRed (Reduction s v r o) (Modulus o)

instance (MyShow s, MyShow v, Signature s, Variables v, RewriteSystem s v r,
          UnivalentSystem o)
         => Show (ComputReduction s v r o) where
    show (CRed ss _) = show ss -- No termination detection based on depth

initial_term :: (Signature s, Variables v, RewriteSystem s v r,
                 UnivalentSystem o)
    => ComputReduction s v r o -> Term s v
initial_term (CRed (Red ss _ z) _) = ss!!(to_int z)

final_term :: (Signature s, Variables v, RewriteSystem s v r, UnivalentSystem o)
    => ComputReduction s v r o -> Term s v
final_term (CRed (Red ts _ z) phi)
    = final_subterm []
    where final_subterm ps
              = root root_symbol ps
                  where n = phi z (length ps)
                        root_symbol = get_symbol (ts!!(to_int n)) (NatStr ps)
          root (FunctionSymbol f) ps
              = Function f (subterms (arity f) ps)
          root (VariableSymbol x) _
              = Variable x
          subterms a ps
              = array (1, a) [(i, final_subterm (ps ++ [i])) | i <- [1..a]]

-- Descendants and Origins

descendants_of_position :: (Signature s, Variables v)
    => NatString -> Step s v -> [NatString]
descendants_of_position ps (qs, (Rule l r))
    = map (\xs -> NatStr xs) (descendants' ps qs (is_prefix qs ps))
    where descendants' (NatStr ps) _ False
              = [ps]
          descendants' (NatStr ps) (NatStr qs) True
              = map (\xs -> qs ++ xs) (compute_new (drop (length qs) ps))
          compute_new ps = compute_new' ps (get_variable l ps)
              where get_variable (Function _ _) []      = Nothing
                    get_variable (Function _ xs) (p:ps) = get_variable (xs!p) ps
                    get_variable (Variable x) _         = Just x
          compute_new' ps Nothing  = []
          compute_new' ps (Just x) = new_positions r x (get_position l ps) []
              where get_position (Function _ xs) (p:ps) = get_position (xs!p) ps
                    get_position (Variable _) ps        = ps
          new_positions (Function _ xs) y ps qs
              = concat (new_positions' (elems xs) y ps qs 1)
          new_positions (Variable x) y ps qs
              = if x == y then [qs ++ ps] else []
          new_positions' [] _ _ _ _
              = []
          new_positions' (x:xs) y ps qs n
              = (new_positions x y ps (qs ++ [n]))
                :(new_positions' xs y ps qs (succ n))

descendants_across_step :: (Signature s, Variables v)
    => [NatString] -> Step s v -> [NatString]
descendants_across_step ps s
    = concat (map (\p -> descendants_of_position p s) ps)

descendants :: (Signature s, Variables v)
    => [NatString] -> [Step s v] -> [NatString]
descendants ps []     = ps
descendants ps (q:qs) = descendants (descendants_across_step ps q) qs

origin_of_position :: (Signature s, Variables v)
    => NatString -> Step s v -> [NatString]
origin_of_position ps (qs, (Rule l r))
    = map (\xs -> NatStr xs) (origin' ps qs (is_prefix qs ps))
    where origin' (NatStr ps) _ False
              = [ps]
          origin' (NatStr ps) (NatStr qs) True
              = map (\xs -> qs ++ xs) (compute_old (drop (length qs) ps))
          compute_old ps = compute_old' ps (get_variable r ps)
              where get_variable (Function _ _) []      = Nothing
                    get_variable (Function _ xs) (p:ps) = get_variable (xs!p) ps
                    get_variable (Variable x) _         = Just x
          compute_old' ps Nothing  = map plain (non_variable_pos l)
              where plain (NatStr ps) = ps
          compute_old' ps (Just x) = old_positions l x (get_position r ps) []
              where get_position (Function _ xs) (p:ps) = get_position (xs!p) ps
                    get_position (Variable _) ps        = ps
          old_positions (Function _ xs) y ps qs
              = concat (old_positions' (elems xs) y ps qs 1)
          old_positions (Variable x) y ps qs
              = if x == y then [qs ++ ps] else []
          old_positions' [] _ _ _ _
              = []
          old_positions' (x:xs) y ps qs n
              = (old_positions x y ps (qs ++ [n]))
                :(old_positions' xs y ps qs (succ n))

origin_across_step :: (Signature s, Variables v)
    => [NatString] -> Step s v -> [NatString]
origin_across_step ps s
    = nub (concat (map (\p -> origin_of_position p s) ps))

-- Compression

accumulate_essential :: (Signature s, Variables v, RewriteSystem s v r,
                         UnivalentSystem o)
    => ComputReduction s v r o -> Int -> [(Step s v, o)]
accumulate_essential s@(CRed (Red _ ps z) phi) d
    = needed_steps (pos_to_depth (final_term s) d) n (k n)
    where n = phi z d
          needed_steps qs n SuccOrdinal
              | leq n z   = []
              | otherwise = ss_new
                  where q@(q', _) = ps!!(to_int (p n))
                        qs_new = origin_across_step qs q
                        ss_new
                            | q' `elem` qs_new = ss' ++ [(q, p n)]
                            | otherwise        = ss'
                        ss' = needed_steps qs_new (p n) (k (p n))
          needed_steps qs n LimitOrdinal
              | leq n z   = []
              | otherwise = needed_steps qs n' (k n')
                  where n' = phi n (maximum (map string_length qs))
          needed_steps qs n ZeroOrdinal
              | leq n z   = []
              | otherwise = error("Greater than 0 while being equal or smaller")

filter_steps :: (Signature s, Variables v, UnivalentSystem o)
    => [(Step s v, o)] -> [(Step s v, o)] -> [Step s v]
filter_steps prev total = filter_steps' prev total []
    where filter_steps' [] left ss =  ss ++ (map fst left)
          filter_steps' prev@((s, n):prev') ((t, m):left') ss
              | (leq n m) && (leq m n)
                  = filter_steps' prev' left' (project_over [s] ss)
              | otherwise
                  = filter_steps' prev left' (ss ++ [t])
          project_over ss []
              = []
          project_over ss ((ps, r):qs)
              = ss_new ++ (project_over ss_new qs)
              where ps_add = descendants [ps] ss
                    ss_new = map (\p -> (p, r)) ps_add

compr_devel :: (Signature s, Variables v, RewriteSystem s v r,
                UnivalentSystem o)
    => ComputReduction s v r o -> [[Step s v]]
compr_devel s = (map fst initial) : (compr_devel' 1 initial)
    where initial
              = accumulate_essential s 0
          compr_devel' d prev
              = new : (compr_devel' (succ d) total)
                  where total = accumulate_essential s d
                        new   = filter_steps prev total

compr_steps :: (Signature s, Variables v, RewriteSystem s v r,
                UnivalentSystem o)
    => ComputReduction s v r o -> [Step s v]
compr_steps s = concat (compr_devel s)

compr_modulus :: (Signature s, Variables v, RewriteSystem s v r,
                  UnivalentSystem o)
    => ComputReduction s v r o -> (Modulus Omega)
compr_modulus s (OmegaElement n)
    | n == 0
        = (\m -> OmegaElement (length (concat (take (succ m) (compr_devel s)))))
    | otherwise
        = error("Modulus only defined for 0")

compression :: (Signature s, Variables v, RewriteSystem s v r,
                UnivalentSystem o)
    => r -> (ComputReduction s v r o) -> (ComputReduction s v r Omega)
compression r s = CRed reduction modulus
    where reduction = Red terms steps zero
          terms = (rewrite_steps (initial_term s) steps)
          steps = compr_steps s
          modulus = compr_modulus s

-- Examples

data OmegaTwoPlusOne = OmegaTwoPlusOneElement Int

instance Show OmegaTwoPlusOne where
    show (OmegaTwoPlusOneElement n) = show n

instance SystemOfNotation OmegaTwoPlusOne where
    k (OmegaTwoPlusOneElement n)
        | n == 0    = LimitOrdinal  -- omega.2
        | n == 1    = LimitOrdinal  -- omega
        | n == 2    = ZeroOrdinal   -- 0
        | otherwise = SuccOrdinal   -- even: n; odd: omega + n
    p  (OmegaTwoPlusOneElement n)
        | n > 2     = OmegaTwoPlusOneElement (n - 2)
        | otherwise = error("Predeccessor undefined")
    q  (OmegaTwoPlusOneElement n)
        | n == 0    = (\m -> OmegaTwoPlusOneElement ((2 * m) + 3))
        | n == 1    = (\m -> OmegaTwoPlusOneElement ((2 * m) + 2))
        | otherwise = error("Limit function undefined")
    to_int  (OmegaTwoPlusOneElement n)
        = n

instance UnivalentSystem OmegaTwoPlusOne where
    leq  (OmegaTwoPlusOneElement m)  (OmegaTwoPlusOneElement n)
        | n == m                                   = True
        | n == 0                                   = True
        | n == 1 && m > 0              && (even m) = True
        |           m == 2                         = True
        | n > 2  && m > 2  && (odd n)  && (odd m)  = m <= n
        | n > 2  && m > 2  && (odd n)  && (even m) = True
        | n > 2  && m > 2  && (even n) && (even m) = m <= n
        | otherwise                                = False
    zero
       = OmegaTwoPlusOneElement 2
    suc (OmegaTwoPlusOneElement n)
       | n == 0    = error("omega.2 does not have a successor")
       | n == 1    = OmegaTwoPlusOneElement 3
       | n == 2    = OmegaTwoPlusOneElement 4
       | otherwise = OmegaTwoPlusOneElement (n + 2)

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

a :: Standard_Term
a = constant 'a'

f_x :: Standard_Term
f_x = Function 'f' (array (1, 1) [(1, Variable 'x')])

g_x :: Standard_Term
g_x = Function 'g' (array (1, 1) [(1, Variable 'x')])

f_a :: Standard_Term
f_a = Function 'f' (array (1, 1) [(1, constant 'a')])

f_omega :: Standard_Term
f_omega = Function 'f' (array (1, 1) [(1, f_omega)])

f_g_omega :: Standard_Term
f_g_omega = Function 'f' (array (1, 1) [(1, g_f_omega)])

g_f_omega :: Standard_Term
g_f_omega = Function 'g' (array (1, 1) [(1, f_g_omega)])

rule_1 = Rule f_x g_x

rule_2 = Rule a f_a

data System_1 = Sys1

instance RewriteSystem Char Char System_1 where
    rules Sys1 = [rule_1]

data System_2 = Sys2

instance RewriteSystem Char Char System_2 where
    rules Sys2 = [rule_1, rule_2]

red_1 :: Reduction Char Char System_1 OmegaTwoPlusOne
red_1 = Red ts (zip ps rs) zero
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

red_2 :: Reduction Char Char System_2 OmegaTwoPlusOne
red_2 = Red ts (zip ps rs) zero
    where ps = step 0
              where step 0 = error("undefined step") : step 1
                    step n
                        | even n = NatStr (ones ((n - 2) `div` 2))
                                   : step (n + 1)
                        | odd n  = NatStr (ones ((n - 1) `div` 2))
                                   : step (n + 1)
                            where ones 0 = []
                                  ones n = 1 : (ones (n - 1))
          rs = rule_2 : rule_1 : rs
          ts = term 0
              where term 0 = error("Undefined term") : term 1
                    term n
                        | even n = f_n (n `div` 2 - 1) : term (n + 1)
                        | odd n  = g_n ((n - 1) `div` 2) : term (n + 1)
                            where f_n 0 = a
                                  f_n n = c_f (f_n (n - 1))
                                  g_n 0 = f_omega
                                  g_n n = c_g (g_n (n - 1))
                                  c_f t = Function 'f' (array (1, 1) [(1, t)])
                                  c_g t = Function 'g' (array (1, 1) [(1, t)]) 

cred_1 = CRed red_1 modulus
    where modulus (OmegaTwoPlusOneElement n)
              | n == 1 = (\m -> OmegaTwoPlusOneElement (4 + (m * 2)))
              | n == 2 = (\m -> OmegaTwoPlusOneElement (3 + (m * 2)))
              | otherwise = error("Invalid input to modulus")

cred_2 = CRed red_2 modulus
    where modulus (OmegaTwoPlusOneElement n)
              | n == 1 = (\m -> OmegaTwoPlusOneElement (4 + (m * 2)))
              | n == 2 = (\m -> OmegaTwoPlusOneElement (3 + (m * 2)))
              | otherwise = error("Invalid input to modulus")

show_steps (CRed (Red _ s _) _) = s
