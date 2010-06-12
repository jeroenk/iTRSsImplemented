-- Plumbing

class MyShow a where
    myshow :: a -> String

instance MyShow Char where
    myshow x = [x]

-- Signatures and variables

class Signature s where
    arity :: s -> Int

class Eq v => Variables v

data (Signature s, Variables v) => Symbols s v =
    FunctionSymbol s
    | VariableSymbol v

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (Symbols s v) where
    show (FunctionSymbol f) = myshow f
    show (VariableSymbol x) = myshow x

-- Terms

data (Signature s, Variables v) => Terms s v =
    Function s [Terms s v]
    | Variable v

constant :: (Signature s, Variables v) => s -> Terms s v
constant c = if arity(c) == 0
             then Function c []
             else error "Input is not a constant"

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (Terms s v) where
    show (Function f []) = myshow f
    show (Function f xs)  = myshow f ++ "(" ++ (show' xs True) ++ ")"
        where show' [] _         = ""
              show' (x:xs) True  = show x ++ show' xs False
              show' (x:xs) False = "," ++ show x ++ show' xs False
    show (Variable v)   = myshow v

-- Strings of natural numbers

data NatStrings = NatString [Int]

instance Show NatStrings where
    show (NatString ns) = show ns

length_string :: NatStrings -> Int
length_string (NatString x) = length x

prefix_position :: Int -> NatStrings -> NatStrings
prefix_position n (NatString ns) = NatString (n:ns)

suffix_position :: Int -> NatStrings -> NatStrings
suffix_position n (NatString ns) = NatString (ns ++ [n])

positions :: (Signature s, Variables v)
             => Terms s v -> [NatStrings]
positions (Function _ xs)
    = NatString [] : concat (prefix_positions (map positions xs) 1)
    where prefix_positions [] _
              = []
          prefix_positions (x:xs) n
              = (map (prefix_position n) x):(prefix_positions xs (succ n))
positions (Variable _)
    = [NatString []]

get_symbol :: (Signature s, Variables v)
              => Terms s v -> NatStrings -> Symbols s v
get_symbol (Function f _) (NatString [])
    = FunctionSymbol f
get_symbol (Function _ xs) (NatString (n:ns))
    = get_symbol (xs!!(pred n)) (NatString ns)
get_symbol (Variable x) (NatString [])
    = VariableSymbol x

-- Substitutions
--
-- For convenience variables may occur multiple times in substitutions. It is
-- the first instance encountered in a left to right traversal that counts.

data Substitutions s v = Substitution [(v, Terms s v)]

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (Substitutions s v) where
    show (Substitution xs) = "{" ++ show' xs True ++ "}"
        where show' [] _
                  = ""
              show' ((x, t):ss) True
                  = "(" ++ myshow x ++ ", " ++ show t ++ ")" ++ show' ss False
              show' ((x, t):ss) False
                  = ", (" ++ myshow x ++ ", " ++ show t ++ ")" ++ show' ss False

in_substitution :: Variables v
                   =>  Substitutions s v -> v -> Bool
in_substitution (Substitution []) x
    = False
in_substitution (Substitution ((y,t):ss)) x
    = if x == y then True else in_substitution (Substitution ss) x

substitute_variable :: Variables v
                       => Substitutions s v -> v -> Terms s v
substitute_variable (Substitution []) x
    = Variable x
substitute_variable (Substitution ((y,t):ss)) x
    = if x == y then t else substitute_variable (Substitution ss) x

substitute :: (Signature s, Variables v)
              => Substitutions s v -> Terms s v -> Terms s v
substitute sigma (Function f xs)
    = Function f (map (substitute sigma) xs)
substitute sigma (Variable x)
    = substitute_variable sigma x

compute_substitution :: (Signature s, Variables v)
                        => Terms s v -> Terms s v -> Substitutions s v
compute_substitution s t = Substitution (compute s t)
    where compute (Function f xs) (Function g ys)
              = concat (zipWith compute xs ys)
          compute t (Variable x)
              = [(x, t)]

-- Excursion: Rational Terms
--
-- Remark that a finite system of regular equations is a substitution where
-- the terms are not allowed to be variables.

type RegularSystems s v = Substitutions s v

rational_term :: (Signature s, Variables v)
                 => RegularSystems s v -> v -> Terms s v
rational_term sigma x = rational_term' sigma (Variable x)
    where rational_term' sigma (Variable x)
              = if in_substitution sigma x
                then rational_term' sigma (substitute_variable sigma x)
                else (Variable x)
          rational_term' sigma (Function f xs)
              = Function f (map (rational_term' sigma) xs)

-- Subterms

subterm :: (Signature s, Variables v)
           => Terms s v -> NatStrings -> Terms s v
subterm s (NatString [])
    = s
subterm (Function _ xs) (NatString (n:ns))
    = subterm (xs!!(pred n)) (NatString ns)

replace_subterm :: (Signature s, Variables v)
           => Terms s v -> Terms s v -> NatStrings -> Terms s v
replace_subterm _ t (NatString [])
    = t
replace_subterm (Function f xs) t (NatString (n:ns))
    = Function f (replace_subterm' xs t n (NatString ns))
    where replace_subterm' [] _ _ ns     = []
          replace_subterm' (x:xs) t 1 ns = (replace_subterm x t ns):xs
          replace_subterm' (x:xs) t n ns = x:(replace_subterm' xs t (pred n) ns)
replace_subterm (Variable x) t _
    = (Variable x)

-- Rewrite rules and systems

data (Signature s, Variables v) => RewriteRules s v =
    Rule (Terms s v) (Terms s v)

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (RewriteRules s v) where
    show (Rule l r) = show l ++ " -> " ++ show r

rewrite_step :: (Signature s, Variables v)
                => Terms s v -> (NatStrings, RewriteRules s v) -> Terms s v
rewrite_step s (p, Rule l r) =
    let sigma   = compute_substitution (subterm s p) l
        sigma_r = substitute sigma r
    in replace_subterm s sigma_r p

rewrite_steps :: (Signature s, Variables v)
           => Terms s v -> [(NatStrings, RewriteRules s v)] -> [Terms s v]
rewrite_steps s []     = [s]
rewrite_steps s (p:ps) = s:(rewrite_steps (rewrite_step s p) ps)

class (Signature s, Variables v) => RewriteSystem s v r where
    rules :: r -> [RewriteRules s v]

-- Reductions
--
-- Remark that we do not represent the final term of a reduction in case the
-- reduction is of length omega, as the term might be uncomputable in that
-- case.

data (Signature s, Variables v, RewriteSystem s v r) => Reductions s v r =
    Reduction [Terms s v] [(NatStrings, RewriteRules s v)]

instance (MyShow s, MyShow v, Signature s, Variables v, RewriteSystem s v r)
         => Show (Reductions s v r) where
    show (Reduction [] _) = ""
    show (Reduction ss _) = show' ss True
        where show' [] _   = ""
              show' (s:ss) True  = show s ++ show' ss False
              show' (s:ss) False = " -> " ++ show s ++ show' ss False

type Modulus = Int -> Int

data (Signature s, Variables v, RewriteSystem s v r)
     => ComputablyReductions s v r =
    ComputablyReduction (Reductions s v r) Modulus

instance (MyShow s, MyShow v, Signature s, Variables v, RewriteSystem s v r)
         => Show (ComputablyReductions s v r) where
    show (ComputablyReduction r _) = show r

final_term :: (Signature s, Variables v, RewriteSystem s v r)
              => ComputablyReductions s v r -> Terms s v
final_term (ComputablyReduction (Reduction ss _) phi)
    = final_term' ss phi (NatString [])
    where final_term' ss phi ps
              = root (get_symbol (ss!!(phi (length_string ps))) ps) ss phi ps
          root (FunctionSymbol f) ss phi ps
              = Function f (subterms (arity f) 1 ss phi ps)
          root (VariableSymbol x) _ _ _
              = Variable x
          subterms 0 _ _ _ _
              = []
          subterms n m ss phi ps
              = (final_term' ss phi (suffix_position m ps))
                :(subterms (pred n) (succ m) ss phi ps)

-- Examples

type Standard_Terms         = Terms Char Char
type Standard_Substitutions = Substitutions Char Char
type Standard_Rules         = RewriteRules Char Char

instance Signature Char where
    arity 'a' = 0
    arity 'b' = 0
    arity 'f' = 1
    arity 'g' = 1
    arity 'h' = 2
    arity _   = error "Character not in signature"

instance Variables Char

f_x :: Standard_Terms
f_x = Function 'f' [Variable 'x']

f_a :: Standard_Terms
f_a = Function 'f' [constant 'a']

g_x :: Standard_Terms
g_x = Function 'g' [Variable 'x']

f_omega :: Standard_Terms
f_omega = Function 'f' [f_omega]

h_omega :: Standard_Terms
h_omega = Function 'h' [h_omega, h_omega]

h_a_f_b :: Standard_Terms
h_a_f_b = Function 'h' [constant 'a', Function 'f' [constant 'b']]

h_x_omega :: Standard_Terms
h_x_omega = Function 'h' [Variable 'x', h_x_omega]

h_x_f_y :: Standard_Terms
h_x_f_y = Function 'h' [Variable 'x', Function 'f' [Variable 'y']]

sigma_1 :: Standard_Substitutions
sigma_1 = Substitution [('x', Function 'f' [constant 'a']), ('y', constant 'a'),
                        ('z', constant 'b')]

sigma_2 :: Standard_Substitutions
sigma_2 = Substitution [('x', f_x)]

f_omega' :: Standard_Terms
f_omega' = rational_term sigma_2 'x'

rule_1 = Rule f_x g_x

rule_2 = Rule (constant 'a') f_omega

rule_3 = Rule h_x_f_y (constant 'a')

rule_4 = Rule h_x_f_y f_x

rule_5 = Rule (constant 'a') f_a

data System_1 = Sys1

instance RewriteSystem Char Char System_1 where
    rules Sys1 = [rule_1, rule_2]

data System_2 = Sys2

instance RewriteSystem Char Char System_2 where
    rules Sys2 = [rule_3, rule_4]

data System_3 = Sys3

instance RewriteSystem Char Char System_3 where
    rules Sys3 = [rule_5]

red_1 :: (Signature Char, Variables Char, RewriteSystem Char Char System_3)
        => Reductions Char Char System_3
red_1 = Reduction ts (zip ps rs)
    where ps = (iterate (\ns -> prefix_position 1 ns) (NatString []))
          rs = repeat rule_5
          ts = rewrite_steps (constant 'a') (zip ps rs)

red_2 :: (Signature Char, Variables Char, RewriteSystem Char Char System_3)
        => Reductions Char Char System_1
red_2 = Reduction ts (zip ps rs)
    where ps = (iterate (\ns -> prefix_position 1 ns) (NatString []))
          rs = repeat rule_1
          ts = rewrite_steps (f_omega) (zip ps rs)

red_3 :: (Signature Char, Variables Char, RewriteSystem Char Char System_3)
        => Reductions Char Char System_1
red_3 = Reduction ts (zip ps rs)
    where ps = [NatString []]
          rs = [rule_4]
          ts = rewrite_steps (h_a_f_b) (zip ps rs)

cred_1 = ComputablyReduction red_1 (\x -> succ x)

cred_2 = ComputablyReduction red_2 (\x -> succ x)

cred_3 = ComputablyReduction red_3 (\x -> 1)
