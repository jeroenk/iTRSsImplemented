-- Plumbing

class MyShow a where
    myshow :: a -> String

instance MyShow Char where
    myshow x = [x]

-- Signatures and variables

class Signature s where
    arity :: s -> Int

class Eq v => Variables v

data (Signature s, Variables v) => Symbol s v =
    FunctionSymbol s
    | VariableSymbol v

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (Symbol s v) where
    show (FunctionSymbol f) = myshow f
    show (VariableSymbol x) = myshow x

-- Terms

data (Signature s, Variables v) => Term s v =
    Function s [Term s v]
    | Variable v

constant :: (Signature s, Variables v) => s -> Term s v
constant c | arity(c) == 0 = Function c []
           | otherwise     = error "Input is not a constant"

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (Term s v) where
    show (Function f []) = myshow f
    show (Function f xs)  = myshow f ++ "(" ++ (show' xs True) ++ ")"
        where show' [] _         = ""
              show' (x:xs) True  = show x ++ show' xs False
              show' (x:xs) False = "," ++ show x ++ show' xs False
    show (Variable v)   = myshow v

less_depth :: (Signature s, Variables v)
              => Int -> Term s v -> Bool
less_depth n (Function _ xs)
    = if n <= 1 then False else and (map (less_depth (pred n)) xs)
less_depth n (Variable _)
    = if n <= 1 then False else True

-- Strings of natural numbers

data NatString = NatString [Int]

instance Eq NatString where
    (NatString ns) == (NatString ms) = ns == ms

instance Show NatString where
    show (NatString ns) = show ns

string_length :: NatString -> Int
string_length (NatString ns) = length ns

prefix_position :: Int -> NatString -> NatString
prefix_position n (NatString ns) = NatString (n:ns)

is_prefix :: NatString -> NatString -> Bool
is_prefix (NatString ns) (NatString ms) = is_prefix' ns ms
    where is_prefix' [] _          = True
          is_prefix' (_:_) []      = False
          is_prefix' (n:ns) (m:ms) = if n == m then is_prefix' ns ms else False

position_of_term :: (Signature s, Variables v)
                    => Term s v -> NatString -> Bool
position_of_term _ (NatString [])
    = True
position_of_term (Function f xs) (NatString (n:ns))
    | n < 1 || n > arity(f) = False
    | otherwise             = position_of_term (xs!!(pred n)) (NatString ns)
position_of_term (Variable _) (NatString (_:_))
    = False

positions :: (Signature s, Variables v)
             => Term s v -> [NatString]
positions (Function _ xs)
    = NatString [] : concat (prefix_positions (map positions xs) 1)
    where prefix_positions [] _
              = []
          prefix_positions (x:xs) n
              = (map (prefix_position n) x):(prefix_positions xs (succ n))
positions (Variable _)
    = [NatString []]

get_symbol :: (Signature s, Variables v)
              => Term s v -> NatString -> Symbol s v
get_symbol (Function f _) (NatString [])
    = FunctionSymbol f
get_symbol (Function f xs) (NatString (n:ns))
    | n >= 1 && n <= arity(f) = get_symbol (xs!!(pred n)) (NatString ns)
    | otherwise               = error "Getting symbol at non-existing position"
get_symbol (Variable x) (NatString [])
    = VariableSymbol x

-- Substitutions
--
-- For convenience variables may occur multiple times in substitutions. It is
-- the first instance encountered in a left to right traversal that counts.

data Substitution s v = Substitution [(v, Term s v)]

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (Substitution s v) where
    show (Substitution xs) = "{" ++ show' xs True ++ "}"
        where show' [] _
                  = ""
              show' ((x, t):ss) True
                  = "(" ++ myshow x ++ ", " ++ show t ++ ")" ++ show' ss False
              show' ((x, t):ss) False
                  = ", (" ++ myshow x ++ ", " ++ show t ++ ")" ++ show' ss False

in_substitution :: Variables v
                   =>  Substitution s v -> v -> Bool
in_substitution (Substitution []) x
    = False
in_substitution (Substitution ((y,t):ss)) x
    = if x == y then True else in_substitution (Substitution ss) x

substitute_variable :: Variables v
                       => Substitution s v -> v -> Term s v
substitute_variable (Substitution []) x
    = Variable x
substitute_variable (Substitution ((y,t):ss)) x
    = if x == y then t else substitute_variable (Substitution ss) x

substitute :: (Signature s, Variables v)
              => Substitution s v -> Term s v -> Term s v
substitute sigma (Function f xs)
    = Function f (map (substitute sigma) xs)
substitute sigma (Variable x)
    = substitute_variable sigma x

compute_substitution :: (Signature s, Variables v)
                        => Term s v -> Term s v -> Substitution s v
compute_substitution s t = Substitution (compute s t)
    where compute (Function f xs) (Function g ys)
              = concat (zipWith compute xs ys)
          compute t (Variable x)
              = [(x, t)]

-- Excursion: Rational Terms
--
-- Remark that a finite system of regular equations is a substitution where
-- the terms are not allowed to be variables.

type RegularSystem s v = Substitution s v

rational_term :: (Signature s, Variables v)
                 => RegularSystem s v -> v -> Term s v
rational_term sigma x = rational_term' (Variable x)
    where rational_term' (Variable x)
              = if in_substitution sigma x
                then rational_term' (substitute_variable sigma x)
                else (Variable x)
          rational_term' (Function f xs)
              = Function f (map rational_term' xs)

-- Subterms

subterm :: (Signature s, Variables v)
           => Term s v -> NatString -> Term s v
subterm s (NatString [])
    = s
subterm (Function f xs) (NatString (n:ns))
    | n >= 1 && n <= arity(f) = subterm (xs!!(pred n)) (NatString ns)
    | otherwise               = error "Getting non-existing subterm"

replace_subterm :: (Signature s, Variables v)
           => Term s v -> Term s v -> NatString -> Term s v
replace_subterm _ t (NatString [])
    = t
replace_subterm (Function f xs) t (NatString (n:ns))
    = Function f (replace_subterm' xs t n (NatString ns))
    where replace_subterm' (x:xs) t 1 ns
              = (replace_subterm x t ns):xs
          replace_subterm' (x:xs) t n ns
              = x:(replace_subterm' xs t (pred n) ns)
          replace_subterm' _ _ _ _
              = error "Replacing non-existing subterm"
replace_subterm (Variable x) t _
    = (Variable x)

-- Rewrite rules and systems

data (Signature s, Variables v) => RewriteRule s v =
    Rule (Term s v) (Term s v)

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (RewriteRule s v) where
    show (Rule l r) = show l ++ " -> " ++ show r

left_height :: (Signature s, Variables v)
               => RewriteRule s v -> Int
left_height (Rule l _) = term_height l
    where term_height (Function _ xs) = 1 + foldl max 0 (map term_height xs)
          term_height (Variable _)    = 0

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
-- Remark that we do not represent the final term of a reduction in case the
-- reduction is of length omega, as the term might be uncomputable in that
-- case.
--
-- We assume the steps and terms in reductions to be indexed starting from 0.

data (Signature s, Variables v, RewriteSystem s v r) => Reduction s v r =
    Reduction [Term s v] [Step s v]

instance (MyShow s, MyShow v, Signature s, Variables v, RewriteSystem s v r)
         => Show (Reduction s v r) where
    show (Reduction [] _) = ""
    show (Reduction ss _) = show' ss True
        where show' [] _   = ""
              show' (s:ss) True  = show s ++ show' ss False
              show' (s:ss) False = " -> " ++ show s ++ show' ss False

type Modulus = Int -> Int

data (Signature s, Variables v, RewriteSystem s v r)
     => ComputablyReduction s v r =
    ComputablyReduction (Reduction s v r) Modulus

instance (MyShow s, MyShow v, Signature s, Variables v, RewriteSystem s v r)
         => Show (ComputablyReduction s v r) where
    show (ComputablyReduction r _) = show r

initial_term :: (Signature s, Variables v, RewriteSystem s v r)
                => ComputablyReduction s v r -> Term s v
initial_term (ComputablyReduction (Reduction (x:_) _) _) = x

final_term :: (Signature s, Variables v, RewriteSystem s v r)
              => ComputablyReduction s v r -> Term s v
final_term (ComputablyReduction (Reduction ss _) phi)
    = final_subterm []
    where final_subterm ps
              = root (root_symbol (phi (length ps)) ps) ps
          root_symbol n ps
              = get_symbol (ss!!n) (NatString ps)
          root (FunctionSymbol f) ps
              = Function f (subterms (arity f) 1 ps)
          root (VariableSymbol x) _
              = Variable x
          subterms 0 _ _
              = []
          subterms n m ps
              = (final_subterm (ps ++ [m])):(subterms (pred n) (succ m) ps)

-- Descendants

descendants_of_position :: (Signature s, Variables v)
                           => NatString -> Step s v -> [NatString]
descendants_of_position ps (qs, (Rule l r))
    = map (\xs -> NatString xs) (descendants' ps qs (is_prefix qs ps))
    where descendants' (NatString ps) _ False
              = [ps]
          descendants' (NatString ps) (NatString qs) True
              = map (\xs -> qs ++ xs) (compute_new (drop (length qs) ps))
          compute_new ps = compute_new' ps (get_variable l ps)
              where get_variable (Function _ _) []
                        = Nothing
                    get_variable (Function _ xs) (p:ps)
                        = get_variable (xs!!(pred p)) ps
                    get_variable (Variable x) _
                        = Just x
          compute_new' ps Nothing  = []
          compute_new' ps (Just x) = new_positions r x (get_position l ps) []
              where get_position (Function _ xs) (p:ps)
                        = get_position (xs!!(pred p)) ps
                    get_position (Variable _) ps
                        = ps
          new_positions (Variable x) y ps qs
              = if x == y then [qs ++ ps] else []
          new_positions (Function _ xs) y ps qs
              = concat (new_positions' xs y ps qs 1)
          new_positions' [] _ _ _ _
              = []
          new_positions' (x:xs) y ps qs n
              = (new_positions x y ps (qs ++ [n]))
                :(new_positions' xs y ps qs (succ n))

descendants_across_step :: (Signature s, Variables v)
                           => [NatString] -> Step s v -> [NatString]
descendants_across_step [] _
    = []
descendants_across_step (p:ps) s
    = (descendants_of_position p s) ++ (descendants_across_step ps s)

descendants :: (Signature s, Variables v)
               => [NatString] -> [Step s v] -> [NatString]
descendants ps []     = ps
descendants ps (q:qs) = descendants (descendants_across_step ps q) qs

-- Strip Lemma

sequence_steps :: (Signature s, Variables v)
                  => [NatString] -> RewriteRule s v -> [Step s v]
sequence_steps [] _     = []
sequence_steps (p:ps) r = (p, r):(sequence_steps ps r)

bottom_develop :: (Signature s, Variables v, RewriteSystem s v r)
                  => ComputablyReduction s v r -> Step s v -> [[Step s v]]
bottom_develop (ComputablyReduction rs _) (q, r)
    = bottom_develop' rs q
    where bottom_develop' (Reduction _ ps) q
              = steps ps [q]
          steps [] _
              = []
          steps ((p, r'):ps) qs
              = bottom_steps:(steps ps descendants_qs)
              where down_steps     = sequence_steps qs r
                    descendants_p  = descendants [p] down_steps
                    bottom_steps   = sequence_steps descendants_p r'
                    descendants_qs = descendants qs [(p, r')]

bottom_steps :: (Signature s, Variables v, RewriteSystem s v r)
                => ComputablyReduction s v r -> Step s v -> [Step s v]
bottom_steps rs s
    = concat (bottom_develop rs s)

bottom_modulus :: (Signature s, Variables v, RewriteSystem s v r)
                  => ComputablyReduction s v r -> Step s v -> Modulus
bottom_modulus rs@(ComputablyReduction _ phi) s@(_, r) n
    = length (concat (take (phi (n + left_height r)) (bottom_develop rs s)))

bottom_reduction :: (Signature s, Variables v, RewriteSystem s v r)
                    => ComputablyReduction s v r -> Step s v
                    -> ComputablyReduction s v r
bottom_reduction r s
    = ComputablyReduction reduction modulus
    where reduction = Reduction terms steps
          terms = (rewrite_steps (rewrite_step (initial_term r) s) steps)
          steps = bottom_steps r s
          modulus = bottom_modulus r s

right_develop :: (Signature s, Variables v, RewriteSystem s v r)
                 => ComputablyReduction s v r -> Step s v -> [[Step s v]]
right_develop (ComputablyReduction rs phi) (q, r)
    = right_develop' rs q r
    where right_develop' (Reduction _ ps) q r
              = steps ps [q] 0 0
          steps _ [] _ _
              = []
          steps ps qs m d
              = right_steps:(steps ps_left descendants_nd m_new (succ d))
              where m_new          = max m (phi d)
                    ps_use         = take (m_new - m) ps
                    ps_left        = drop (m_new - m) ps
                    descendants_qs = descendants qs ps_use
                    descendants_d  = filter at_d descendants_qs
                        where at_d (NatString qs) = (length qs) == d
                    descendants_nd = filter not_at_d descendants_qs
                        where not_at_d (NatString qs) = (length qs) /= d
                    right_steps = sequence_steps descendants_d r

right_steps :: (Signature s, Variables v, RewriteSystem s v r)
               => ComputablyReduction s v r -> Step s v -> [Step s v]
right_steps rs s
    = concat (right_develop rs s)

right_modulus :: (Signature s, Variables v, RewriteSystem s v r)
                 => ComputablyReduction s v r -> Step s v -> Modulus
right_modulus rs s n
    = length (concat (take (succ n) (right_develop rs s)))

right_reduction :: (Signature s, Variables v, RewriteSystem s v r)
                   => ComputablyReduction s v r -> Step s v
                   -> ComputablyReduction s v r
right_reduction r s
    = ComputablyReduction reduction modulus
    where reduction = Reduction terms steps
          terms = (rewrite_steps (final_term r) steps)
          steps = right_steps r s
          modulus = right_modulus r s

strip_lemma :: (Signature s, Variables v, RewriteSystem s v r)
               => r -> ComputablyReduction s v r -> Step s v
               -> (ComputablyReduction s v r, ComputablyReduction s v r)
strip_lemma _ r s = (bottom_reduction r s, right_reduction r s)

-- Confluence

accumulate_depth :: (Signature s, Variables v, RewriteSystem s v r)
                    => ComputablyReduction s v r -> Int -> ([Step s v], Int)
accumulate_depth  (ComputablyReduction (Reduction _ ps) phi) d
    = needed_steps (pred (phi d)) ps d
    where needed_steps (-1) _ d
              = ([], d)
          needed_steps n (p:ps) d
              | relevant  = (p:steps, d_new)
              | otherwise = (steps, d_later)
                  where (steps, d_later) = needed_steps (pred n) ps d
                        redex_depth = string_length (fst p)
                        relevant = redex_depth <= d_later
                        rule_height = left_height (snd p)
                        d_new = max d_later (redex_depth + rule_height - 1)

needed_depth :: (Signature s, Variables v, RewriteSystem s v r)
                => ComputablyReduction s v r -> Int -> Int
needed_depth s d = snd (accumulate_depth s d)

get_steps_to_depth :: (Signature s, Variables v, RewriteSystem s v r)
                      => ComputablyReduction s v r -> Int -> [Step s v]
get_steps_to_depth s d = fst (accumulate_depth s d)

filter_steps :: (Signature s, Variables v, RewriteSystem s v r)
                => r -> ComputablyReduction s v r -> [Step s v] -> Int
                -> [Step s v]
filter_steps r s [] d     = get_steps_to_depth s d
filter_steps r s (p:ps) d = filter_steps r s' ps d
    where s' = fst (strip_lemma r s p)

confl_devel :: (Signature s, Variables v, RewriteSystem s v r)
               => r -> ComputablyReduction s v r -> ComputablyReduction s v r
               -> [[Step s v]]
confl_devel r (ComputablyReduction (Reduction _ ps) phi_s) t
    = confl_devel' t ps 0 0 []
    where confl_devel' t ps d n prev
              | steps_needed = new:(confl_devel' t ps (succ d) n prev_new)
              | otherwise    = confl_devel' t' (tail ps) d (succ n) prev
                    where steps_needed = (phi_s (needed_depth t d)) <= n
                          new = filter_steps r t prev d
                          prev_new = prev ++ new
                          t' = fst (strip_lemma r t (head ps))

confl_steps :: (Signature s, Variables v, RewriteSystem s v r)
              => r -> ComputablyReduction s v r -> ComputablyReduction s v r
              -> [Step s v]
confl_steps r s t = concat (confl_devel r s t)

confl_modulus :: (Signature s, Variables v, RewriteSystem s v r)
                 => r -> ComputablyReduction s v r
                 -> ComputablyReduction s v r -> Modulus
confl_modulus r s t n = length (concat (take (succ n) (confl_devel r s t)))

confl_side :: (Signature s, Variables v, RewriteSystem s v r)
              => r -> ComputablyReduction s v r -> ComputablyReduction s v r
              -> ComputablyReduction s v r
confl_side r s t = ComputablyReduction reduction modulus
    where reduction = Reduction terms steps
          terms = (rewrite_steps (final_term s) steps)
          steps = confl_steps r s t
          modulus = confl_modulus r s t

confluence :: (Signature s, Variables v, RewriteSystem s v r)
              => r -> (ComputablyReduction s v r, ComputablyReduction s v r)
              -> (ComputablyReduction s v r, ComputablyReduction s v r)
confluence r (s, t) = (confl_side r s t, confl_side r t s)

-- Examples

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
f_x = Function 'f' [Variable 'x']

f_a :: Standard_Term
f_a = Function 'f' [constant 'a']

g_x :: Standard_Term
g_x = Function 'g' [Variable 'x']

h_x_x :: Standard_Term
h_x_x = Function 'h' [Variable 'x', Variable 'x']

f_omega :: Standard_Term
f_omega = Function 'f' [f_omega]

h_omega :: Standard_Term
h_omega = Function 'h' [h_omega, h_omega]

h_a_f_b :: Standard_Term
h_a_f_b = Function 'h' [constant 'a', Function 'f' [constant 'b']]

h_x_omega :: Standard_Term
h_x_omega = Function 'h' [Variable 'x', h_x_omega]

h_x_f_y :: Standard_Term
h_x_f_y = Function 'h' [Variable 'x', Function 'f' [Variable 'y']]

h_x_f_x :: Standard_Term
h_x_f_x = Function 'h' [Variable 'x', Function 'f' [Variable 'x']]

h_x_h_a_x :: Standard_Term
h_x_h_a_x = Function 'h' [Variable 'x',
                          Function 'h' [constant 'a', Variable 'x']]

sigma_1 :: Standard_Substitution
sigma_1 = Substitution [('x', Function 'f' [constant 'a']), ('y', constant 'a'),
                        ('z', constant 'b')]

sigma_2 :: Standard_Substitution
sigma_2 = Substitution [('x', f_x)]

f_omega' :: Standard_Term
f_omega' = rational_term sigma_2 'x'

rule_1 = Rule f_x g_x

rule_2 = Rule (constant 'a') f_omega

rule_3 = Rule h_x_f_y (constant 'a')

rule_4 = Rule h_x_f_y f_x

rule_5 = Rule (constant 'a') f_a

rule_6 = Rule f_x h_x_h_a_x

rule_7 = Rule f_x h_x_x

rule_8 = Rule f_x (constant 'a')

rule_9 = Rule f_x h_x_f_x

rule_10 :: Standard_Rule
rule_10 = Rule (constant 'a') (constant 'b')

rule_11 :: Standard_Rule
rule_11 = Rule (constant 'b') (constant 'c')

data System_1 = Sys1

instance RewriteSystem Char Char System_1 where
    rules Sys1 = [rule_1, rule_2]

data System_2 = Sys2

instance RewriteSystem Char Char System_2 where
    rules Sys2 = [rule_3, rule_4]

data System_3 = Sys3

instance RewriteSystem Char Char System_3 where
    rules Sys3 = [rule_5, rule_6, rule_7, rule_8, rule_9, rule_10, rule_11]

red_1 :: (Signature Char, Variables Char, RewriteSystem Char Char System_3)
        => Reduction Char Char System_3
red_1 = Reduction ts (zip ps rs)
    where ps = (iterate (\ns -> prefix_position 1 ns) (NatString [1]))
          rs = repeat rule_5
          ts = rewrite_steps (Function 'f' [constant 'a']) (zip ps rs)

red_2 :: (Signature Char, Variables Char, RewriteSystem Char Char System_3)
        => Reduction Char Char System_1
red_2 = Reduction ts (zip ps rs)
    where ps = (iterate (\ns -> prefix_position 1 ns) (NatString []))
          rs = repeat rule_1
          ts = rewrite_steps (f_omega) (zip ps rs)

red_3 :: (Signature Char, Variables Char, RewriteSystem Char Char System_3)
        => Reduction Char Char System_1
red_3 = Reduction ts (zip ps rs)
    where ps = [NatString [1], NatString [1]]
          rs = [rule_4, rule_6]
          ts = rewrite_steps (Function 'f' [h_a_f_b]) (zip ps rs)

red_4 :: (Signature Char, Variables Char, RewriteSystem Char Char System_3)
        => Reduction Char Char System_3
red_4 = Reduction ts (zip ps rs)
    where ps = [NatString [], NatString [2], NatString [2,2]]
          rs = [rule_9, rule_9, rule_9]
          ts = rewrite_steps (Function 'f' [constant 'a']) (zip ps rs)

red_5 :: (Signature Char, Variables Char, RewriteSystem Char Char System_3)
        => Reduction Char Char System_3
red_5 = Reduction ts (zip ps rs)
    where ps = [NatString [1], NatString [1]]
          rs = [rule_10, rule_11]
          ts = rewrite_steps (Function 'f' [constant 'a']) (zip ps rs)

red_6 :: (Signature Char, Variables Char, RewriteSystem Char Char System_1)
        => Reduction Char Char System_1
red_6 = Reduction ts (zip ps rs)
    where ps = (NatString []):(map (\p -> prefix_position 1 (prefix_position 1 p)) ps)
          rs = rule_1:rs
          ts = rewrite_steps f_omega (zip ps rs)

red_7 :: (Signature Char, Variables Char, RewriteSystem Char Char System_1)
        => Reduction Char Char System_1
red_7 = Reduction ts (zip ps rs)
    where ps = (NatString [1]):(map (\p -> prefix_position 1 (prefix_position 1 p)) ps)
          rs = rule_1:rs
          ts = rewrite_steps f_omega (zip ps rs)

cred_1 = ComputablyReduction red_1 (\x -> succ x)

cred_2 = ComputablyReduction red_2 (\x -> succ x)

cred_3 = ComputablyReduction red_3 (\x -> 2)

cred_4 = ComputablyReduction red_4 (\x -> min 3 (succ x))

cred_5 = ComputablyReduction red_5 (\x -> if x == 0 then 0 else 2)

cred_6 = ComputablyReduction red_6 (\x -> succ x)

cred_7 = ComputablyReduction red_7 (\x -> x)

show_steps (ComputablyReduction (Reduction _ s) _) = s
