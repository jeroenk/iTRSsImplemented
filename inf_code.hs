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

import MyShow
import SignatureAndVariables
import Terms
import Array
import List

-- Plumbing

instance MyShow Char where
    myshow x = [x]

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

pos :: (Signature s, Variables v) => Term s v -> [NatString]
pos (Function _ xs)
    = NatStr [] : concat (prefix_positions (map pos (elems xs)) 1)
    where prefix_positions [] _
              = []
          prefix_positions (x:xs) n
              = (map (prefix_position n) x):(prefix_positions xs (succ n))
pos (Variable _)
    = [NatStr []]

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

in_substitution :: Variables v =>  Substitution s v -> v -> Bool
in_substitution (Subst []) x
    = False
in_substitution (Subst ((y,t):ss)) x
    = if x == y then True else in_substitution (Subst ss) x

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

-- Excursion: Rational Terms
--
-- Remark that a finite system of regular equations is a substitution where
-- the terms are not allowed to be variables.

type RegularSystem s v = Substitution s v

rational_term :: (Signature s, Variables v)
    => RegularSystem s v -> v -> Term s v
rational_term sigma x = rational (Variable x)
    where rational (Variable x)
              | in_substitution sigma x = rational (substitute_variable sigma x)
              | otherwise               = (Variable x)
          rational (Function f xs)
              = Function f (xs // [(i, rational (xs!i)) | i <- indices xs])

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

left_height :: (Signature s, Variables v) => RewriteRule s v -> Int
left_height (Rule l _) = term_height l

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
-- reduction is of length omega, the term might be uncomputable.
--
-- We assume the steps and terms in reductions to be indexed starting from 0.

data (Signature s, Variables v, RewriteSystem s v r) => Reduction s v r
    = Red [Term s v] [Step s v]

instance (MyShow s, MyShow v, Signature s, Variables v, RewriteSystem s v r)
         => Show (Reduction s v r) where
    show (Red [] _) = ""
    show (Red ss _) = show' ss True
        where show' [] _   = ""
              show' (s:ss) True  = show s ++ show' ss False
              show' (s:ss) False = " -> " ++ show s ++ show' ss False

type Modulus = Int -> Int

data (Signature s, Variables v, RewriteSystem s v r) => ComputReduction s v r
    = CRed (Reduction s v r) Modulus

instance (MyShow s, MyShow v, Signature s, Variables v, RewriteSystem s v r)
         => Show (ComputReduction s v r) where
    show (CRed (Red ts _) phi) = show' ts 0 0 (head ts)
        where show' [] _ _ _
                  = ""
              show' ts n d l
                  | less_height l d = (if n == 0 then "" else " -> ") ++ show l
                  | otherwise      = (show_d ts n d) ++ (show' ts' n' d' l')
                      where n' = max n (phi d)
                            d' = succ d
                            l' = head (drop ((n' - n) - 1) ts)
                            ts' = drop (n' - n) ts
              show_d ts n d
                  | (n' - n) < 1 = ""
                  | otherwise    = show_steps (take (n' - n) ts) n
                      where n' = max n (phi d)
              show_steps [] _     = ""
              show_steps (t:ts) 0 = show t ++ show_steps ts 1
              show_steps (t:ts) n = " -> " ++ show t ++ show_steps ts (succ n)

initial_term :: (Signature s, Variables v, RewriteSystem s v r)
    => ComputReduction s v r -> Term s v
initial_term (CRed (Red (x:_) _) _) = x

final_term :: (Signature s, Variables v, RewriteSystem s v r)
    => ComputReduction s v r -> Term s v
final_term (CRed (Red ts _) phi)
    = final_subterm [] 0 ts
    where final_subterm ps n ts
              = root root_symbol ps n' ts'
                  where n' = max n (phi (length ps))
                        ts' = drop (n' - n) ts
                        root_symbol = get_symbol (head ts') (NatStr ps)
          root (FunctionSymbol f) ps n ts
              = Function f (subterms (arity f) ps n ts)
          root (VariableSymbol x) _ _ _
              = Variable x
          subterms a ps n ts
              = array (1, a) [(i, final_subterm (ps ++ [i]) n ts) | i <- [1..a]]

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

-- Strip Lemma

sequence_steps :: (Signature s, Variables v)
    => [NatString] -> RewriteRule s v -> [Step s v]
sequence_steps [] _     = []
sequence_steps (p:ps) r = (p, r):(sequence_steps ps r)

bottom_develop :: (Signature s, Variables v, RewriteSystem s v r)
    => ComputReduction s v r -> Step s v -> [[Step s v]]
bottom_develop (CRed rs _) (q, r)
    = bottom_develop' rs q
    where bottom_develop' (Red _ ps) q
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
    => ComputReduction s v r -> Step s v -> [Step s v]
bottom_steps rs s
    = concat (bottom_develop rs s)

bottom_modulus :: (Signature s, Variables v, RewriteSystem s v r)
    => ComputReduction s v r -> Step s v -> Modulus
bottom_modulus rs@(CRed _ phi) s@(_, r) n
    = length (concat (take (phi (n + left_height r)) (bottom_develop rs s)))

bottom_reduction :: (Signature s, Variables v, RewriteSystem s v r)
    => ComputReduction s v r -> Step s v -> ComputReduction s v r
bottom_reduction r s
    = CRed reduction modulus
    where reduction = Red terms steps
          terms = (rewrite_steps (rewrite_step (initial_term r) s) steps)
          steps = bottom_steps r s
          modulus = bottom_modulus r s

right_develop :: (Signature s, Variables v, RewriteSystem s v r)
    => ComputReduction s v r -> Step s v -> [[Step s v]]
right_develop (CRed rs phi) (q, r)
    = right_develop' rs q r
    where right_develop' (Red _ ps) q r
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
                        where at_d (NatStr qs) = (length qs) == d
                    descendants_nd = filter not_at_d descendants_qs
                        where not_at_d (NatStr qs) = (length qs) /= d
                    right_steps = sequence_steps descendants_d r

right_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => ComputReduction s v r -> Step s v -> [Step s v]
right_steps rs s
    = concat (right_develop rs s)

right_modulus :: (Signature s, Variables v, RewriteSystem s v r)
    => ComputReduction s v r -> Step s v -> Modulus
right_modulus rs s n
    = length (concat (take (succ n) (right_develop rs s)))

right_reduction :: (Signature s, Variables v, RewriteSystem s v r)
    => ComputReduction s v r -> Step s v -> ComputReduction s v r
right_reduction r s
    = CRed reduction modulus
    where reduction = Red terms steps
          terms = (rewrite_steps (final_term r) steps)
          steps = right_steps r s
          modulus = right_modulus r s

strip_lemma :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> ComputReduction s v r -> Step s v
               -> (ComputReduction s v r, ComputReduction s v r)
strip_lemma _ r s = (bottom_reduction r s, right_reduction r s)

-- Confluence

accumulate_essential :: (Signature s, Variables v, RewriteSystem s v r)
    => ComputReduction s v r -> Int -> ([Step s v], [NatString])
accumulate_essential (CRed (Red ts ps) phi) d
    = needed_steps used_steps last_pos
    where used_steps = take (phi d) ps
          last_term  = last (rewrite_steps (head ts) used_steps)
          last_pos   = pos_to_depth last_term d
          needed_steps [] qs
              = ([], qs)
          needed_steps (p@(p', _):ps) qs
              = (ps_new, qs_new)
              where (ps', qs') = needed_steps ps qs
                    qs_new = origin_across_step qs' p
                    ps_new
                        | p' `elem` qs_new = p : ps'
                        | otherwise        = ps'

needed_depth :: (Signature s, Variables v, RewriteSystem s v r)
    => ComputReduction s v r -> Int -> Int
needed_depth s d = maximum (map string_length (snd (accumulate_essential s d)))

get_steps_to_depth :: (Signature s, Variables v, RewriteSystem s v r)
    => ComputReduction s v r -> Int -> [Step s v]
get_steps_to_depth s d = fst (accumulate_essential s d)

filter_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> ComputReduction s v r -> [Step s v] -> Int -> [Step s v]
filter_steps r s [] d     = get_steps_to_depth s d
filter_steps r s (p:ps) d = filter_steps r s' ps d
    where s' = fst (strip_lemma r s p)

confl_devel :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> ComputReduction s v r -> ComputReduction s v r -> [[Step s v]]
confl_devel r (CRed (Red _ ps) phi_s) t
    = confl_devel' t ps 0 0 []
    where confl_devel' t ps d n prev
              | steps_needed = new:(confl_devel' t ps (succ d) n prev_new)
              | otherwise    = confl_devel' t' (tail ps) d (succ n) prev
                    where steps_needed = (phi_s (needed_depth t d)) <= n
                          new = filter_steps r t prev d
                          prev_new = prev ++ new
                          t' = fst (strip_lemma r t (head ps))

confl_steps :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> ComputReduction s v r -> ComputReduction s v r -> [Step s v]
confl_steps r s t = concat (confl_devel r s t)

confl_modulus :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> ComputReduction s v r -> ComputReduction s v r -> Modulus
confl_modulus r s t n = length (concat (take (succ n) (confl_devel r s t)))

confl_side :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> ComputReduction s v r -> ComputReduction s v r
              -> ComputReduction s v r
confl_side r s t = CRed reduction modulus
    where reduction = Red terms steps
          terms = (rewrite_steps (final_term s) steps)
          steps = confl_steps r s t
          modulus = confl_modulus r s t

confluence :: (Signature s, Variables v, RewriteSystem s v r)
    => r -> (ComputReduction s v r, ComputReduction s v r)
              -> (ComputReduction s v r, ComputReduction s v r)
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
f_x = Function 'f' (array (1, 1) [(1, Variable 'x')])

f_y :: Standard_Term
f_y = Function 'f' (array (1, 1) [(1, Variable 'y')])

f_a :: Standard_Term
f_a = Function 'f' (array (1, 1) [(1, constant 'a')])

f_b :: Standard_Term
f_b = Function 'f' (array (1, 1) [(1, constant 'b')])

g_x :: Standard_Term
g_x = Function 'g' (array (1, 1) [(1, Variable 'x')])

h_x_x :: Standard_Term
h_x_x = Function 'h' (array (1, 2) [(1, Variable 'x'), (2, Variable 'x')])

f_omega :: Standard_Term
f_omega = Function 'f' (array (1, 1) [(1, f_omega)])

h_omega :: Standard_Term
h_omega = Function 'h' (array (1, 2) [(1, h_omega), (2, h_omega)])

h_a_f_b :: Standard_Term
h_a_f_b = Function 'h' (array (1, 2) [(1, constant 'a'), (2, f_b)])

f_h_a_f_b :: Standard_Term
f_h_a_f_b = Function 'f' (array (1, 1) [(1, h_a_f_b)])

h_x_omega :: Standard_Term
h_x_omega = Function 'h' (array (1, 2) [(1, Variable 'x'), (2, h_x_omega)])

h_x_f_y :: Standard_Term
h_x_f_y = Function 'h' (array (1, 2) [(1, Variable 'x'), (2, f_y)])

h_x_f_x :: Standard_Term
h_x_f_x = Function 'h' (array (1, 2) [(1, Variable 'x'), (2, f_x)])

h_a_x :: Standard_Term
h_a_x = Function 'h' (array (1, 2) [(1, constant 'a'), (2, Variable 'x')])

h_x_h_a_x :: Standard_Term
h_x_h_a_x = Function 'h' (array (1, 2) [(1, Variable 'x'), (2, h_a_x)])

sigma_1 :: Standard_Substitution
sigma_1 = Subst [('x', f_a), ('y', constant 'a'), ('z', constant 'b')]

sigma_2 :: Standard_Substitution
sigma_2 = Subst [('x', f_x)]

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

red_1 :: Reduction Char Char System_3
red_1 = Red ts (zip ps rs)
    where ps = (iterate (\ns -> prefix_position 1 ns) (NatStr [1]))
          rs = repeat rule_5
          ts = rewrite_steps (f_a) (zip ps rs)

red_2 :: Reduction Char Char System_1
red_2 = Red ts (zip ps rs)
    where ps = (iterate (\ns -> prefix_position 1 ns) (NatStr []))
          rs = repeat rule_1
          ts = rewrite_steps (f_omega) (zip ps rs)

red_3 :: Reduction Char Char System_1
red_3 = Red ts (zip ps rs)
    where ps = [NatStr [1], NatStr [1]]
          rs = [rule_4, rule_6]
          ts = rewrite_steps (f_h_a_f_b) (zip ps rs)

red_4 :: Reduction Char Char System_3
red_4 = Red ts (zip ps rs)
    where ps = [NatStr [], NatStr [2], NatStr [2,2]]
          rs = [rule_9, rule_9, rule_9]
          ts = rewrite_steps (f_a) (zip ps rs)

red_5 :: Reduction Char Char System_3
red_5 = Red ts (zip ps rs)
    where ps = [NatStr [1], NatStr [1]]
          rs = [rule_10, rule_11]
          ts = rewrite_steps (f_a) (zip ps rs)

red_6 :: Reduction Char Char System_1
red_6 = Red ts (zip ps rs)
    where ps = (NatStr []):(map (\p -> prefix_position 1 (prefix_position 1 p)) ps)
          rs = rule_1:rs
          ts = rewrite_steps f_omega (zip ps rs)

red_7 :: Reduction Char Char System_1
red_7 = Red ts (zip ps rs)
    where ps = (NatStr [1]):(map (\p -> prefix_position 1 (prefix_position 1 p)) ps)
          rs = rule_1:rs
          ts = rewrite_steps f_omega (zip ps rs)

cred_1 = CRed red_1 (\x -> succ x)

cred_2 = CRed red_2 (\x -> succ x)

cred_3 = CRed red_3 (\x -> 2)

cred_4 = CRed red_4 (\x -> min 3 (succ x))

cred_5 = CRed red_5 (\x -> if x == 0 then 0 else 2)

cred_6 = CRed red_6 (\x -> succ x)

cred_7 = CRed red_7 (\x -> x)

show_steps (CRed (Red _ s) _) = s

show_phi (CRed _ phi) = show_phi' 0
    where show_phi' d = (show (phi d)) ++ (show_phi' (succ d))
