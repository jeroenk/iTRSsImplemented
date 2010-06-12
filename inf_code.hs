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
    Function_Symbol s
    | Variable_Symbol v

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (Symbols s v) where
    show (Function_Symbol f) = myshow f
    show (Variable_Symbol x) = myshow x

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

data Nat_Strings = Nat_String [Int]

instance Show Nat_Strings where
    show (Nat_String ns) = show ns

prefix_position :: Int -> Nat_Strings -> Nat_Strings
prefix_position n (Nat_String ns) = Nat_String (n:ns)

positions :: (Signature s, Variables v)
             => Terms s v -> [Nat_Strings]
positions (Function _ xs)
    = Nat_String [] : concat (prefix_positions (map positions xs) 1)
    where prefix_positions [] _
              = []
          prefix_positions (x:xs) n
              = (map (prefix_position n) x):(prefix_positions xs (n + 1))
positions (Variable _)
    = [Nat_String []]

get_symbol :: (Signature s, Variables v)
              => Terms s v -> Nat_Strings -> Symbols s v
get_symbol (Function f _) (Nat_String [])
    = Function_Symbol f
get_symbol (Function _ xs) (Nat_String (n:ns))
    = get_symbol (subterm' xs n) (Nat_String ns)
    where subterm' (x:xs) 1 = x
          subterm' (x:xs) n = subterm' xs (n - 1)
          subterm' _ _      = error "Undefined subterm"
get_symbol (Variable x) (Nat_String [])
    = Variable_Symbol x
get_symbol (Variable x) _
    = error "Undefined subterm"

-- Substitutions

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

-- Excursion: Rational Terms
--
-- Remark that a finite system of regular equations is a substitution where
-- the terms are not allowed to be variables

type Regular_Systems s v = Substitutions s v

rational_term :: (Signature s, Variables v)
                 => Regular_Systems s v -> v -> Terms s v
rational_term sigma x = rational_term' sigma (Variable x)
    where rational_term' sigma (Variable x)
              = if in_substitution sigma x
                then rational_term' sigma (substitute_variable sigma x)
                else (Variable x)
          rational_term' sigma (Function f xs)
              = Function f (map (rational_term' sigma) xs)

-- Subterms

subterm :: (Signature s, Variables v)
           => Terms s v -> Nat_Strings -> Terms s v
subterm s (Nat_String [])
    = s
subterm (Function _ xs) (Nat_String (n:ns))
    = subterm (subterm' xs n) (Nat_String ns)
    where subterm' (x:xs) 1 = x
          subterm' (x:xs) n = subterm' xs (n - 1)
          subterm' _ _      = error "Undefined subterm"
subterm (Variable _) _
    = error "Undefined subterm"

-- Examples

type Standard_Terms         = Terms Char Char
type Standard_Substitutions = Substitutions Char Char

instance Signature Char where
    arity 'a' = 0
    arity 'b' = 0
    arity 'f' = 1
    arity 'g' = 1
    arity 'h' = 2
    arity _   = error "Character not in signature"

instance Variables Char

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
sigma_2 = Substitution [('x', Function 'f' [Variable 'x'])]

f_omega' :: Standard_Terms
f_omega' = rational_term sigma_2 'x'
