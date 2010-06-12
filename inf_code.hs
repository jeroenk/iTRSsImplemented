class Signature s where
    arity :: s -> Int

class Eq v => Variables v

data (Signature s, Variables v) => Infinite_Terms s v =
    Function s [Infinite_Terms s v]
    | Variable v

constant :: (Signature s, Variables v) => s -> Infinite_Terms s v
constant c = if arity(c) == 0
             then Function c []
             else error "Input is not a constant"

class MyShow a where
    myshow :: a -> String

instance MyShow Char where
    myshow x = [x]

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (Infinite_Terms s v) where
    show (Function f []) = myshow f
    show (Function f xs)  = myshow f ++ "(" ++ (show' xs True) ++ ")"
        where show' [] _         = ""
              show' (x:xs) True  = show x ++ show' xs False
              show' (x:xs) False = "," ++ show x ++ show' xs False
    show (Variable v)   = myshow v

data Nat_Strings = Nat_String [Int]

instance Show Nat_Strings where
    show (Nat_String ns) = show ns

prefix_position :: Int -> Nat_Strings -> Nat_Strings
prefix_position n (Nat_String ns) = Nat_String (n:ns)

positions :: (Signature s, Variables v) => (Infinite_Terms s v) -> [Nat_Strings]
positions (Function _ xs)
    = Nat_String [] : concat (prefix_positions (map positions xs) 1)
    where prefix_positions [] _
              = []
          prefix_positions (x:xs) n
              = (map (prefix_position n) x):(prefix_positions xs (n + 1))
positions (Variable _)
    = [Nat_String []]

longest_prefix :: (Signature s, Variables v)
                  => (Infinite_Terms s v) -> Nat_Strings -> Nat_Strings
longest_prefix (Function _ []) _
    = Nat_String []
longest_prefix (Function _ _) (Nat_String [])
    = Nat_String []
longest_prefix (Function f xs) (Nat_String (n:ns))
    = if arity(f) < n
      then Nat_String []
      else prefix_position n (longest_prefix (subterm xs n) (Nat_String ns))
           where subterm (x:xs) 1 = x
                 subterm (x:xs) n = subterm xs (n - 1)
longest_prefix (Variable _) _
    = Nat_String []

data Substitutions s v = Substitution [(v, Infinite_Terms s v)]

instance (MyShow s, MyShow v, Signature s, Variables v)
         => Show (Substitutions s v) where
    show (Substitution xs) = "{" ++ show' xs True ++ "}"
        where show' [] _
                  = ""
              show' ((x, t):ss) True
                  = "(" ++ myshow x ++ ", " ++ show t ++ ")" ++ show' ss False
              show' ((x, t):ss) False
                  = ", (" ++ myshow x ++ ", " ++ show t ++ ")" ++ show' ss False

substitute_variable :: Variables v
                       => Substitutions s v -> v -> Infinite_Terms s v
substitute_variable (Substitution []) x
    = Variable x
substitute_variable (Substitution ((y,t):ss)) x
    = if x == y then t else substitute_variable (Substitution ss) x

substitute :: (Signature s, Variables v)
              => Substitutions s v -> Infinite_Terms s v -> Infinite_Terms s v
substitute sigma (Function f xs)
    = Function f (map (substitute sigma) xs)
substitute sigma (Variable x)
    = substitute_variable sigma x

-- Examples

type Standard_Terms         = Infinite_Terms Char Char
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
