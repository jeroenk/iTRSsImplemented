class Signature a where
  arity :: a -> Int

data Signature a => Infinite_Terms a b =
  Function a [Infinite_Terms a b]
  | Variable b

class MyShow a where
  myshow :: a -> String

instance MyShow Char where
  myshow x = [x]

instance (MyShow a, MyShow b, Signature a) => Show (Infinite_Terms a b) where
  show (Function x []) = myshow x
  show (Function x y)  = myshow x ++ "(" ++ (show' y True) ++ ")"
    where show' [] _         = ""
          show' (x:xs) True  = show x ++ show' xs False
          show' (x:xs) False = "," ++ show x ++ show' xs False
  show (Variable x)   = myshow x

data Nat_Strings = Nat_String [Int]

instance Show Nat_Strings where
  show (Nat_String x) = show x

prefix_positions :: [[Nat_Strings]] -> [Nat_Strings]
prefix_positions xs = concat (prefix_positions' xs 1)
  where prefix_position n (Nat_String xs) = Nat_String (n:xs)
        prefix_positions' [] _
          = []
        prefix_positions' (x:xs) n
          = (map (prefix_position n) x):(prefix_positions' xs (n + 1))

positions :: Signature a => (Infinite_Terms a b) -> [Nat_Strings]
positions (Function x y) = Nat_String [] : prefix_positions (map positions y)
positions (Variable _)   = [Nat_String []]

-- Example signature and example terms

type Standard_Terms = Infinite_Terms Char Char

instance Signature Char where
    arity 'a' = 0
    arity 'b' = 0
    arity 'f' = 1
    arity 'g' = 1
    arity 'h' = 2
    arity _   = error "Character not in signature"

f_omega :: Standard_Terms
f_omega = Function 'f' [f_omega]

h_omega :: Standard_Terms
h_omega = Function 'h' [h_omega, h_omega]

h_a_f_b :: Standard_Terms
h_a_f_b = Function 'h' [Function 'a' [], Function 'f' [Function 'b' []]]
