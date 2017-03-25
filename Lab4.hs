import Prelude hiding (Num)
import qualified Prelude (Num)

type Num = Integer
type Var = String
type Z = Integer
type T = Bool
type State = Var -> Z

data Aexp = N Num | V Var | Mult Aexp Aexp | Add Aexp Aexp | Sub Aexp Aexp
    deriving (Show, Eq, Read)

data Bexp = TRUE | FALSE | Neg Bexp | And Bexp Bexp | Eq Aexp Aexp | Le Aexp Aexp
    deriving (Show, Eq, Read)


n_val::Num -> Z
n_val n = n

a_val::Aexp->State->Z
a_val (N n) s       = n_val(n)
a_val (V v) s       = s v
a_val (Mult a1 a2) s = a_val(a1)s * a_val(a2)s
a_val (Add a1 a2)  s = a_val(a1)s + a_val(a2)s
a_val (Sub a1 a2)  s = a_val(a1)s - a_val(a2)s

b_val::Bexp->State->T
b_val (TRUE)  s     = True
b_val (FALSE) s     = False
b_val (Neg b) s
  | (b_val(b)s)     = False
  | otherwise       = True
b_val (And b1 b2) s
  | b_val(b1)s && b_val(b2)s  = True
  | otherwise = False
b_val (Eq a1 a2) s
  | a_val(a1)s == a_val(a2)s  = True
  | a_val(a1)s /= a_val(a2)s  = False
b_val (Le a1 a2) s
  | a_val(a1)s <= a_val(a2)s  = True
  | otherwise = False

s::State
s "x" = 1
s "y" = 2
s "z" = 3
s _ = 0

a::Aexp
a = Mult (Add(V "x")(V "y")) (Sub(V "z")(N 1))

b::Bexp
b = (Neg TRUE)

main = putStrLn $ "hi"
