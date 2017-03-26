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

data Stm = Ass Var Aexp | Skip | Comp Stm Stm | If Bexp Stm Stm | While Bexp Stm
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


update::State->Z->Var->State
update s i v = (\v' -> if (v == v') then i else ( s v' ) )

cond :: ( a->T, a->a, a->a ) ->( a->a )
cond (b, s1, s2) x  = if (b x) then (s1 x) else (s2 x)

fix :: ((State->State)->(State->State))->(State->State)
fix ff = ff (fix ff)

s_ds::Stm->State->State
s_ds ( Ass v a ) s    = update s (a_val a s) v
s_ds ( Skip ) s       = s
s_ds ( Comp s1 s2 ) s = s_ds s2 (s_ds s1 s)
s_ds ( If b s1 s2 ) s = undefined
s_ds ( While b s1 ) s = undefined


--ss Var Aexp | Skip | Comp Stm Stm |
--               If Bexp Stm Stm | While Bexp Stm


main = putStrLn $ "hi"
