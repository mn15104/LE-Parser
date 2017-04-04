import Prelude hiding (Num)
import System.IO
import Control.Monad


--s_static :: Stm -> State -> State

-- MAKE EVERYTHING NATURAL.
-- https://www.cs.bris.ac.uk/Teaching/Resources/COMS22201/semanticsLab6.pdf
-- https://www.cs.bris.ac.uk/Teaching/Resources/COMS22201/semanticsCwk2.pdf
-- https://www.cs.bris.ac.uk/Teaching/Resources/COMS22201/semanticsLec6.pdf
-- https://www.cs.bris.ac.uk/Teaching/Resources/COMS22201/nielson.pdf

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

update::State->Z->Var->State
update s i v = (\v' -> if (v == v') then i else ( s v' ) )

cond :: ( a->T, a->a, a->a ) ->( a->a )
cond (b, s1, s2) x  = if (b x) then (s1 x) else (s2 x)

fix :: ((State->State)->(State->State))->(State->State)
fix ff = ff (fix ff)



------------------------------------------

data Aexp = N Num | V Var| Mult Aexp Aexp | Add Aexp Aexp | Sub Aexp Aexp
      deriving (Show, Eq, Read)
data Bexp = TRUE | FALSE | Neg Bexp | And Bexp Bexp | Le Aexp Aexp | Eq Aexp Aexp
      deriving (Show, Eq, Read)

type Num   = Integer
type Var   = String
type Pname = String
type Z = Integer
type T = Bool
-- type Loc = Num
type DecV  = [(Var,Aexp)]
type DecP  = [(Pname,Stm)]
type State = Var -> Z
type EnvP = Pname -> Stm
type EnvV = Var   -> Z

data Config = Inter Stm State | Final State

data Stm  = Skip | Comp Stm Stm | Ass Var Aexp | If Bexp Stm Stm | While Bexp Stm | Block DecV DecP Stm | Call Pname
      deriving (Show, Eq, Read)

-- new :: Loc -> Loc
-- new n = n + 1

updateV::State->(Var, Aexp)->State
updateV s (var, aexp) = (\var' -> if (var == var') then a_val aexp s else ( s var' ) )

updateV'::State->DecV->State
updateV' s decv = foldl updateV s decv

updateP::EnvP->(Pname, Stm)->EnvP
updateP s (pname, stm) = (\pname' -> if (pname == pname') then stm else ( s pname' ) )

updateP'::EnvP->DecP->EnvP
updateP' s decp = foldl updateP s decp

--updateP :: (DecP, EnvV, EnvP) -> EnvP

ns_stm :: Config -> Config
ns_stm (Inter (Skip) s)       = Final s
ns_stm (Inter (Comp s1 s2) s) = Final s''
                                where
                                Final s'  = ns_stm(Inter s1 s)
                                Final s'' = ns_stm(Inter s2 s')
ns_stm (Inter (Ass var aexp) s) = Final (update s z var)
                                  where
                                  z = a_val aexp s
ns_stm (Inter (If bexp s1 s2) s)
    | b_val bexp s  = ns_stm(Inter s1 s)
    | otherwise     = ns_stm(Inter s2 s)
ns_stm (Inter (While bexp s1) s)
    | not (b_val bexp s)     = Final s
    | otherwise     = ns_stm(Inter (While bexp s1) s')
                    where
                    Final s' = ns_stm(Inter s1 s)

ns_stm (Inter (Block decv decp stm) s)  = Final s'''
                                        where
                                        s' = updateV' s decv
                                        s'' = updateP' s' decp -- ??? How to make environmental variables globally accessible?
                                        s''' = ns_stm(Inter stm s'')


s_ns::Stm->State->State
s_ns s1 s = s'
          where
          Final s' = ns_stm (Inter s1 s)

s_ds::Stm->State->State
s_ds ( Ass v a ) s    = update s (a_val a s) v
s_ds ( Skip ) s       = s
s_ds ( Comp s1 s2 ) s = s_ds s2 (s_ds s1 s)
s_ds ( If b s1 s2 ) s = undefined
s_ds ( While b s1 ) s = undefined
