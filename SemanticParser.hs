{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
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


cond :: ( a->T, a->a, a->a ) ->( a->a )
cond (b, s1, s2) x  = if (b x) then (s1 x) else (s2 x)

fix :: ((State->State)->(State->State))->(State->State)
fix ff = ff (fix ff)





-- new :: Loc -> Loc
-- new n = n + 1
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
type EnvP    = Pname -> Stm
type EnvP_m = Pname -> (Stm, EnvP)
type EnvV = Var   -> Z
data Config   = Inter Stm State EnvV EnvP | Final State EnvV EnvP
data Config_m = Inter_m Stm State EnvV EnvP_m | Final_m State EnvV EnvP_m
data Stm  = Skip | Comp Stm Stm | Ass Var Aexp | If Bexp Stm Stm | While Bexp Stm | Block DecV DecP Stm | Call Pname
      deriving (Show, Eq, Read)

--updateP :: (DecP, EnvV, EnvP) -> EnvP

update::State->Z->Var->State
update s i v = (\v' -> if (v == v') then i else ( s v' ) )

updateV'::State->(Var, Aexp)->State
updateV' s (var, aexp) = (\var' -> if (var == var') then a_val aexp s else ( s var' ) )

updateV::State->DecV->State
updateV s decv = foldl updateV' s decv

updateP'::EnvP->(Pname, Stm)->EnvP
updateP' envp (pname, stm) = (\pname' -> if (pname == pname') then stm else ( envp pname' ) )

updateP::EnvP->DecP->EnvP
updateP envp decp = foldl updateP' envp decp

ns_stm :: Config -> Config
ns_stm (Inter (Skip) s envv envp)          =   Final s envv envp

ns_stm (Inter (Comp s1 s2) s envv envp)    =   Final s'' envv'' envp''
                                          where
                                          Final s'  envv' envp' = ns_stm(Inter s1 s envv envp)
                                          Final s'' envv'' envp'' = ns_stm(Inter s2 s' envv' envp')

ns_stm (Inter (Ass var aexp) s envv envp)  =   Final (updateV s [(var, aexp)]) envv envp
                                        --  where
                                        --  z = a_val aexp s

ns_stm (Inter (If bexp s1 s2) s envv envp)
    | b_val bexp s  = ns_stm(Inter s1 s envv envp)
    | otherwise     = ns_stm(Inter s2 s envv envp)

ns_stm (Inter (While bexp s1) s envv envp)
    | not (b_val bexp s)      = Final s envv envp
    | otherwise               = Final s'' envv'' envp''
                                where
                                Final s' envv' envp' = ns_stm(Inter s1 s envv envp)
                                Final s'' envv'' envp'' = ns_stm(Inter s1 s' envv' envp')

ns_stm (Inter (Block decv decp stm) s envv envp)   = Final s'' envv'' envp''
                                              where
                                              s'                = updateV s decv
                                              envp'             = updateP envp decp
                                              Final s'' envv'' envp''  = ns_stm(Inter stm s' envv envp')

ns_stm (Inter (Call pname) s envv envp)      =     Final s' envv' envp'
                                              where
                                              Final s' envv' envp'  = ns_stm(Inter (envp pname) s envv envp)

s_mixed::Stm->Config->Config
s_mixed   stm (Final s envv envp) = Final s' envv' envp'
          where
          Final s' envv' envp' = ns_stm (Inter stm s envv envp)

s_dynamic::Stm->Config->Config
s_dynamic stm (Final s envv envp) = Final s' envv' envp'
          where
          Final s' envv' envp' = ns_stm (Inter stm s envv envp)

---------------------------------------------

s_test1 = s_testx(s_dynamic s1'' (Final s2 s3 s4))
s_test2 = s_testy(s_dynamic s1'' (Final s2 s3 s4))
s_test3 = s_testz(s_dynamic s1'' (Final s2 s3 s4))
s_testx::Config -> Integer
s_testx (Inter stm state envp envv) = state "x"
s_testx (Final state envv envp) = state "x"
s_testy::Config -> Integer
s_testy (Inter stm state envv envp) = state "y"
s_testy (Final state envv envp) = state "y"
s_testz::Config -> Integer
s_testz (Inter stm state envv envp) = state "z"
s_testz (Final state envv envp) = state "z"


s1 :: Stm
s1 = Block [("X", N 5)] [("foo", Skip)] Skip

s1' :: Stm
s1' = Block [("x",N 0)] [("p",Ass "x" (Mult (V "x") (N 2))),("q",Call "p")] (Block [("x",N 5)] [("p",Ass "x" (Add (V "x") (N 1)))] (Call "q"))

s1'' :: Stm
s1'' = Block [] [("fac",Block [("z",V "x")] [] (If (Eq (V "x") (N 1)) Skip (Comp (Ass "x" (Sub (V "x") (N 1))) (Comp (Ass "y" (Mult (V "z") (V "y"))) (Call "fac") ))))] (Comp (Ass "y" (N 1)) (Call "fac"))

s2 :: State
s2 "x" = 5
s2 _ = 0

s3 :: EnvV
s3 _ = 0

s4 :: EnvP
s4 _ = Skip


------




s_ds::Stm->State->State
s_ds ( Ass v a ) s    = update s (a_val a s) v
s_ds ( Skip ) s       = s
s_ds ( Comp s1 s2 ) s = s_ds s2 (s_ds s1 s)
s_ds ( If b s1 s2 ) s = undefined
s_ds ( While b s1 ) s = undefined
