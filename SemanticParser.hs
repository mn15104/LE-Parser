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




-- new :: Loc -> Loc
-- new n = n + 1
------------------------------------------

data Aexp = N Num | V Var| Mult Aexp Aexp | Add Aexp Aexp | Sub Aexp Aexp
      deriving (Show, Eq, Read)
data Bexp = TRUE | FALSE | Neg Bexp | And Bexp Bexp | Le Aexp Aexp | Eq Aexp Aexp
      deriving (Show, Eq, Read)
data Stm  = Skip | Comp Stm Stm | Ass Var Aexp | If Bexp Stm Stm | While Bexp Stm | Block DecV DecP Stm | Call Pname
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
type EnvP_d    = Pname -> Stm
data Config_d   = Inter_d Stm State EnvP_d | Final_d State EnvP_d

decVcontainsV :: [(Var, Aexp)] -> Var -> Bool
decV `decVcontainsV` var = (var `elem` decV')
                          where decV' = map fst decV

update'::State->(Var, Aexp)->State
update' s (var, aexp) = (\var' -> if (var == var') then a_val aexp s else ( s var' ) )

update::State->DecV->State
update s decv = foldl update' s decv

updateP_d'::EnvP_d->(Pname, Stm)->EnvP_d
updateP_d' envp (pname, stm) = (\pname' -> if (pname == pname') then stm else ( envp pname' ) )

updateP_d::EnvP_d->DecP->EnvP_d
updateP_d envp decp = foldl updateP_d' envp decp

ns_stm_d :: Config_d -> Config_d
ns_stm_d (Inter_d (Skip) s envp)          =   Final_d s envp

ns_stm_d (Inter_d (Comp s1 s2) s envp)    =   Final_d s'' envp''
                                          where
                                          Final_d s'  envp' = ns_stm_d(Inter_d s1 s envp)
                                          Final_d s'' envp'' = ns_stm_d(Inter_d s2 s' envp')

ns_stm_d (Inter_d (Ass var aexp) s envp)  =   Final_d (update s [(var, aexp)]) envp

ns_stm_d (Inter_d (If bexp s1 s2) s envp)
    | b_val bexp s  = ns_stm_d(Inter_d s1 s envp)
    | otherwise     = ns_stm_d(Inter_d s2 s envp)

ns_stm_d (Inter_d (While bexp s1) s envp)
    | not (b_val bexp s)      = Final_d s envp
    | otherwise               = Final_d s'' envp''
                                where
                                Final_d s'  envp' = ns_stm_d(Inter_d s1 s envp)
                                Final_d s''  envp'' = ns_stm_d(Inter_d (While bexp s1) s' envp')

ns_stm_d (Inter_d (Block decv decp stm) s envp)   = Final_d s_restore envp''
                                              where
                                              s'                = update s decv       -- Update state mapping for P's local variables
                                              envp'             = updateP_d envp decp -- Update procedure mapping for P's procedures
                                              Final_d s'' envp''  = ns_stm_d(Inter_d stm s' envp')            -- Execute process and return any (dynamically) updated processes and variables
                                              s_restore = (\v -> if decVcontainsV decv v then s v else s'' v ) -- Ignore local variable declarations in Block Process

ns_stm_d (Inter_d (Call pname) s envp)      =     Final_d s' envp'
                                              where
                                              Final_d s' envp'  = ns_stm_d(Inter_d (envp pname) s envp)

s_dynamic::Stm->Config_d->Config_d
s_dynamic stm (Final_d s envp) = Final_d s' envp'
          where
          Final_d s' envp' = ns_stm_d (Inter_d stm s envp)

-- ---------------------------------------------

s_test1 = s_testx(s_dynamic s1'' (Final_d def_state_d def_envp_d))
s_test2 = s_testy(s_dynamic s1'' (Final_d def_state_d def_envp_d))
s_test3 = s_testz(s_dynamic s1'' (Final_d def_state_d def_envp_d))
s_testx::Config_d -> Integer
s_testx (Inter_d stm state envp ) = state "x"
s_testx (Final_d state envp) = state "x"
s_testy::Config_d -> Integer
s_testy (Inter_d stm state envp) = state "y"
s_testy (Final_d state envp) = state "y"
s_testz::Config_d -> Integer
s_testz (Inter_d stm state envp) = state "z"
s_testz (Final_d state envp) = state "z"


s1 :: Stm
s1 = Block [("X", N 5)] [("foo", Skip)] Skip

s1' :: Stm
s1' = Block [("x",N 0)] [("p",Ass "x" (Mult (V "x") (N 2))),("q",Call "p")] (Block [("x",N 5)] [("p",Ass "x" (Add (V "x") (N 1)))] (Call "q"))

s1'' :: Stm
s1'' = Block [] [("fac",Block [("z",V "x")] [] (If (Eq (V "x") (N 1)) Skip (Comp (Ass "x" (Sub (V "x") (N 1))) (Comp (Call "fac") (Ass "y" (Mult (V "z") (V "y")))  ))))] (Comp (Ass "y" (N 1)) (Call "fac"))

s1''' :: Stm
s1''' = Comp (Ass "y" (N 1)) (While (Neg (Eq (V "x") (N 1))) (Comp (Ass "y" (Mult (V "y") (V "x"))) (Ass "x" (Sub (V "x") (N 1)))))

def_state_d :: State
def_state_d "x" = 5
def_state_d _ = 0

def_envp_d :: EnvP_d
def_envp_d _ = Skip
