{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
import Prelude hiding (Num)
import System.IO
import Control.Monad

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

----------------------------------------------------------------------------------
----------------------------- * DYNAMIC * ----------------------------------------

s_dynamic::Stm->State->State
s_dynamic stm state = final_state
          where
          Final_d final_state final_envp = ns_stm_d (Inter_d stm state default_envp_d)

var_state_d::Var -> Stm -> Integer      -- Dynamic variable state tester; using Default Config
var_state_d v stm = final_state v
          where final_state = s_dynamic stm default_state_d


----------------------------------------------------------------------------------
----------------------------- * TEST STATEMENTS * --------------------------------

scope_test :: Stm
scope_test = Block [("x",N 0)] [("p",Ass "x" (Mult (V "x") (N 2))),("q",Call "p")] (Block [("x",N 5)] [("p",Ass "x" (Add (V "x") (N 1)))] (Comp (Call "q") (Ass "y" (V "x"))))

fac_recurse :: Stm
fac_recurse = Block [] [("fac",Block [("z",V "x")] [] (If (Eq (V "x") (N 1)) Skip (Comp (Ass "x" (Sub (V "x") (N 1))) (Comp(Call "fac")(Ass "y" (Mult (V "z") (V "y")))   ))))] (Comp (Ass "y" (N 1)) (Call "fac"))

fac_while:: Stm
fac_while = Comp (Ass "y" (N 1)) (While (Neg (Eq (V "x") (N 1))) (Comp (Ass "y" (Mult (V "y") (V "x"))) (Ass "x" (Sub (V "x") (N 1)))))

exercise_2_37 :: Stm
exercise_2_37 = Block [("y",N 1)] [] (Comp (Ass "x" (N 1)) (Comp (Block [("x",N 2)] [] (Ass "y" (Add (V "x") (N 1)))) (Ass "x" (Add (V "y") (V "x")))))

----------------------------------------------------------------------------------
------------------------- * DYNAMIC DEFAULT CONFIGURATION * -----------------------

default_state_d :: State
default_state_d "x" = 5
default_state_d _ = 0

default_envp_d :: EnvP_d
default_envp_d _ = Skip
