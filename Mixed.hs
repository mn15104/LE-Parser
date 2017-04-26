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
type DecV  = [(Var,Aexp)]
type DecP  = [(Pname,Stm)]
type State = Var -> Z
data EnvP_m = ENVP (Pname -> (Stm, EnvP_m, DecP))
data Config_m   = Inter_m Stm State EnvP_m | Final_m State EnvP_m

decVcontainsV :: [(Var, Aexp)] -> Var -> Bool
decV `decVcontainsV` var = (var `elem` decV')
                          where decV' = map fst decV

update'::State->(Var, Aexp)->State
update' s (var, aexp) = (\var' -> if (var == var') then a_val aexp s else ( s var' ) )

update::State->DecV->State
update s decv = foldl update' s decv

updateP_m'::EnvP_m->(Pname, Stm, DecP)->EnvP_m
updateP_m' (ENVP envp_m) (pname, stm, decp) = ENVP (\pname' -> if (pname == pname') then (stm, ENVP envp_m, decp) else ( envp_m pname') )

updateP_m::EnvP_m->DecP->EnvP_m
updateP_m envp_m decp = foldl updateP_m' envp_m decp'
                        where decp' = append' decp

append'::[(Pname, Stm)]->[(Pname, Stm, DecP)]
append' decp = map (\(pname, stm)->(pname, stm, decp)) decp

ns_stm_m :: Config_m -> Config_m
ns_stm_m (Inter_m (Skip) s  envp_m)          =   Final_m s  envp_m

ns_stm_m (Inter_m (Comp s1 s2) s  envp_m)    =   Final_m s''  envp_m''
                                          where
                                          Final_m s'  envp_m' = ns_stm_m(Inter_m s1 s envp_m)
                                          Final_m s'' envp_m'' = ns_stm_m(Inter_m s2 s' envp_m')

ns_stm_m (Inter_m (Ass var aexp) s envp_m)  =   Final_m (update s [(var, aexp)])  envp_m


ns_stm_m (Inter_m (If bexp s1 s2) s envp_m)
    | b_val bexp s  = ns_stm_m(Inter_m s1 s envp_m)
    | otherwise     = ns_stm_m(Inter_m s2 s envp_m)

ns_stm_m (Inter_m (While bexp s1) s envp_m)
    | not (b_val bexp s)      = Final_m s envp_m
    | otherwise               = Final_m s'' envp_m''
                                where
                                Final_m s' envp_m' = ns_stm_m(Inter_m s1 s envp_m)
                                Final_m s'' envp_m'' = ns_stm_m(Inter_m (While bexp s1) s' envp_m')

ns_stm_m (Inter_m (Block decv decp stm) s envp_m)   = Final_m s_restore envp_m''
                                              where
                                              s'                     = update s decv          -- Update state mapping for P's local variables
                                              envp_m'                = updateP_m envp_m decp  -- Update procedure mapping for P's procedures
                                              Final_m s'' envp_m''   = ns_stm_m(Inter_m stm s'  envp_m')
                                              s_restore              = (\v -> if decVcontainsV decv v then s v else s'' v )

ns_stm_m (Inter_m (Call pname) s (ENVP envp_m) )    =    ns_stm_m(Inter_m (p_stm) s  (envp_recurse) )
                                                    where
                                                    (p_stm, p_environment, p_dec)             = envp_m pname                        -- Get & use statically defined body of P
                                                    envp_recurse      = updateP_m (p_environment) p_dec -- When calling P, update its environment so it recognises itself

----------------------------------------------------------------------------------
------------------------------- * MIXED * ----------------------------------------

s_mixed::Stm->State->State
s_mixed stm state = final_state
        where
        Final_m final_state final_envp = ns_stm_m (Inter_m stm state default_envp_m)

var_state_m::Var -> Stm -> Integer      -- Dynamic variable state tester; using Default Config
var_state_m v stm = final_state v
          where final_state = s_mixed stm default_state_m

----------------------------------------------------------------------------------
----------------------------- * TEST STATEMENTS * --------------------------------

jamie_AST = Block [("x",N 5)] [("a",If (Neg (Le (V "x") (N 3))) (Comp (Ass "y" (Add (V "y") (N 1))) (Comp (Ass "x" (Sub (V "x") (N 1))) (Call "b"))) Skip),("b",Comp (Ass "y" (Add (V "y") (N 100))) (Call "a"))] (Comp (Block [("x",N 6)] [("a",Ass "x" (N 50))] (Comp (Ass "y" (N 0)) (Comp (Call "b") (Ass "xinner" (V "x"))))) (Ass "xouter" (V "x")))


scope_test :: Stm
scope_test = Block [("x",N 0)] [("p",Ass "x" (Mult (V "x") (N 2))),("q",Call "p")] (Block [("x",N 5)] [("p",Ass "x" (Add (V "x") (N 1)))] (Comp (Call "q") (Ass "y" (V "x"))))

fac_recurse :: Stm
fac_recurse = Block [] [("fac",Block [("z",V "x")] [] (If (Eq (V "x") (N 1)) Skip (Comp (Ass "x" (Sub (V "x") (N 1))) (Comp(Call "fac")(Ass "y" (Mult (V "z") (V "y")))   ))))] (Comp (Ass "y" (N 1)) (Call "fac"))

fac_while:: Stm
fac_while = Comp (Ass "y" (N 1)) (While (Neg (Eq (V "x") (N 1))) (Comp (Ass "y" (Mult (V "y") (V "x"))) (Ass "x" (Sub (V "x") (N 1)))))

exercise_2_37 :: Stm
exercise_2_37 = Block [("y",N 1)] [] (Comp (Ass "x" (N 1)) (Comp (Block [("x",N 2)] [] (Ass "y" (Add (V "x") (N 1)))) (Ass "x" (Add (V "y") (V "x")))))

----------------------------------------------------------------------------------
------------------------- * MIXED DEFAULT CONFIGURATION * -----------------------

default_state_m :: State
default_state_m "x" = 5
default_state_m _ = -1

default_envp_m :: EnvP_m
default_envp_m = ENVP (\pname -> (Skip, default_envp_m, []))
