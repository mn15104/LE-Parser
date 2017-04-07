{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
import Prelude hiding (Num)
import System.IO
import Control.Monad



n_val::Num -> Z
n_val n = n

a_val_static::Aexp->Config_st->Z
a_val_static (N n) config        = n_val(n)
a_val_static (V v) (Inter_st stm s envv envp loc store decv)
  | (envv v == -1)   = s v            -- if global variable, evaluate using state
  | otherwise        = store (envv v) -- if local variable, evaluate using store
a_val_static (Mult a1 a2) config = a_val_static(a1)config * a_val_static(a2)config
a_val_static (Add a1 a2)  config = a_val_static(a1)config + a_val_static(a2)config
a_val_static (Sub a1 a2)  config = a_val_static(a1)config - a_val_static(a2)config

b_val_static::Bexp->Config_st->T
b_val_static (TRUE)  config   = True
b_val_static (FALSE) config   = False
b_val_static (Neg b) config
  | (b_val_static(b)config)     = False
  | otherwise       = True
b_val_static (And b1 b2) config
  | b_val_static(b1)config && b_val_static(b2)config = True
  | otherwise = False
b_val_static (Eq a1 a2) config
  | a_val_static(a1) config == a_val_static(a2) config = True
  | a_val_static(a1) config /= a_val_static(a2) config = False
b_val_static (Le a1 a2) config
  | a_val_static(a1) config <= a_val_static(a2) config  = True
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
type Loc = Num
type EnvV = Var  -> Loc   -- Mapping #1: Associates a location with a variable
type Store = Loc -> Z     -- Mapping #2: Associates a variable value with a location
type DecV  = [(Var,Aexp)]
type DecP  = [(Pname,Stm)]
type State = Var -> Z

data EnvP_st = ENVP_st (Pname -> (Stm, EnvV, EnvP_st, DecV))
data Config_st   = Inter_st Stm State EnvV EnvP_st Loc Store DecV| Final_st State EnvV EnvP_st Loc Store DecV


new :: Loc -> Loc
new loc = loc + 1

updateV_st'::Config_st->(Var, Aexp)->Config_st
updateV_st' (Inter_st stm s envv envp loc store decv) (var, aexp) = Final_st s envv' envp nextloc newstore decv
                            where nextloc = new loc;                    -- inside current procedure A
                                  envv' = (\var' -> if (var == var')    -- update current environment's variable to location mapping -- difference between decv and assign, i.e. updateV_st and update, only decv is static inside a procedure
                                                    then loc            -- variables inside a begin decv s end block are static to it
                                                    else ( envv var' ))
                                  newstore = (\loc' -> if (loc == loc') -- update global store to hold the aexp using the original envv - e.g. x := x + 1, we have to evaluate the RHS x with the original envv
                                                            then a_val_static aexp (Inter_st stm s envv envp loc store decv)
                                                            else store loc')

updateV_st::Config_st->DecV->Config_st
updateV_st config decv  = foldl updateV_st' config decv

updateP_st'::Config_st->(Pname, Stm)->Config_st
updateP_st' (Inter_st statement s envv envp loc store decv) (pname, stm) = Final_st s envv envp' loc store decv
                            where envp' = ENVP_st (\pname' ->  if (pname == pname') then (stm, envv, envp', decv) else ( old_envp pname') )
                                  ENVP_st old_envp = envp
updateP_st' (Final_st s envv envp loc store decv) (pname, stm) = Final_st s envv envp' loc store decv
                            where envp' = ENVP_st (\pname' ->  if (pname == pname') then (stm, envv, envp', decv) else ( old_envp pname') )
                                  ENVP_st old_envp = envp

updateP_st::Config_st->DecP->Config_st
updateP_st config decp = foldl updateP_st' config decp

updateS_st::Config_st->Z->Var->Config_st
updateS_st (Inter_st stm s envv envp loc store decv) z v =  Final_st s' envv envp loc store decv
                                                      where s' = (\v' -> if (v == v') then z else ( s v' ) )

decVcontainsV :: [(Var, Aexp)] -> Var -> Bool
decV `decVcontainsV` var = (var `elem` decV')
                          where decV' = map fst decV

ns_stm_st :: Config_st -> Config_st
ns_stm_st (Inter_st (Skip) s envv envp loc store decv)           =   Final_st s envv envp loc store decv

ns_stm_st (Inter_st (Comp s1 s2) s envv envp loc store decv)     =   Final_st s'' envv'' envp'' loc'' store'' decv
                                              where
                                              Final_st s'  envv' envp' loc' store' decv'    = ns_stm_st(Inter_st s1 s envv envp loc store decv)
                                              Final_st s'' envv'' envp'' loc'' store'' decv'' = ns_stm_st(Inter_st s2 s' envv' envp' loc' store' decv')

ns_stm_st (Inter_st (Ass var aexp) s envv envp loc store decv)
  | decVcontainsV decv var  = updateV_st (Inter_st (Ass var aexp) s envv envp loc store decv) ([(var, aexp)])             -- update local variable
  | otherwise               = updateS_st (Inter_st (Ass var aexp) s envv envp loc store decv)
                                        (a_val_static aexp (Inter_st (Ass var aexp) s envv envp loc store decv)) var --update global variable


ns_stm_st (Inter_st (If bexp s1 s2) s envv envp loc store decv)
    | b_val_static bexp (Inter_st (If bexp s1 s2) s envv envp loc store decv)   = ns_stm_st(Inter_st s1 s envv envp loc store decv)
    | otherwise                                                       = ns_stm_st(Inter_st s2 s envv envp loc store decv)

ns_stm_st (Inter_st (While bexp s1) s envv envp loc store decv)
    | not (b_val_static bexp (Inter_st (While bexp s1) s envv envp loc store decv))      = Final_st s envv envp loc store decv
    | otherwise               = Final_st s'' envv'' envp'' loc'' store'' decv
                                where
                                Final_st s' envv' envp' loc' store' decv'      = ns_stm_st(Inter_st s1 s envv envp loc store decv)
                                Final_st s'' envv'' envp'' loc'' store'' decv''= ns_stm_st(Inter_st (While bexp s1) s' envv' envp' loc' store' decv')
-- State holds global variables
ns_stm_st (Inter_st (Block decv decp stm) s envv envp loc store olddecv)   = Final_st s'' envv envp'' loc'' store'' olddecv
                                                        where Final_st s'' env'' envp'' loc'' store'' decv'' = ns_stm_st(Inter_st stm s' envv' envp' loc' store' decv')
                                                              Final_st s' envv' envp' loc' store' decv' = updateP_st config' decp        -- update environment procedure
                                                              config' = updateV_st (Inter_st (Block decv decp stm) s envv envp loc store decv) decv -- update environment variables using decv
                                                            --  envv''' = (\v -> if((s v /= s'' v) && (decVcontainsV olddecv v)) then updatedloc else envv v)
                                                            --  updatedloc = if(envv''' == envv)  then new loc''  else loc''
                                                            -- what if we *only update envv* instead of state, and when passing it back, let original_envv = (\v -> if (not(decVcontainsV branched_decV v)) then oldenvv v else newenvv v)
                                                                                                                                                                    -- if branched function had v as local variable, then ignore it and restore and use the original envv for v
                                                                                                                                                                    -- if branched function did not have v as local variable, then it possibly globally updated v, so use the updated envv



ns_stm_st (Inter_st (Call pname) s envv (ENVP_st envp) loc store decv)    =    Final_st s'' envv envp'' loc'' store'' decv
                                                        where (stm', envv', envp', decv') = envp pname                      -- Get & use local environment
                                                              Final_st sr envvr recursive_envp_update locr storer decvr = updateP_st' (Final_st s envv' envp' loc store decv') (pname, stm') -- Opdate P's procedure environment to include itself
                                                              Final_st s'' envv'' envp'' loc'' store'' decv'' = ns_stm_st(Inter_st (stm') s  envv' recursive_envp_update loc store decv')  -- Execute called statement

s_static::Stm->Config_st->Config_st
s_static stm (Final_st s envv envp loc store decv) = ns_stm_st (Inter_st stm s envv envp loc store decv)


----------------------------------------------------------------------------------------
----------------------------- * STATIC TEST FUNCTIONS * --------------------------------

s_test1_st = s_testy_st(s_static exercise_2_37 (default_config_st))

s_get_store_st::Config_st->Integer->Integer
s_get_store_st (Inter_st stm state envv envp loc store decv) n  = store(n)
s_get_store_st (Final_st state envv envp loc store decv) n = store(n)

s_testx_st::Config_st -> Integer
s_testx_st (Inter_st stm state envv envp loc store decv) = store (envv "x")
s_testx_st (Final_st state envv envp loc store decv) = store (envv "x")
s_testy_st::Config_st -> Integer
s_testy_st (Inter_st stm state envv envp loc store decv) = state "x"
s_testy_st (Final_st state envv envp loc store decv) = state "x"
s_testz_st::Config_st -> Integer
s_testz_st (Inter_st stm state envv envp loc store decv) = store (envv "z")
s_testz_st (Final_st state envv envp loc store decv) = store (envv "z")

----------------------------------------------------------------------------------
----------------------------- * TEST STATEMENTS * --------------------------------

scope_test :: Stm
scope_test = Block [("x",N 0)] [("p",Ass "x" (Mult (V "x") (N 2))),("q",Call "p")] (Block [("x",N 5)] [("p",Ass "x" (Add (V "x") (N 1)))] (Call "q"))

fac_recurse :: Stm
fac_recurse = Block [] [("fac",Block [("z",V "x")] [] (If (Eq (V "x") (N 1)) Skip (Comp (Ass "x" (Sub (V "x") (N 1))) (Comp (Call "fac") (Ass "y" (Mult (V "z") (V "y"))) ))))] (Comp (Ass "y" (N 1)) (Call "fac"))

fac_while:: Stm
fac_while = Comp (Ass "y" (N 1)) (While (Neg (Eq (V "x") (N 1))) (Comp (Ass "y" (Mult (V "y") (V "x"))) (Ass "x" (Sub (V "x") (N 1)))))

my_test :: Stm
my_test = Comp (Ass "z" (V "x")) (If (Eq (V "x") (N 1)) Skip (Comp (Ass "x" (Sub (V "x") (N 1))) (Ass "y" (Sub (V "z") (V "y")))))

exercise_2_37 :: Stm
exercise_2_37 = Block [("y",N 1)] [] (Comp (Ass "x" (N 1)) (Comp (Block [("x",N 2)] [] (Ass "y" (Add (V "x") (N 1)))) (Ass "x" (Add (V "y") (V "x")))))

----------------------------------------------------------------------------------
------------------------- * STATIC DEFAULT CONFIGURATION * -----------------------

default_config_st = Final_st def_state_st def_envv_st def_envp_st def_loc_st def_store_st def_decv_st

def_state_st :: State
def_state_st "x" = 5
def_state_st _ = 0

def_envv_st :: EnvV
def_envv_st _ = -1

def_envp_st :: EnvP_st
def_envp_st = ENVP_st (\pname -> (Skip, def_envv_st, def_envp_st, def_decv_st))

def_loc_st :: Loc
def_loc_st = 0

def_store_st :: Store
def_store_st _ = -1

def_decv_st :: DecV
def_decv_st = []
------------------------------------------------------------------------------
