{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
import Prelude hiding (Num)
import System.IO
import Control.Monad



n_val::Num -> Z
n_val n = n

a_val_static::Aexp->Config_st->Z
a_val_static (N n) config        = n_val(n)
a_val_static (V v) (Inter_st stm envv envp loc store) = store (envv v)          -- if global variable, evaluate using state
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

data EnvP_st = ENVP_st (Pname -> (Stm, EnvV, EnvP_st))
data Config_st   = Inter_st Stm EnvV EnvP_st Loc Store | Final_st EnvV EnvP_st Loc Store


new :: Loc -> Loc
new loc = loc + 1

updateV_st'::Config_st->(Var, Aexp)->Config_st
updateV_st' (Inter_st stm envv envp loc store) (var, aexp) = Final_st envv' envp nextloc newstore
                            where nextloc = new loc;                    -- inside current procedure A
                                  envv' = (\var' -> if (var == var')    -- update current environment's variable to location mapping -- difference between decv and assign, i.e. updateV_st and update, only decv is static inside a procedure
                                                    then loc            -- variables inside a begin decv s end block are static to it
                                                    else ( envv var' ))
                                  newstore = (\loc' -> if (loc == loc') -- update global store to hold the aexp using the original envv - e.g. x := x + 1, we have to evaluate the RHS x with the original envv
                                                            then a_val_static aexp (Inter_st stm envv envp loc store)
                                                            else store loc')

updateV_st::Config_st->DecV->Config_st
updateV_st config decv  = foldl updateV_st' config decv

updateP_st'::Config_st->(Pname, Stm)->Config_st
updateP_st' (Inter_st statement envv envp loc store) (pname, stm) = Final_st envv envp' loc store
                            where envp' = ENVP_st (\pname' ->  if (pname == pname') then (stm, envv, envp') else ( old_envp pname') )
                                  ENVP_st old_envp = envp
updateP_st' (Final_st envv envp loc store) (pname, stm) = Final_st envv envp' loc store
                            where envp' = ENVP_st (\pname' ->  if (pname == pname') then (stm, envv, envp') else ( old_envp pname') )
                                  ENVP_st old_envp = envp

updateP_st::Config_st->DecP->Config_st
updateP_st config decp = foldl updateP_st' config decp

decVcontainsV :: [(Var, Aexp)] -> Var -> Bool
decV `decVcontainsV` var = (var `elem` decV')
                          where decV' = map fst decV

ns_stm_st :: Config_st -> Config_st
ns_stm_st (Inter_st (Skip) envv envp loc store)           =   Final_st envv envp loc store

ns_stm_st (Inter_st (Comp s1 s2) envv envp loc store )     =   Final_st envv'' envp'' loc'' store''
                                              where
                                              Final_st envv' envp' loc' store'     = ns_stm_st(Inter_st s1 envv envp loc store )
                                              Final_st envv'' envp'' loc'' store'' = ns_stm_st(Inter_st s2 envv' envp' loc' store' )

ns_stm_st (Inter_st (Ass var aexp) envv envp loc store) =  Final_st envv envp loc store' 
                                                  where location = envv var
                                                  store' = (\l -> if l == location then a_val_static aexp (Inter_st stm envv envp loc store)
                                                                  else store l)

ns_stm_st (Inter_st (If bexp s1 s2) envv envp loc store)
    | b_val_static bexp (Inter_st (If bexp s1 s2) envv envp loc store )   = ns_stm_st(Inter_st s1 envv envp loc store)
    | otherwise                                                       = ns_stm_st(Inter_st s2 envv envp loc store)

ns_stm_st (Inter_st (While bexp s1) envv envp loc store )
    | not (b_val_static bexp (Inter_st (While bexp s1) envv envp loc store))      = Final_st envv envp loc store
    | otherwise               = Final_st envv'' envp'' loc'' store''
                                where
                                Final_st envv' envp' loc' store'     = ns_stm_st(Inter_st s1 envv envp loc store)
                                Final_st envv'' envp'' loc'' store'' = ns_stm_st(Inter_st (While bexp s1) envv' envp' loc' store')
-- State holds global variables
ns_stm_st (Inter_st (Block decv decp stm) envv envp loc store)   = Final_st envv envp'' loc'' store''
                                                        where config' = updateV_st (Inter_st (Block decv decp stm) envv envp loc store) decv  -- use local variables using decv
                                                              Final_st envv' envp' loc' store'  = updateP_st config' decp        -- update environment procedure
                                                              Final_st envv'' envp'' loc'' store'' = ns_stm_st(Inter_st stm envv' envp' loc' store')
                                                              



ns_stm_st (Inter_st (Call pname) envv (ENVP_st envp) loc store )    =    Final envv envp'' loc'' store'' 
                                                        where (stm', envv', envp') = envp pname                      -- Get & use local environment
                                                              Final_st envvr envp_recurse locr storer = updateP_st' (Final_st envv' envp' loc store) (pname, stm') -- Update P's procedure environment to include itself
                                                              Final_st envv'' envp'' loc'' store'' = ns_stm_st(Inter_st stm' envv' envp_recurse loc store)

s_static::Stm->Config_st->Config_st
s_static stm (Final_st envv envp loc store) = ns_stm_st (Inter_st stm envv envp loc store)


----------------------------------------------------------------------------------------
----------------------------- * STATIC TEST FUNCTIONS * --------------------------------

s_test1_st = s_testy_st(s_static scope_test (default_config_st))

s_get_store_st::Config_st->Integer->Integer
s_get_store_st (Inter_st stm envv envp loc store) n  = store(n)
s_get_store_st (Final_st envv envp loc store) n = store(n)

s_testx_st::Config_st -> Integer
s_testx_st (Inter_st stm envv envp loc store) = store (envv "x")
s_testx_st (Final_st envv envp loc store) = store (envv "x")
s_testy_st::Config_st -> Integer
s_testy_st (Inter_st stm envv envp loc store) = store (envv "y")
s_testy_st (Final_st envv envp loc store) = store (envv "y")
s_testz_st::Config_st -> Integer
s_testz_st (Inter_st stm envv envp loc store) = store (envv "z")
s_testz_st (Final_st envv envp loc store) = store (envv "z")

----------------------------------------------------------------------------------
----------------------------- * TEST STATEMENTS * --------------------------------

scope_test :: Stm
scope_test = Block [("x",N 0)] [("p",Ass "x" (Mult (V "x") (N 2))),("q",Call "p")] (Block [("x",N 5)] [("p",Ass "x" (Add (V "x") (N 1)))] (Comp (Call "q") (Ass "y" (V "x"))))

fac_recurse :: Stm
fac_recurse = Block [] [("fac",Block [("z",V "x")] [] (If (Eq (V "x") (N 1)) Skip (Comp (Ass "x" (Sub (V "x") (N 1))) (Comp(Ass "y" (Mult (V "z") (V "y")))  (Call "fac") ))))] (Comp (Ass "y" (N 1)) (Call "fac"))

fac_while:: Stm
fac_while = Comp (Ass "y" (N 1)) (While (Neg (Eq (V "x") (N 1))) (Comp (Ass "y" (Mult (V "y") (V "x"))) (Ass "x" (Sub (V "x") (N 1)))))

my_test :: Stm
my_test = Comp (Ass "z" (V "x")) (If (Eq (V "x") (N 1)) Skip (Comp (Ass "x" (Sub (V "x") (N 1))) (Ass "y" (Sub (V "z") (V "y")))))

exercise_2_37 :: Stm
exercise_2_37 = Block [("y",N 1)] [] (Comp (Ass "x" (N 1)) (Comp (Block [("x",N 2)] [] (Ass "y" (Add (V "x") (N 1)))) (Ass "x" (Add (V "y") (V "x")))))

----------------------------------------------------------------------------------
------------------------- * STATIC DEFAULT CONFIGURATION * -----------------------

default_config_st = Final_st def_envv_st def_envp_st def_loc_st def_store_st


def_envv_st :: EnvV
def_envv_st "y" = -5
def_envv_st _ = 0

def_envp_st :: EnvP_st
def_envp_st = ENVP_st (\pname -> (Skip, def_envv_st, def_envp_st))

def_loc_st :: Loc
def_loc_st = 1

def_store_st :: Store
def_store_st -5 = 100
def_store_st _ = 0
------------------------------------------------------------------------------
