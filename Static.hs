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
data Config_st   = Inter_st Stm EnvV EnvP_st Loc Store  | Final_st EnvV EnvP_st Loc Store


new :: Loc -> Loc
new loc = loc + 1

updateV_st'::Config_st->(Var, Aexp)->Config_st
updateV_st' (Inter_st stm envv envp loc store ) (var, aexp) = Final_st envv' envp nextloc newstore
                            where nextloc = new loc;                    -- inside current procedure A
                                  envv' = (\var' -> if (var == var')    -- update current environment's variable to location mapping -- difference between decv and assign, i.e. updateV_st and update, only decv is static inside a procedure
                                                    then loc            -- variables inside a begin decv s end block are static to it
                                                    else ( envv var' ))
                                  newstore = (\loc' -> if (loc == loc') -- update global store to hold the aexp using the original envv - e.g. x := x + 1, we have to evaluate the RHS x with the original envv
                                                            then a_val_static aexp (Inter_st stm envv envp loc store )
                                                            else store loc')

updateV_st::Config_st->DecV->Config_st
updateV_st config decv  = foldl updateV_st' config decv

updateP_st'::Config_st->(Pname, Stm)->Config_st
updateP_st' (Inter_st statement envv envp loc store ) (pname, stm) = Final_st envv envp' loc store
                            where envp' = ENVP_st (\pname' ->  if (pname == pname') then (stm, envv, envp') else ( old_envp pname') )
                                  ENVP_st old_envp = envp
updateP_st' (Final_st envv envp loc store ) (pname, stm) = Final_st envv envp' loc store
                            where envp' = ENVP_st (\pname' ->  if (pname == pname') then (stm, envv, envp') else ( old_envp pname') )
                                  ENVP_st old_envp = envp

updateP_st::Config_st->DecP->Config_st
updateP_st config decp = foldl updateP_st' config decp

ns_stm_st :: Config_st -> Config_st
ns_stm_st (Inter_st (Skip) envv envp loc store )           =   Final_st envv envp loc store

ns_stm_st (Inter_st (Comp s1 s2) envv envp loc store )     =   Final_st envv'' envp'' loc'' store''
                                              where
                                              Final_st envv' envp' loc' store'     = ns_stm_st(Inter_st s1 envv envp loc store  )
                                              Final_st envv'' envp'' loc'' store''   = ns_stm_st(Inter_st s2 envv' envp' loc' store' )

ns_stm_st (Inter_st (Ass var aexp) envv envp loc store ) =  Final_st envv envp loc store'
                                                  where
                                                  location = envv var
                                                  store' = (\l -> if l == location then a_val_static aexp (Inter_st (Ass var aexp) envv envp loc store ) else store l)


ns_stm_st (Inter_st (If bexp s1 s2) envv envp loc store )
    | b_val_static bexp (Inter_st (If bexp s1 s2) envv envp loc store  )    = ns_stm_st(Inter_st s1 envv envp loc store )
    | otherwise                                                             = ns_stm_st(Inter_st s2 envv envp loc store )

ns_stm_st (Inter_st (While bexp s1) envv envp loc store )
    | not (b_val_static bexp (Inter_st (While bexp s1) envv envp loc store ))      = Final_st envv envp loc store
    | otherwise               = Final_st envv'' envp'' loc'' store''
                                where
                                Final_st envv' envp' loc' store'     = ns_stm_st(Inter_st s1 envv envp loc store )
                                Final_st envv'' envp'' loc'' store''  = ns_stm_st(Inter_st (While bexp s1) envv' envp' loc' store' )


ns_stm_st (Inter_st (Block decv decp stm) envv envp loc store )   = Final_st envv envp'' loc'' store''
                                                        where config' = updateV_st (Inter_st (Block decv decp stm) envv envp loc store ) decv  -- use local variables using decv
                                                              Final_st envv' envp' loc' store' = updateP_st config' decp        -- update environment procedure
                                                              Final_st envv'' envp'' loc'' store'' = ns_stm_st(Inter_st stm envv' envp' loc' store' )

ns_stm_st (Inter_st (Call pname) envv (ENVP_st envp) loc store )    =    Final_st envv envp'' loc'' store''
                                                       where (stm', envv', envp') = envp pname                      -- Get & use local environment
                                                             Final_st envvr envp_recurse locr storer  = updateP_st' (Final_st envv' envp' loc store ) (pname, stm') -- Update P's procedure environment to include itself
                                                             Final_st envv'' envp'' loc'' store'' = ns_stm_st(Inter_st stm' envv' envp_recurse loc store )




----------------------------------------------------------------------------------------
----------------------------- * STATIC: SYNTACTIC ANALYSIS * --------------------------------

analyse_decv::DecV->(State,EnvV,Loc,Store)->(State,EnvV,Loc,Store)
analyse_decv decv (state, envv, loc, store) = foldl analyse_decv' (state, envv, loc, store) decv

analyse_decv'::(State,EnvV,Loc,Store)->(Var, Aexp)->(State,EnvV,Loc,Store)
analyse_decv' (state, envv, loc, store) (var, aexp) = (state, envv', loc', store')
                            where loc' = new loc;                    -- inside current procedure A
                                  envv' = (\var' -> if (var == var')    -- update current environment's variable to location mapping -- difference between decv and assign, i.e. updateV_st and update, only decv is static inside a procedure
                                                    then loc            -- variables inside a begin decv s end block are static to it
                                                    else ( envv var' ))
                                  store' = (\n -> if (n == loc) -- update global store to hold the aexp using the original envv - e.g. x := x + 1, we have to evaluate the RHS x with the original envv
                                                    then state var
                                                    else store n)

analyse_decp::DecP->(State,EnvV,Loc,Store)->(State,EnvV,Loc,Store)
analyse_decp decp (state, envv, loc, store) = foldl analyse_decp' (state, envv, loc, store) decp

analyse_decp'::(State,EnvV,Loc,Store)->(Pname,Stm)->(State,EnvV,Loc,Store)
analyse_decp' (state, envv, loc, store) (pname, stm) = analyse_stm stm (state, envv, loc, store)

analyse_aexp::Aexp->(State,EnvV,Loc,Store)->(State,EnvV,Loc,Store)
analyse_aexp (N num) (state, envv, loc, store) = (state, envv, loc, store)
analyse_aexp (V var) (state, envv, loc, store) = (state, envv', loc', store')
                            where loc' = new loc;                    -- inside current procedure A
                                  envv' = (\var' -> if (var == var')    -- update current environment's variable to location mapping -- difference between decv and assign, i.e. updateV_st and update, only decv is static inside a procedure
                                                    then loc            -- variables inside a begin decv s end block are static to it
                                                    else ( envv var' ))
                                  store' = (\n -> if (n == loc) -- update global store to hold the aexp using the original envv - e.g. x := x + 1, we have to evaluate the RHS x with the original envv
                                                    then state var
                                                    else store n)
analyse_aexp (Mult a1 a2) (state, envv, loc, store) = analyse_aexp a2 (state, envv', loc', store')
                                                where (state', envv', loc', store') = analyse_aexp a1 (state, envv, loc, store)
analyse_aexp (Add a1 a2) (state, envv, loc, store) = analyse_aexp a2 (state, envv', loc', store')
                                                where (state', envv', loc', store') = analyse_aexp a1 (state, envv, loc, store)
analyse_aexp (Sub a1 a2) (state, envv, loc, store) = analyse_aexp a2 (state, envv', loc', store')
                                                where (state', envv', loc', store') = analyse_aexp a1 (state, envv, loc, store)

analyse_bexp::Bexp->(State,EnvV,Loc,Store)->(State,EnvV,Loc,Store)
analyse_bexp (TRUE) (state, envv, loc, store) = (state, envv, loc, store)
analyse_bexp (FALSE) (state, envv, loc, store) = (state, envv, loc, store)
analyse_bexp (Neg b) (state, envv, loc, store) = analyse_bexp b (state, envv, loc, store)
analyse_bexp (And b1 b2) (state, envv, loc, store) = analyse_bexp b2 (state, envv', loc', store')
                                                where (state', envv', loc', store') = analyse_bexp b1 (state, envv, loc, store)
analyse_bexp (Le a1 a2) (state, envv, loc, store) = analyse_aexp a2 (state, envv', loc', store')
                                                where (state', envv', loc', store') = analyse_aexp a2 (state, envv, loc, store)
analyse_bexp (Eq a1 a2) (state, envv, loc, store) = analyse_aexp a2 (state, envv', loc', store')
                                                where (state', envv', loc', store') = analyse_aexp a2 (state, envv, loc, store)

analyse_stm::Stm->(State,EnvV,Loc,Store)->(State,EnvV,Loc,Store)

analyse_stm Skip (state, envv, loc, store) = (state, envv, loc, store)

analyse_stm (Comp s1 s2) (state, envv, loc, store) = analyse_stm s2 (state ,envv', loc', store')
                                    where (state', envv', loc', store') = analyse_stm s1 (state ,envv, loc, store)

analyse_stm (Ass var aexp) (state, envv, loc, store)  = (state, envv'', loc'', store'')
                                    where envv' = (\v -> if v == var then loc else envv v)
                                          store' = (\n -> if n == loc then state var else store n)
                                          loc' = new loc
                                          (state'', envv'', loc'', store'') = analyse_aexp aexp (state, envv', loc', store')

analyse_stm (If bexp s1 s2) (state, envv, loc, store) =  analyse_stm s2 (state, envv'', loc'', store'')
                                    where (state', envv', loc', store') = analyse_bexp bexp (state, envv, loc, store)
                                          (state'', envv'', loc'', store'') = analyse_stm s1 (state', envv', loc', store')

analyse_stm (While bexp s) (state, envv, loc, store) = analyse_stm s (state', envv', loc', store')
                                    where (state', envv', loc', store') = analyse_bexp bexp (state, envv, loc, store)

analyse_stm (Block decv decp s) (state, envv, loc, store) = analyse_stm s (state'', envv'', loc'', store'')
                                                  where (state', envv', loc', store') = analyse_decv decv (state, envv, loc, store)
                                                        (state'', envv'', loc'', store'') = analyse_decp decp (state, envv', loc', store')

analyse_stm (Call pname) (state, envv, loc, store) = (state, envv, loc, store)

----------------------------------------------------------------------------------------
----------------------------- * STATIC TEST FUNCTIONS * --------------------------------

s_static::Stm->State->State           -- State transformer
s_static stm state = final_state
          where (state', envv', loc', store') = analyse_stm stm (state, default_envv_st, default_loc_st, default_store_st)  -- Get initial configuration from state
                Final_st envv'' envp'' loc'' store'' = s_static' stm (Final_st envv' default_envp_st loc' store')  -- Execute program
                final_state = (\v -> store''(envv'' v))                                                       -- Return new state

s_static'::Stm->Config_st->Config_st  -- Configuration transformer
s_static' stm (Final_st envv envp loc store ) = ns_stm_st (Inter_st stm envv envp loc store )

var_state_st::Var -> Stm -> Integer      -- Variable state tester  -- Using Default Config
var_state_st v stm = final_state v
          where final_state = s_static stm default_state_st

var_location_st::Var -> Stm -> Integer    -- Variable location tester  -- Using Default Config
var_location_st v stm = envv'' v
          where (state', envv', loc', store') = analyse_stm stm (default_state_st, default_envv_st, default_loc_st, default_store_st)  -- Get initial configuration from state
                Final_st envv'' envp'' loc'' store'' = s_static' stm (Final_st envv' default_envp_st loc' store')


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
------------------------- * STATIC DEFAULT CONFIGURATION * -----------------------

default_config_st = Final_st default_envv_st default_envp_st default_loc_st default_store_st

default_envv_st :: EnvV
default_envv_st _   = -1

default_envp_st :: EnvP_st
default_envp_st = ENVP_st (\pname -> (Skip, default_envv_st, default_envp_st))

default_loc_st :: Loc
default_loc_st = 0

--globals
default_store_st :: Store
default_store_st _ = -1

default_state_st :: State
default_state_st "x" = 7;
default_state_st "y" = 8;
default_state_st "z" = 9;
default_state_st _ = 100;


------------------------------------------------------------------------------
