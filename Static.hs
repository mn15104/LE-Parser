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

a_val_state::Aexp->State->Z
a_val_state (N n) s       = n_val(n)
a_val_state (V v) s       = s v
a_val_state (Mult a1 a2) s = a_val_state(a1)s * a_val_state(a2)s
a_val_state (Add a1 a2)  s = a_val_state(a1)s + a_val_state(a2)s
a_val_state (Sub a1 a2)  s = a_val_state(a1)s - a_val_state(a2)s

a_val::Aexp->EnvV->Store->Z
a_val (N n) s st        = n_val(n)
a_val (V v) s st        = st (s v)
a_val (Mult a1 a2) s st = a_val(a1)s st * a_val(a2)s st
a_val (Add a1 a2)  s st = a_val(a1)s st + a_val(a2)s st
a_val (Sub a1 a2)  s st = a_val(a1)s st - a_val(a2)s st

b_val::Bexp->EnvV->Store->T
b_val (TRUE)  s  st   = True
b_val (FALSE) s  st   = False
b_val (Neg b) s  st
  | (b_val(b)s st)     = False
  | otherwise       = True
b_val (And b1 b2) s st
  | b_val(b1)s st && b_val(b2)s st = True
  | otherwise = False
b_val (Eq a1 a2) s st
  | a_val(a1)s st == a_val(a2)s st = True
  | a_val(a1)s st /= a_val(a2)s st = False
b_val (Le a1 a2) s st
  | a_val(a1)s st <= a_val(a2)s st  = True
  | otherwise = False


cond :: ( a->T, a->a, a->a ) ->( a->a )
cond (b, s1, s2) x  = if (b x) then (s1 x) else (s2 x)

fix :: ((State->State)->(State->State))->(State->State)
fix ff = ff (fix ff)


data Aexp = N Num | V Var| Mult Aexp Aexp | Add Aexp Aexp | Sub Aexp Aexp
      deriving (Show, Eq, Read)
data Bexp = TRUE | FALSE | Neg Bexp | And Bexp Bexp | Le Aexp Aexp | Eq Aexp Aexp
      deriving (Show, Eq, Read)

type Num   = Integer
type Var   = String
type Pname = String
type Z = Integer
type T = Bool

type DecV  = [(Var,Aexp)]
type DecP  = [(Pname,Stm)]
type State = Var -> Z
data EnvP = ENVP (Pname -> (Stm, EnvV, EnvP))
data Config   = Inter Stm State EnvV EnvP Loc Store DecV| Final State EnvV EnvP Loc Store DecV
data Stm  = Skip | Comp Stm Stm | Ass Var Aexp | If Bexp Stm Stm | While Bexp Stm | Block DecV DecP Stm | Call Pname
      deriving (Show, Eq, Read)

type Loc = Num

type EnvV = Var  -> Loc   -- Mapping #1: Associates a location with a variable
type Store = Loc -> Z     -- Mapping #2: Associates a variable value with a location

-- To determine value of variable x : 1) Find location of variable 2) Find value stored in location

new :: Loc -> Loc
new loc = loc + 1
-- We're updating values by increasing loc & store, when we should actually be updating an existing value
updateV'::Config->(Var, Aexp)->Config
updateV' (Inter stm s envv envp loc store decv) (var, aexp) = Final s envv' envp nextloc newstore decv
                            where nextloc = new loc;                    -- inside current procedure A
                                  envv' = (\var' -> if (var == var')    -- update current environment's variable to location mapping -- difference between decv and assign, i.e. updateV and update, only decv is static inside a procedure
                                                    then loc            -- variables inside a begin decv s end block are static to it
                                                    else ( envv var' ))
                                  newstore = (\loc' -> if (loc == loc') -- update global store to hold the aexp using the original envv - e.g. x := x + 1, we have to evaluate the RHS x with the original envv
                                                            then a_val aexp envv store
                                                            else store loc')

updateV::Config->DecV->Config
updateV config decv  = foldl updateV' config decv

updateP'::Config->(Pname, Stm)->Config
updateP' (Inter statement s envv envp loc store decv) (pname, stm) = Final s envv envp' loc store decv
                            where envp' = ENVP (\pname' ->  if (pname == pname') then (stm, envv, envp') else ( old_envp pname') )
                                  ENVP old_envp = envp
updateP' (Final s envv envp loc store decv) (pname, stm) = Final s envv envp' loc store decv
                            where envp' = ENVP (\pname' ->  if (pname == pname') then (stm, envv, envp') else ( old_envp pname') )
                                  ENVP old_envp = envp

updateP::Config->DecP->Config
updateP config decp = foldl updateP' config decp

updateS::Config->Z->Var->Config
updateS (Inter stm s envv envp loc store decv) z v =  Final s' envv envp loc store decv
                                                      where s' = (\v' -> if (v == v') then z else ( s v' ) )


ns_stm :: Config -> Config
-- ns_stm (Inter (Skip) s envv envp loc store)           =   Final s envv envp loc store
--
-- ns_stm (Inter (Comp s1 s2) s envv envp loc store)     =   Final s'' envv'' envp'' loc'' store''
--                                               where
--                                               Final s'  envv' envp' loc' store'     = ns_stm(Inter s1 s envv envp loc store)
--                                               Final s'' envv'' envp'' loc'' store'' = ns_stm(Inter s2 s' envv' envp' loc' store')
--

decVcontainsV :: [(Var, Aexp)] -> Var -> Bool
decV `decVcontainsV` var = (var `elem` decV')
                          where decV' = map fst decV

ns_stm (Inter (Ass var aexp) s envv envp loc store decv)
  | decVcontainsV decv var  = updateV (Inter (Ass var aexp) s envv envp loc store decv) ([(var, aexp)])             -- update local variable
  | (envv var == -1)        = updateS (Inter (Ass var aexp) s envv envp loc store decv) (a_val_state aexp s) var    -- update global variable using state (global variables)
  | otherwise               = updateS (Inter (Ass var aexp) s envv envp loc store decv) (a_val aexp envv store) var --update global variable using local variable

-- -- Ass -> return the envv
-- ns_stm (Inter (If bexp s1 s2) s envv envp loc store)
--     | b_val bexp envv store   = ns_stm(Inter s1 s envv envp loc store)
--     | otherwise               = ns_stm(Inter s2 s envv envp loc store)
--
-- ns_stm (Inter (While bexp s1) s envv envp loc store)
--     | not (b_val bexp envv store)      = Final s envv envp loc store
--     | otherwise               = Final s'' envv'' envp'' loc'' store''
--                                 where
--                                 Final s' envv' envp' loc' store' = ns_stm(Inter s1 s envv envp loc store)
--                                 Final s'' envv'' envp'' loc'' store'' = ns_stm(Inter (While bexp s1) s' envv' envp' loc' store')
-- State holds global variables
ns_stm (Inter (Block decv decp stm) s envv envp loc store olddecv)   = Final s'' envv envp'' loc'' store'' olddecv
                                                        where Final s'' env'' envp'' loc'' store'' decv'' = ns_stm(Inter stm s' envv' envp' loc' store' decv)
                                                              Final s' envv' envp' loc' store' decv = updateP config' decp
                                                              config' = updateV (Inter (Block decv decp stm) s envv envp loc store decv) decv
--
-- ns_stm (Inter (Call pname) s envv (ENVP envp)  loc store)    =    Final s'' envv envp'' loc'' store''
--                                                                   where (stm', envv', envp' )  = envp pname                      -- Get & use local environment
--                                                                         Final s'' envv'' envp'' loc'' store'' = ns_stm(Inter (stm') s  envv' recursive_envp_update loc store)
--                                                                         Final sr envvr recursive_envp_update locr storer = updateP' (Final s envv' envp' loc store) (pname, stm') -- update P's procedure environment to include itself
-- --------------only decv of a procedure is static
-- --- if decv, update local envv
-- --- if assign, make it global
-- --- always return
--
--
-- s_static::Stm->Config->Config
-- s_static  stm (Final s envv envp loc store) = ns_stm (Inter stm s envv envp loc store)
--
-- s_test1 = s_testx(s_static s1' (Final s2 s3 s4 s5 s6))
-- s_test2 = s_testy(s_static s1' (Final s2 s3 s4 s5 s6))
-- s_test3 = s_testz(s_static s1''' (Final s2 s3 s4 s5 s6))
-- s_test4 = s_testlocal(s_static s1' (Final s2 s3 s4 s5 s6))
-- s_test5 n = s_teststore n (s_static s1' (Final s2 s3 s4 s5 s6))
--
-- s_teststore::Integer->Config -> Integer
-- s_teststore n (Inter stm state envv envp loc store) = store(n)
-- s_teststore n (Final state envv envp loc store) = store(n)
-- s_testlocal::Config -> Integer
-- s_testlocal (Inter stm state envv envp loc store) = loc
-- s_testlocal (Final state envv envp loc store) = loc
-- s_testx::Config -> Integer
-- s_testx (Inter stm state envv envp loc store) = store (envv "x")
-- s_testx (Final state envv envp loc store) = store (envv "x")
-- s_testy::Config -> Integer
-- s_testy (Inter stm state envv envp loc store) = store (envv  "y")
-- s_testy (Final state envv envp loc store) = store (envv "y")
-- s_testz::Config -> Integer
-- s_testz (Inter stm state envv envp loc store) = store (envv "z")
-- s_testz (Final state envv envp loc store) = store (envv "z")
--
-- -- Checklist : neg, eq
-- s1 :: Stm
-- s1 = Block [("X", N 5)] [("foo", Skip)] Skip
--
-- s1' :: Stm
-- s1' = Block [("x",N 0)] [("p",Ass "x" (Mult (V "x") (N 2))),("q",Call "p")] (Block [("x",N 5)] [("p",Ass "x" (Add (V "x") (N 1)))] (Call "q"))
--
-- s1'' :: Stm
-- s1'' = Block [] [("fac",Block [("z",V "x")] [] (If (Eq (V "x") (N 1)) Skip (Comp (Ass "x" (Sub (V "x") (N 1))) (Comp (Ass "y" (Mult (V "z") (V "y"))) (Call "fac") ))))] (Comp (Ass "y" (N 1)) (Call "fac"))
--
-- s1''' :: Stm
-- s1''' = Comp (Ass "y" (N 1)) (While (Neg (Eq (V "x") (N 1))) (Comp (Ass "y" (Mult (V "y") (V "x"))) (Ass "x" (Sub (V "x") (N 1)))))
--
-- s1'''' :: Stm
-- s1'''' = Comp (Ass "z" (V "x")) (If (Eq (V "x") (N 1)) Skip (Comp (Ass "x" (Sub (V "x") (N 1))) (Ass "y" (Sub (V "z") (V "y")))))
--
-- --
-- s2 :: State
-- s2 _ = 0
--
-- s3 :: EnvV
-- s3 "x" = 0
-- s3 _ = 0
--
-- s4 :: EnvP
-- s4 = ENVP (\pname -> (Skip, s3, s4))
--
-- s5 :: Loc
-- s5 = 1
--
-- s6 :: Store
-- s6 0 = 10
-- s6 _ = 7
