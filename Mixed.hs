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
data EnvP_m = ENVP (Pname -> (Stm, EnvP_m))
type EnvV = Var   -> Z
data Config   = Inter Stm State EnvP_m | Final State EnvP_m
data Stm  = Skip | Comp Stm Stm | Ass Var Aexp | If Bexp Stm Stm | While Bexp Stm | Block DecV DecP Stm | Call Pname
      deriving (Show, Eq, Read)


updateV'::State->(Var, Aexp)->State
updateV' s (var, aexp) = (\var' -> if (var == var') then a_val aexp s else ( s var' ) )

updateV::State->DecV->State
updateV s decv = foldl updateV' s decv

updateP'::EnvP_m->(Pname, Stm)->EnvP_m
updateP' (ENVP envp_m) (pname, stm) = ENVP (\pname' -> if (pname == pname') then (stm, ENVP envp_m) else ( envp_m pname') )

updateP::EnvP_m->DecP->EnvP_m
updateP envp_m decp = foldl updateP' envp_m decp

-- Introduce 'current environment' variable?

ns_stm :: Config -> Config
ns_stm (Inter (Skip) s  envp_m)          =   Final s  envp_m

ns_stm (Inter (Comp s1 s2) s  envp_m)    =   Final s''  envp_m''
                                          where
                                          Final s'  envp_m' = ns_stm(Inter s1 s envp_m)
                                          Final s'' envp_m'' = ns_stm(Inter s2 s' envp_m')

ns_stm (Inter (Ass var aexp) s envp_m)  =   Final (updateV s [(var, aexp)])  envp_m
                                        --  where
                                        --  z = a_val aexp s

ns_stm (Inter (If bexp s1 s2) s envp_m)
    | b_val bexp s  = ns_stm(Inter s1 s envp_m)
    | otherwise     = ns_stm(Inter s2 s envp_m)

ns_stm (Inter (While bexp s1) s envp_m)
    | not (b_val bexp s)      = Final s envp_m
    | otherwise               = Final s'' envp_m''
                                where
                                Final s' envp_m' = ns_stm(Inter s1 s envp_m)
                                Final s'' envp_m'' = ns_stm(Inter (While bexp s1) s' envp_m')

ns_stm (Inter (Block decv decp stm) s envp_m)   = Final s'' envp_m''
                                              where
                                              s'                          = updateV s decv
                                              envp_m'                     = updateP envp_m decp
                                              Final s'' envp_m''   = ns_stm(Inter stm s'  envp_m')

ns_stm (Inter (Call pname) s (ENVP envp_m) )    =    ns_stm(Inter (stm') s  (recursive_envp_update) )
                                                    where
                                                    (stm', envp_m')             = envp_m pname                      -- Get & use local environment of P
                                                    recursive_envp_update       = updateP' (envp_m') (pname, stm')  -- When calling P, update its environment so it recognises itself

s_mixed::Stm->Config->Config
s_mixed   stm (Final s envp) = Final s' envp'
          where
          Final s'  envp' = ns_stm (Inter stm s envp)

s_test1 = s_testx(s_mixed s1''' (Final s2 s3))
s_test2 = s_testy(s_mixed s1''' (Final s2 s3))
s_test3 = s_testz(s_mixed s1'' (Final s2 s3))
s_testx::Config -> Integer
s_testx (Inter stm state envp_m) = state "x"
s_testx (Final state envp_m) = state "x"
s_testy::Config -> Integer
s_testy (Inter stm state envp) = state "y"
s_testy (Final state envp) = state "y"
s_testz::Config -> Integer
s_testz (Inter stm state envp) = state "z"
s_testz (Final state envp) = state "z"


s1 :: Stm
s1 = Block [("X", N 5)] [("foo", Skip)] Skip

s1' :: Stm
s1' = Block [("x",N 0)] [("p",Ass "x" (Mult (V "x") (N 2))),("q",Call "p")] (Block [("x",N 5)] [("p",Ass "x" (Add (V "x") (N 1)))] (Call "q"))

s1'' :: Stm
s1'' = Block [] [("fac",Block [("z",V "x")] [] (If (Eq (V "x") (N 1)) Skip (Comp (Ass "x" (Sub (V "x") (N 1))) (Comp (Ass "y" (Mult (V "z") (V "y"))) (Call "fac") ))))] (Comp (Ass "y" (N 1)) (Call "fac"))

s1''' :: Stm
s1''' = Comp (Ass "y" (N 1)) (While (Neg (Eq (V "x") (N 1))) (Comp (Ass "y" (Mult (V "y") (V "x"))) (Ass "x" (Sub (V "x") (N 1)))))

--
s2 :: State
s2 "x" = 5
s2 _ = 0


s3 :: EnvP_m
s3 = ENVP (\pname -> (Skip, s3))
