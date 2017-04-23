{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
import Prelude hiding (Num)
import System.IO
import Control.Monad
import Control.Applicative hiding ((<|>), many)
import qualified Text.ParserCombinators.Parsec as Parsec
import Text.ParserCombinators.Parsec hiding (State, parse)
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token


parse :: String -> Stm
parse str =
       case Parsec.parse procParser "" str of
       Left e  -> error $ show e
       Right r -> r


s_static::Stm->State->State
s_static stm state = final_state
           where (state', envv', loc', store') = analyse_stm stm (state, default_envv_st, default_loc_st, default_store_st)  -- Get initial configuration from state
                 Final_st envv'' envp'' loc'' store'' = s_static' stm (Final_st envv' default_envp_st loc' store')           -- Execute program
                 final_state = (\v -> store''(envv'' v))                                                                     -- Return new state

s_mixed::Stm->State->State
s_mixed stm state = final_state
         where
         Final_m final_state final_envp = ns_stm_m (Inter_m stm state default_envp_m)

s_dynamic::Stm->State->State
s_dynamic stm state = final_state
          where
          Final_d final_state final_envp = ns_stm_d (Inter_d stm state default_envp_d)





-----------------------------------------------------------------------------------------------------------
------------------------------------- * STATIC HELPER FUNCTIONS * -----------------------------------------

s_static'::Stm->Config_st->Config_st  -- Configuration transformer
s_static' stm (Final_st envv envp loc store ) = ns_stm_st (Inter_st stm envv envp loc store )

var_state_st::Var -> Stm -> Integer      -- Variable state tester  -- Using Default Config
var_state_st v stm = final_state v
          where final_state = s_static stm default_state

var_location_st::Var -> Stm -> Integer    -- Variable location tester  -- Using Default Config
var_location_st v stm = envv'' v
          where (state', envv', loc', store') = analyse_stm stm (default_state, default_envv_st, default_loc_st, default_store_st)  -- Get initial configuration from state
                Final_st envv'' envp'' loc'' store'' = s_static' stm (Final_st envv' default_envp_st loc' store')

------------------------------------------------------------------------------------------------------------
-------------------------------------- * MIXED HELPER FUNCTIONS * ----------------------------------------


var_state_m::Var -> Stm -> Integer      -- Dynamic variable state tester; using Default Config
var_state_m v stm = final_state v
          where final_state = s_mixed stm default_state

------------------------------------------------------------------------------------------------------------
------------------------------------- * DYNAMIC HELPER FUNCTIONS * ---------------------------------------


var_state_d::Var -> Stm -> Integer      -- Dynamic variable state tester; using Default Config
var_state_d v stm = final_state v
          where final_state = s_dynamic stm default_state


----------------------------------------------------------------------------------
----------------------------- * TEST STATEMENTS * --------------------------------

fac_loop_string = "/*fac_loop (p.23)*/\ny:=1;\nwhile !(x=1) do (\n y:=y*x;\n x:=x-1\n)"

scope_test :: Stm
scope_test = Block [("x",N 0)] [("p",Ass "x" (Mult (V "x") (N 2))),("q",Call "p")] (Block [("x",N 5)] [("p",Ass "x" (Add (V "x") (N 1)))] (Comp (Call "q") (Ass "y" (V "x"))))

fac_recurse :: Stm
fac_recurse = Block [] [("fac",Block [("z",V "x")] [] (If (Eq (V "x") (N 1)) Skip (Comp (Ass "x" (Sub (V "x") (N 1))) (Comp(Call "fac")(Ass "y" (Mult (V "z") (V "y")))   ))))] (Comp (Ass "y" (N 1)) (Call "fac"))

fac_while:: Stm
fac_while = Comp (Ass "y" (N 1)) (While (Neg (Eq (V "x") (N 1))) (Comp (Ass "y" (Mult (V "y") (V "x"))) (Ass "x" (Sub (V "x") (N 1)))))

exercise_2_37 :: Stm
exercise_2_37 = Block [("y",N 1)] [] (Comp (Ass "x" (N 1)) (Comp (Block [("x",N 2)] [] (Ass "y" (Add (V "x") (N 1)))) (Ass "x" (Add (V "y") (V "x")))))

-----------------------------------------------------------------------------------
------------------------------- * DEFAULT STATE  * --------------------------------

default_state :: State
default_state "x" = 7;
default_state "y" = 8;
default_state "z" = 9;
default_state _ = 100;

----------------------------------------------------------------------------------
------------------------- * STATIC DEFAULT CONFIGURATION * -----------------------

default_config_st = Final_st default_envv_st default_envp_st default_loc_st default_store_st

default_envv_st :: EnvV
default_envv_st _   = -1

default_envp_st :: EnvP_st
default_envp_st = ENVP_st (\pname -> (Skip, default_envv_st, default_envp_st))

default_loc_st :: Loc
default_loc_st = 0

default_store_st :: Store --globals
default_store_st _ = -1

-----------------------------------------------------------------------------------
------------------------- * MIXED DEFAULT CONFIGURATION * -------------------------

default_envp_m :: EnvP_m
default_envp_m = ENVP (\pname -> (Skip, default_envp_m))

-----------------------------------------------------------------------------------
------------------------- * DYNAMIC DEFAULT CONFIGURATION * -----------------------

default_envp_d :: EnvP_d
default_envp_d _ = Skip



----------------------------------------------------------------------------------------------------------
---------------------------------------- * STATIC: AST ANALYSER * ----------------------------------------

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


--------------------------------------------------------------------------------------------
----------------------------- * STATIC SEMANTIC FUNCTIONS * --------------------------------

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



--------------------------------------------------------------------------------------------
----------------------------- * MIXED SEMANTIC FUNCTIONS * -------------------------------


updateP_m'::EnvP_m->(Pname, Stm)->EnvP_m
updateP_m' (ENVP envp_m) (pname, stm) = ENVP (\pname' -> if (pname == pname') then (stm, ENVP envp_m) else ( envp_m pname') )

updateP_m::EnvP_m->DecP->EnvP_m
updateP_m envp_m decp = foldl updateP_m' envp_m decp


ns_stm_m :: Config_m -> Config_m
ns_stm_m (Inter_m (Skip) s  envp_m)          =   Final_m s  envp_m

ns_stm_m (Inter_m (Comp s1 s2) s  envp_m)    =   Final_m s''  envp_m''
                                          where
                                          Final_m s'  envp_m' = ns_stm_m(Inter_m s1 s envp_m)
                                          Final_m s'' envp_m'' = ns_stm_m(Inter_m s2 s' envp_m')

ns_stm_m (Inter_m (Ass var aexp) s envp_m)  =   Final_m (update_state s [(var, aexp)])  envp_m


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
                                              s'                     = update_state s decv          -- Update state mapping for P's local variables
                                              envp_m'                = updateP_m envp_m decp  -- Update procedure mapping for P's procedures
                                              Final_m s'' envp_m''   = ns_stm_m(Inter_m stm s'  envp_m')
                                              s_restore              = (\v -> if decVcontainsV decv v then s v else s'' v )

ns_stm_m (Inter_m (Call pname) s (ENVP envp_m) )    =    ns_stm_m(Inter_m (p_stm) s  (envp_recurse) )
                                                    where
                                                    (p_stm, p_environment)             = envp_m pname                        -- Get & use statically defined body of P
                                                    envp_recurse      = updateP_m' (p_environment) (pname, p_stm)  -- When calling P, update its environment so it recognises itself



---------------------------------------------------------------------------------------------
----------------------------- * DYNAMIC SEMANTIC FUNCTIONS * --------------------------------

decVcontainsV :: [(Var, Aexp)] -> Var -> Bool
decV `decVcontainsV` var = (var `elem` decV')
                          where decV' = map fst decV

update_state'::State->(Var, Aexp)->State
update_state' s (var, aexp) = (\var' -> if (var == var') then a_val aexp s else ( s var' ) )

update_state::State->DecV->State
update_state s decv = foldl update_state' s decv

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

ns_stm_d (Inter_d (Ass var aexp) s envp)  =   Final_d (update_state s [(var, aexp)]) envp

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
                                              s'                = update_state s decv       -- Update state mapping for P's local variables
                                              envp'             = updateP_d envp decp -- Update procedure mapping for P's procedures
                                              Final_d s'' envp''  = ns_stm_d(Inter_d stm s' envp')            -- Execute process and return any (dynamically) updated processes and variables
                                              s_restore = (\v -> if decVcontainsV decv v then s v else s'' v ) -- Ignore local variable declarations in Block Process

ns_stm_d (Inter_d (Call pname) s envp)      =     Final_d s' envp'
                                              where
                                              Final_d s' envp'  = ns_stm_d(Inter_d (envp pname) s envp)



-----------------------------------------------------------------------------------
------------------------ * AEXP/BEXP SEMANTIC FUNCTIONS   * -----------------------

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


---------------------------------------------------------------------------------------
---------------------------------- * QUESTION 2   * -----------------------------------

---------------------------------------------------------------------------------------
---------------------------------- *   PARSER     * -----------------------------------


languageDef =
   emptyDef { Token.commentStart    = "/*"
            , Token.commentEnd      = "*/"
            , Token.commentLine     = "//"
            , Token.identStart      = letter
            , Token.identLetter     = alphaNum
            , Token.reservedNames   = [ "if", "then", "else", "while", "do", "skip", "true", "false", "begin", "end", "call", "var", "proc", "is"]
            , Token.reservedOpNames = ["+", "-", "*", "!", "&", "<=", "=", ":=", ";"]
            }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
integer    = Token.integer    lexer
semi       = Token.semi       lexer
whiteSpace = Token.whiteSpace lexer

-- AEXP --

aExp :: Parser Aexp
aExp = buildExpressionParser aOperators aTerm

aTerm =  parens aExp
     <|> liftM V identifier
     <|> liftM N integer

aOperators = [ [Infix  (reservedOp "*"   >> return (Mult)) AssocRight],
               [Infix  (reservedOp "+"   >> return (Add)) AssocRight,
                Infix  (reservedOp "-"   >> return (Sub)) AssocRight]
             ]

-- BEXP --

bExp :: Parser Bexp
bExp = buildExpressionParser bOperators bTerm

bTerm =  parens bExp
     <|> TRUE <$ reserved "true"
     <|> FALSE <$ reserved "false"
     <|> rExp

rExp =
  do a1 <- aExp
     op <- relation
     a2 <- aExp
     return $ op a1 a2

relation =   (reservedOp "=" >> return Eq)
         <|> (reservedOp "<=" >> return Le)

bOperators = [ [Prefix (reservedOp "!" >> return (Neg))]
             , [Infix  (reservedOp "&" >> return (And)) AssocRight]
             ]

semicolon = [ [Infix  (reservedOp ";"   >> return (Comp)) AssocRight]]

-- PROC PARSER --

procParser :: Parser Stm
procParser = whiteSpace >> stm

stm :: Parser Stm
stm =   seqstm_right_asc
          <|> parens stm
          <|> block

seqstm_right_asc :: Parser Stm
seqstm_right_asc  = buildExpressionParser semicolon stm'

stm' :: Parser Stm
stm' =      parens stm
           <|> skipStm
           <|> call
           <|> block
           <|> ifStm
           <|> whileStm
           <|> assignStm

whitespace :: Parser ()
whitespace = many (oneOf "\ \t \n") *> pure ()

assignStm :: Parser Stm
assignStm = Ass <$> identifier <* reservedOp ":=" <*> aExp

ifStm :: Parser Stm
ifStm = If <$ reserved "if" <*> bExp <* reserved "then" <*> stm <* reserved "else" <*> stm

whileStm :: Parser Stm
whileStm = While <$ reserved "while" <*> bExp <* reserved "do" <*> stm

skipStm :: Parser Stm
skipStm = Skip <$ reserved "skip" <* whiteSpace

block :: Parser Stm
block = Block <$ reserved "begin" <*> vDec <*> pDec <*> stm <* reserved "end"

call :: Parser Stm
call = Call <$ reserved "call" <*> identifier

vDec :: Parser [(Var,Aexp)]
vDec = many vDec'
   where vDec' = do reserved "var"
                    v <- identifier
                    reservedOp ":="
                    expr <- aExp
                    reservedOp ";"
                    return $ (v ,expr)

pDec :: Parser [(Pname,Stm)]
pDec = many pDec'
  where pDec' = do reserved "proc"
                   prog <- identifier
                   reserved "is"
                   s <- stm'
                   reservedOp ";"
                   return $ (prog, s)


---------------------------------------------------------------------------------------------
-------------------------------- * TYPES && DATA TYPES * ------------------------------------

data Aexp = N Num | V Var| Mult Aexp Aexp | Add Aexp Aexp | Sub Aexp Aexp deriving (Show, Eq, Read)
data Bexp = TRUE | FALSE | Neg Bexp | And Bexp Bexp | Le Aexp Aexp | Eq Aexp Aexp deriving (Show, Eq, Read)
data Stm  = Skip | Comp Stm Stm | Ass Var Aexp | If Bexp Stm Stm | While Bexp Stm | Block DecV DecP Stm | Call Pname  deriving (Show, Eq, Read)

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

type EnvP_d    = Pname -> Stm
data Config_d   = Inter_d Stm State EnvP_d | Final_d State EnvP_d

data EnvP_m = ENVP (Pname -> (Stm, EnvP_m))
data Config_m   = Inter_m Stm State EnvP_m | Final_m State EnvP_m

data EnvP_st = ENVP_st (Pname -> (Stm, EnvV, EnvP_st))
data Config_st   = Inter_st Stm EnvV EnvP_st Loc Store  | Final_st EnvV EnvP_st Loc Store







---------------------------------------------------------------------------------------------
