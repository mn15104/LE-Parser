
> import Prelude hiding (Num)
> import qualified Prelude (Num)


-- Types and Constructors --

> type Num = Integer
> type Var = String
> type Z   = Integer
> type T   = Bool

> type State = (Var -> Z)

> data Aexp = N Num | V Var | Mult Aexp Aexp |
>               Add Aexp Aexp | Sub Aexp Aexp
>   deriving (Show, Eq, Read)

> data Bexp = TRUE | FALSE | Neg Bexp | And Bexp Bexp |
>               Eq Aexp Aexp | Le Aexp Aexp | Imp Bexp Bexp
>   deriving (Show, Eq, Read)

> data Stm = Ass Var Aexp | Skip | Comp Stm Stm |
>               If Bexp Stm Stm | While Bexp Stm
>   deriving (Show, Eq, Read)


-- Terms --

> s :: State
> s = (\x -> if x == "x" then 1
>               else if x == "y" then 2
>                       else if x == "z" then 3 else 0)

> s' :: State
> s' = update s 5 "x"

 s "x" = 1
 s "y" = 2
 s "z" = 3
 s  _  = 0

> a :: Aexp
> a = Mult ( Add ( V ( "x" ) ) ( V ( "y" ) ) ) ( Sub ( V ( "x" ) ) ( N ( -1 ) ) )

> b :: Bexp
> b = Neg ( Eq ( Add ( V ( "x" ) ) ( V ( "y" ) ) ) ( N ( 4 ) ) )

> p :: Stm
> p = Comp ( Ass ( "y" ) ( N (1) ) )
>       ( While (Neg ( Eq ( V ( "x" ) ) ( N ( 1 ) ) ) )
>       ( Comp (Ass ("x") ( Sub ( V ("x") ) ( N (-1) ) ) )
>       ( Ass ("y") ( Mult ( V ("y") ) ( V ("x") ) ) ) ) )


-- Functions --

> n_val :: Num -> Z -- The Semantic Function
> n_val x = x

> a_val :: Aexp -> State -> Z
> a_val ( V x ) s        = s x
> a_val ( N x ) s        = x
> a_val ( Mult x y )  s  = ( a_val x s ) * ( a_val y s )
> a_val ( Add x y  )  s  = ( a_val x s ) + ( a_val y s )
> a_val ( Sub x y  )  s  = ( a_val x s ) - ( a_val y s )

> b_val :: Bexp -> State -> T
> b_val TRUE          s = True
> b_val FALSE         s = False
> b_val ( Eq x y  )   s = ( a_val x s ) == ( a_val y s )
> b_val ( Neg x   )   s = not ( ( b_val x s ) )
> b_val ( And x y )   s = and [ ( b_val x s ), ( b_val x s ) ]
> b_val ( Le x y  )   s = ( a_val x s ) <= ( a_val y s )
> b_val ( Imp x y )   s = not( and [ ( b_val x s ), not( b_val y s ) ] )

> update::State->Z->Var->State
> update s i v = (\v' -> if (v == v') then i else ( s v' ) )

> cond :: ( a->T, a->a, a->a ) ->( a->a )
> cond (b, s1, s2) x  = if (b x) then (s1 x) else (s2 x)

> fix :: ((State->State)->(State->State))->(State->State)
> fix ff = ff (fix ff)

> s_ds::Stm->State->State
> s_ds ( Ass v a ) s    = update s (a_val a s) v
> s_ds ( Skip ) s       = s
> s_ds ( Comp s1 s2 ) s = s_ds s2 (s_ds s1 s)
> s_ds ( If b s1 s2 ) s = undefined
> s_ds ( While b s1 ) s = undefined




ss Var Aexp | Skip | Comp Stm Stm |
               If Bexp Stm Stm | While Bexp Stm

