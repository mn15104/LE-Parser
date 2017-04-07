module ParseWhile where

import Control.Applicative hiding ((<|>), many)
import Prelude hiding (Num)
import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

-- Grammar of the Proc language
---------------------------------------
-- Aexp ::= Num | Var | Aexp + Aexp | Aexp - Aexp | Aexmp * Aexp
-- Bexp ::= true | false | ~ Bexp | Bexp ^ Bexp | Bexp <= Bexp | Bexp == Bexp
-- Stm  ::= x := a | skip | S1 ; S2 | if b then S1 else S2 | while b do S | begin DV DP S end | call p

type Num   = Integer
type Var   = String
type Pname = String
type DecV  = [(Var,Aexp)]
type DecP  = [(Pname,Stm)]


------------------------------------------

data Aexp = N Num | V Var| Mult Aexp Aexp | Add Aexp Aexp | Sub Aexp Aexp deriving (Show)
data Bexp = TRUE | FALSE | Neg Bexp | And Bexp Bexp | Le Aexp Aexp | Eq Aexp Aexp deriving (Show)
data Stm  = Skip | Comp Stm Stm | Ass Var Aexp | If Bexp Stm Stm | While Bexp Stm | Block DecV DecP Stm | Call Pname deriving (Show)


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

identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis: parens p takes care of the parenthesis and uses p to parse what's inside them
integer    = Token.integer    lexer -- parses an integer
semi       = Token.semi       lexer -- parses a semicolon
whiteSpace = Token.whiteSpace lexer -- parses whitespace




--"(Comp (Ass "y" (N 1)) (While (Neg (Eq (V "x") (N 1))) (Comp (Ass "y"(Mult (V "y") (V "x"))) (Ass "x" (Sub (V "x") (N 1)))))"

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

seqstm_right_asc :: Parser Stm
seqstm_right_asc  = buildExpressionParser semicolon stm'

-- PROC PARSER --

procParser :: Parser Stm
procParser = whiteSpace >> stm

stm :: Parser Stm
stm =   seqstm_right_asc
          <|> parens stm
          <|> block

seqstm_left_asc :: Parser Stm -- separate the statements at the ; into Comp S1 S2
seqstm_left_asc =
 do list <- (sepBy1 stm' semi)
    return $ is_semi list

is_semi :: [Stm] -> Stm
is_semi [] = error "error"
is_semi [x] = x
is_semi (x:xs) = Comp x (is_semi xs)

stm' :: Parser Stm
stm' =      parens stm'
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



-- "/*fac_loop (p.23)*/\ny:=1;\nwhile !(x=1) do (\n y:=y*x;\n x:=x-1\n)"
-- PARSING FUNCTION --

parse' :: String -> Stm
parse' str =
     case parse procParser "" str of
       Left e  -> error $ show e
       Right r -> r
