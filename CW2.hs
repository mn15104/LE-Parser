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


-- PARSING FUNCTION --

parse' :: String -> Stm
parse' str =
     case parse procParser "" str of
       Left e  -> error $ show e
       Right r -> r

-- ""(Comp (Ass "y" (N 1)) (While (Neg (Eq (V "x") (N 1))) (Comp (Ass "y"(Mult (V "y") (V "x"))) (Ass "x" (Sub (V "x") (N 1))))))"


-- AEXP --

aExp :: Parser Aexp
aExp = buildExpressionParser aOperators aTerm

aTerm =  parens aExp
     <|> liftM V identifier
     <|> liftM N integer

aOperators = [ [Infix  (reservedOp "*"   >> return (Mult)) AssocLeft],
               [Infix  (reservedOp "+"   >> return (Add)) AssocLeft,
                Infix  (reservedOp "-"   >> return (Sub)) AssocLeft]
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
             , [Infix  (reservedOp "&" >> return (And)) AssocLeft]
             ]

-- PROC PARSER --

procParser :: Parser Stm
procParser = whiteSpace >> stm

stm :: Parser Stm
stm =   parens stm
          <|> comp
          <|> block

comp :: Parser Stm
comp =
   do s1 <- stm'
      reserved ";"
      s2 <- stm'
      return $ Comp s1 s2

stm' :: Parser Stm
stm' =      ifStm
           <|> whileStm
           <|> skipStm
           <|> assignStm
           <|> block
           <|> call

var :: Parser Var
var = many1(oneOf ['A' .. 'Z'] <|> oneOf ['a' .. 'z']) <* whiteSpace

whitespace :: Parser ()
whitespace = many (oneOf "\ \t \n") *> pure ()

assignStm :: Parser Stm
assignStm = Ass <$> var <* reservedOp ":=" <*> aExp

ifStm :: Parser Stm
ifStm = If <$ reserved "if" <*> bExp <* reserved "then" <*> stm <* reserved "else" <*> stm

whileStm :: Parser Stm
whileStm = While <$ reserved "while" <*> bExp <* reserved "do" <*> stm

skipStm :: Parser Stm
skipStm = Skip <$ reserved "skip"

block :: Parser Stm
block = Block <$ reserved "begin" <*> vDec <*> pDec <*> stm <* reserved "end"

vDec :: Parser [(Var,Aexp)]
vDec = many vDec'
   where vDec' = do reserved "var"
                    v <- var
                    reservedOp ":="
                    expr <- aExp
                    reservedOp ";"
                    return $ (v ,expr)

pDec :: Parser [(Pname,Stm)]
pDec = many pDec'
  where pDec' = do reserved "proc"
                   prog <- var
                   reserved "is"
                   s <- stm'
                   reservedOp ";"
                   return $ (prog, s)

call :: Parser Stm
call = Call <$ reserved "call" <*> var