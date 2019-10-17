module ULC where
import MonadicParser
import Data.Char
import Control.Monad
import Control.Applicative
import Text.Show.Unicode
-- Goal: Parse valid expressions and create a beta redux repl
-- abstract syntax tree definition
-- parsers
-- check terms are valid (no unbound variables)
-- beta reduction rules

--Tree

data Term = Abs Term Term
          | App Term Term
          | Lit String deriving Show
          
--Parsers
{-
BKN rules:

iden     := ['a'-'z','A'-'Z']?
lam      := '(' '_'* iden '_'*  '->' '_'* termlist ')'
termlist := term ( term )?
term     := iden '_'?
          | lam
expr     := termlist

-}

iden :: Parser (Term)
iden = do
  id <- some (sat isAlpha)
  return $ Lit id

lam' :: Parser(Term)
lam' = do
  spaces
  id <- iden
  spaces
  reserved "->"
  spaces
  t <- inr
  return (Abs id t)
  
  
lam :: Parser (Term)
lam = do
  parens lam'

term :: Parser (Term)
term = iden
  <|> lam

expr :: Parser(Term)
expr = chainl1 (do t <- lam; spaces; return t) (pure App)

inr :: Parser (Term)
inr = chainl1 (do t<-term; spaces; return t) (pure App)


main = forever $ do
  putStr ">> "
  s <- getLine
  uprint $ pp $ eval $  runParser expr s

-- C-x 8 RET   03bb
pp :: Term -> String
pp (Lit x) = x
pp (Abs (Lit x) t) = "("++"λ."++x++"->"++(pp t)++")"
pp (App t1 t2) = (pp t1) ++ " " ++ (pp t2)

pprint x= uprint $ pp x

delete e xs = filter (\x -> x/=e) xs

freeVars :: Term -> [String]
freeVars (Lit x) = [x]
freeVars (Abs (Lit x) term) = delete x (freeVars term)
freeVars (App t1 t2) = (freeVars t1) ++ (freeVars t2)

rename :: String -> String -> Term -> Term
rename x x'(Lit y) = if x == y then (Lit x') else (Lit y)
rename x x'(App t1 t2) =
  (App (rename x x' t1) (rename x x' t2))
rename x x'(Abs (Lit y) t) =
  if x == y
  then error "Bad renaming"
  else (Abs (Lit y) t)
    

-- Id,body,target -> term
sub :: Term -> Term -> Term -> Term
sub (Lit x) s (Lit y) = if x == y then s else (Lit y)
sub (Lit x) s (Abs (Lit y) t) =
  if x == y then (Abs (Lit y) t) -- stop, binder = x
  else
    if not(elem y (freeVars s))
    -- no capture
    then (Abs (Lit y) (sub (Lit x) s t))
    -- capture, rename, try again
    else sub (Lit x) s (Abs (Lit (y++"'")) (rename y (y++"'") t))
sub (Lit x) s (App t1 t2) = (App (sub (Lit x) s t1) (sub (Lit x) s t2))
sub _ _ _ = error "Unmatched sub case"


cbv ::  Term -> Term
-- E-AppAbs 
cbv (App (Abs i1 t1) (Abs i2 t2)) =  sub i1 (Abs i2 t2) t1
-- E-App2
cbv (App (Abs i b) t) = (App (Abs i b) (cbv t))
-- E-App1
cbv (App t1 t2) = (App (cbv t1) t2)
cbv (Abs i t) = (Abs i t)
cbv t = error $ "problem with: " ++ show t

eval :: Term -> Term
eval (Abs i b) = (Abs i b)
eval (Lit x) = (Lit x)
eval t1 = eval $ cbv t1

p = runParser expr
t1 = "(x -> x)(y -> y)(z -> z)"
true = "(x -> (y -> x))"
false = "(x -> (y -> y))"
unit = "(x -> x)"