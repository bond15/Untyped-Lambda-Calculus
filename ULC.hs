module ULC where
import MonadicParser
import Data.Char
import Data.IORef
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

data Cmd = Eval Term | Assign String Term deriving Show
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

assign :: Parser (Cmd)
assign = do
  (Lit i) <- iden
  spaces
  reserved "="
  spaces
  e <- inr -- expr
  return (Assign i e)

cmd :: Parser (Cmd)
cmd = assign
--expr
  <|> (do e <- inr; return (Eval e))


execParser :: Parser a -> String -> Maybe a
execParser p s =
  case parse p s of
    [(res,[])] -> Just res
    _ -> Nothing


printCtxt :: IORef [(String,Term)] -> IO ()
printCtxt ctxt = do
  l <- readIORef ctxt
  putStrLn $ show l

addCtxt :: String -> Term -> [(String,Term)] -> [(String,Term)]
addCtxt key val ctxt = ctxt ++ [(key,val)]

clookup x [] = error "empty lookup"
clookup x (y:ys) =
  if x == (fst y)
  then snd y
  else clookup x ys

inCtxt x [] = False
inCtxt x (y:ys)=
  if x == (fst y)
  then True
  else inCtxt x ys
    

findAndReplace x (Lit y) ctxt =
  if x == y && inCtxt x ctxt
  then clookup x ctxt
  else (Lit y)
findAndReplace x (App t1 t2) ctxt =
  (App (findAndReplace x t1 ctxt) (findAndReplace x t2 ctxt))
findAndReplace x (Abs i t) ctxt =
  (Abs i (findAndReplace x t ctxt))

rep' term [] ctxt = term
rep' term (y:ys) ctxt =
  rep' (findAndReplace y term ctxt) ys ctxt
rep term ctxt = rep' term (freeVars term) ctxt

main =do
  ctxt <- newIORef loadLib
  forever $ do
  putStr ">> "
  s <- getLine
  case execParser cmd s of
    Just res ->
      case res of
        Eval e -> do
          c <- readIORef ctxt          
          uprint $ pp $ eval $ rep e c
        Assign i e -> do
          c <- readIORef ctxt
          writeIORef ctxt (addCtxt i (eval $ rep e c) c)
    Nothing -> putStrLn "Parse Error"
  

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





-- stdlib
lib = [
  ("true", "(x -> (y -> x))"),
  ("false","(x -> (y -> y))"),
  ("if"  , "(x -> (y -> (z -> x y z)))"),
  ("and" , "(x -> (y -> x y false))"),
  ("pair", "(f -> (s -> (b -> b f s)))"),
  ("fst" , "(p -> p true)"),
  ("snd" , "(p -> p false)")
  ]


loadLib' = map (\p -> (fst p, runParser expr $ snd p)) lib
loadLib  = map (\p -> (fst p, rep (snd p) loadLib')) loadLib'
--loadLib ctxt = foldr (++) ctxt $ map (\s -> fst (runParser expr s)) lib  

t1 = "(x -> x)(y -> y)(z -> z)"
true = "(x -> (y -> x))"
false = "(x -> (y -> y))"
unit = "(x -> x)"
