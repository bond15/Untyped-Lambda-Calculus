module MonadicParser where
import Data.Char
import Control.Monad
import Control.Applicative


data Parser a = Parser{ parse :: String -> [(a,String)]}

runParser :: Parser a -> String -> a
runParser m s =
  case parse m s of
    [(res,[])] -> res
    [(_,rs)] -> error "leftovers"
    _ -> error "error"

item :: Parser Char
item = Parser $ \s ->
  case s of
    [] -> []
    (c:cs) -> [(c,cs)]

zero :: Parser a
zero = Parser $ \s -> []

result :: a -> Parser a
result v = Parser $ \s -> [(v,s)]


bind :: Parser a -> (a -> Parser b) -> Parser b
bind p f = Parser $
  \s -> concatMap 
        (\(a,s') -> parse (f a) s')
        $ parse p s


instance Functor Parser where
  -- fmap :: (a -> b) -> f a -> f b
  fmap f (Parser cs) =
    Parser (\s -> [(f a,b) | (a,b) <- cs s])

instance Applicative Parser where
  -- pure :: a -> f a
  -- <*>  :: f (a -> b) -> f a -> f b
  pure = result
  (Parser cs1) <*> (Parser cs2) =
    Parser (\s ->
              [(f a, s2) | (f, s1) <- cs1 s,
                           (a, s2) <- cs2 s1])

instance Monad Parser where
  return = result
  (>>=) = bind


instance Alternative Parser where
  empty = Parser (\s -> []) 
  p <|> q = Parser ( \s ->  
               case parse p s of
                 [] -> parse q s
                 res -> res)

instance MonadPlus Parser where
  mzero = Parser (\s -> []) 
  p `mplus` q = Parser (\s -> 
                         parse p s ++ parse q s)



sat :: (Char -> Bool) -> Parser Char
sat p = do
  c <- item
  if p c then result c else zero

oneOf :: [Char] -> Parser Char
oneOf s = sat (flip elem s)

chainl :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = (p `chainl1` op) <|> return a

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op = do
  a <- p
  rest a
  where
    rest a = (do
      f <- op
      b <- p
      rest (f a b)) <|> return a
      
char :: Char -> Parser Char
char c = sat (c == )

natural :: Parser Integer
natural =  read <$> some (sat isDigit)

string :: String -> Parser String
string [] = return []
string (c:cs) = do
  char c
  string cs
  return (c:cs)

spaces :: Parser String
spaces = many $ oneOf " \r\n"

token :: Parser a -> Parser a
token p = do
  a <- p
  spaces
  return a

reserved :: String -> Parser String
reserved s = token (string s)

digit :: Parser Char
digit = sat isDigit

number :: Parser Int
number = do
  s <- string "-" <|> return []
  cs <- some digit
  return $ read (s ++ cs)

parens :: Parser a -> Parser a
parens m =  do
  reserved "("
  n <- m
  reserved ")"
  return n
