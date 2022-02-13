{-# LANGUAGE InstanceSigs #-}
import Text.Read

type Symb = String

infixl 2 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving Eq

freeVars :: Expr -> [Symb]
freeVars (Var x) = [x]
freeVars (a :@ b) = (freeVars a) ++ (freeVars b)
freeVars (Lam x y) = concat (map (\z -> if (z == x) then [] else [z]) (freeVars y))

maxByLen ar = foldr (\elem suf -> if (length elem) > (length suf) then elem else suf) "" ar

newVar lst | length lst == 0 = "x"
           | otherwise = (maxByLen lst) ++ ("'")

isContain [] x = False
isContain (a:ab) x = (x == a) || (isContain ab x)

subst :: Symb -> Expr -> Expr -> Expr
subst v n t@(Var a) | (a == v)  = n
                    | otherwise = t
subst v n (f1 :@ f2) = (subst v n f1) :@ (subst v n f2)
subst v n (Lam var ex) | (var == v) = (Lam var ex)
                       | (isContain (freeVars n) var) == False = (Lam var (subst v n ex))
                       | otherwise = (Lam new_var (subst v n (subst var (Var new_var) ex)))
                                        where new_var = newVar ((freeVars n) ++ (freeVars ex))

infix 1 `alphaEq`

alphaEq :: Expr -> Expr -> Bool
alphaEq (Var x) (Var y) = x == y
alphaEq (e1 :@ e2) (g1 :@ g2) = (e1 `alphaEq` g1) && (e2 `alphaEq` g2)
alphaEq (Lam var1 ex1) (Lam var2 ex2) | (var1 == var2) = (ex1 `alphaEq` ex2)
                                      | otherwise = ((isContain (freeVars ex2) var1) == False)
                                                && (ex1 `alphaEq` (subst var2 (Var var1) ex2))
alphaEq _ _ = False

p1 = (Lam "x" $ Lam "y" $ (Var "x") :@ (Var "y"))
p2 = (Lam "a" $ Lam "x" $ (Var "a") :@ (Var "x"))

p3 = Lam "x'" (Var "x" :@ Var "x'")
p4 = Lam "y" $ (Var "x") :@ (Var "y")

isJust (Just t) = True
isJust _ = False
takeValueFromJust (Just t) = t

reduceOnce :: Expr -> Maybe Expr
reduceOnce ((Lam x y) :@ exp2) = Just (subst x exp2 y)
reduceOnce (Var x) = Nothing
reduceOnce (Lam var expr) = if (isJust res) then Just (Lam var (takeValueFromJust res)) else Nothing
                where res = reduceOnce expr
reduceOnce (a :@ b) = if (isJust res1) then Just ((takeValueFromJust res1) :@ b)
                      else if (isJust res2) then Just(a :@ (takeValueFromJust res2))
                      else Nothing
                        where res1 = reduceOnce a
                              res2 = reduceOnce b

nf :: Expr -> Expr
nf x = if ((isJust res) == False) then x else nf (takeValueFromJust res)
    where res = reduceOnce x

-- parse functions
getWords [] = []
getWords c = (fst res) : (getWords (snd res))
    where res = head $ lex c

helpPrefPsp 1 (")" : xs) = ([], xs)
helpPrefPsp bal ("(" : xs) = ("(" : (fst res), snd res)
            where res = helpPrefPsp (bal + 1) xs
helpPrefPsp bal (")" : xs) = (")" : (fst res), snd res)
            where res = helpPrefPsp (bal - 1) xs
helpPrefPsp bal (x   : xs) = ( x  : (fst res), snd res)
            where res = helpPrefPsp bal xs

getPspPref (x:xs) = helpPrefPsp 1 xs

getLast (x:[]) = x
getLast (x:xs) = getLast xs

withoutLast (x:[]) = []
withoutLast (x:xs) = (x:(withoutLast xs))

splitFirstBracket ("(":xs) = ([], "(":xs)
splitFirstBracket (a:[]) = ([], [a])
splitFirstBracket (x:xs) = (x : (fst res), snd res)
            where res = splitFirstBracket xs
-------------------------------------
-------------------------------------

help_reader mas | (length mas) == 1    = (Var (head mas))
                | (head mas)   == "\\" = if ((mas !! 2) == "->") then
                                                                    Lam (mas !! 1) $ help_reader (drop 3 mas)
                                         else Lam (mas !! 1) $ (help_reader $ "\\" : (drop 2 mas))
                | (head mas)   /= "("  =  (help_reader fp) :@ (help_reader sp)
                | otherwise            = if (length (snd res) == 0)
                                         then help_reader (fst (res))
                                         else help_reader (fst (res)) :@ help_reader (snd (res))
                                            where res = getPspPref mas
                                                  fp = fst (splitFirstBracket mas)
                                                  sp = snd (splitFirstBracket mas)


readExpr mas = help_reader $ getWords mas

instance Read Expr where
    readsPrec :: Int -> String -> [(Expr,String)]
    readsPrec _ str = [(readExpr str, "")]

infix 1 `betaEq`

betaEq :: Expr -> Expr -> Bool
betaEq x y = (nf x) `alphaEq` (nf y)

instance Show Expr where
    show (Var y) = y
    show (Lam x y) = "\\" ++ x ++ " -> " ++ (show y)
    show ((Var x) :@ (Var y)) = x ++ " " ++ y
    show (a :@ (Var t)) = "(" ++ (show a) ++ ") " ++ t
    show ((Var t) :@ a) = t ++ " (" ++ (show a) ++ ")"
    show (a :@ b) = "(" ++ (show a) ++ ") (" ++ (show b) ++ ")"