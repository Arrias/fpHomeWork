{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
--import Data.Maybe (fromMaybe)
--import Data.Monoid (Sum(..),Product(..))
--import Control.Monad.Trans.Writer(  writer,  execWriter, runWriter, censor, listen, listens, tell, Writer )
--import Control.Monad.Trans.Reader( runReader, ask, asks, local, reader, Reader )
--import Control.Monad.Trans.State ( evalState, modify, execState, get, put, State, state, runState )
-- import Control.Monad.Except
-- import Data.Maybe
-- import Control.Applicative
-- import Control.Monad.Trans.Maybe
-- import Control.Monad.Trans.Except
-- import Control.Monad.IO.Class (liftIO)
-- import Data.Foldable (msum)
-- import Data.Char (isNumber, isPunctuation)

import Control.Monad.Fail
import Control.Applicative
import Control.Monad.State
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Identity (Identity(..))
import Control.Monad.Reader
import Control.Monad.Except
import Data.Maybe
import Data.List (union,group, sort)

infixl 4 :@
infixr 3 :->

type Symb = String

-- Терм
data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
  deriving (Eq,Show)

-- Тип
data Type = TVar Symb
          | Type :-> Type
  deriving (Eq,Show)

-- Контекст
newtype Env = Env [(Symb,Type)]
  deriving (Eq,Show)

-- Подстановка
newtype SubsTy = SubsTy [(Symb, Type)]
  deriving (Eq,Show)

remove_dups :: (Ord a, Eq a) => [a] -> [a]
remove_dups xs = remove $ sort xs
  where
    remove []  = []
    remove [x] = [x]
    remove (x1:x2:xs)
      | x1 == x2  = remove (x1:xs)
      | otherwise = x1 : remove (x2:xs)

freeVars :: Expr -> [Symb]
freeVars (Var x) = [x]
freeVars (a :@ b) = remove_dups ((freeVars a) ++ (freeVars b))
freeVars (Lam x y) = concat (map (\z -> if (z == x) then [] else [z]) (freeVars y))

freeTVars :: Type -> [Symb]
freeTVars (TVar a) = [a]
freeTVars (a :-> b) = remove_dups (freeTVars a ++ freeTVars b)

extendEnv :: Env -> Symb -> Type -> Env
extendEnv (Env xs) s t = Env $ (s, t) : xs

freeTVarsEnv :: Env -> [Symb]
freeTVarsEnv (Env ((s, t) : xs)) = remove_dups (freeTVars t ++ freeTVarsEnv (Env xs))
freeTVarsEnv (Env []) = []


appEnv :: MonadError String m => Env -> Symb -> m Type
appEnv (Env []) v = throwError $ "There is no variable \"" ++ v ++ "\" in the enviroment."
appEnv (Env ((t, x) : xs)) v | (v == t) = return x
                             | otherwise = appEnv (Env xs) v

appSubsTy :: SubsTy -> Type -> Type
appSubsTy v (a :-> b) = (appSubsTy v a) :-> (appSubsTy v b)
appSubsTy (SubsTy lst) ws@(TVar x) = case p of
                                          Just p -> p
                                          Nothing -> ws
                                      where p = lookup x lst

appSubsEnv :: SubsTy -> Env -> Env
appSubsEnv v a@(Env []) = a
appSubsEnv v (Env ((s, t) : xs)) = extendEnv (appSubsEnv v (Env xs)) s (appSubsTy v t)

getValue :: SubsTy -> Symb -> Maybe Type
getValue (SubsTy []) a = Nothing
getValue (SubsTy ((s, t) : xs)) a | a == s = Just t
                                  | otherwise = getValue (SubsTy xs) a

addToSubs (t, s) (SubsTy v) = SubsTy ((t,s):v)

genComposeSubs :: [Symb] -> SubsTy -> SubsTy -> SubsTy
genComposeSubs [] _ _ = SubsTy []
genComposeSubs (x:xs) v1 v2 = let res_it = case p of
                                                Just tp -> appSubsTy v1 tp
                                                Nothing -> fromJust $ getValue v1 x
                                            where p = getValue v2 x in (addToSubs (x, res_it) (genComposeSubs xs v1 v2))

composeSubsTy :: SubsTy -> SubsTy -> SubsTy
composeSubsTy v1@(SubsTy a) v2@(SubsTy b) = let lets = remove_dups $ (map fst a) ++ (map fst b)
                                                    in genComposeSubs lets v1 v2


instance Semigroup SubsTy where
  a <> b = composeSubsTy a b

instance Monoid SubsTy where
  mempty = SubsTy []

unify :: MonadError String m => Type -> Type -> m SubsTy
unify (TVar x) (TVar y) | x == y = return $ SubsTy []
                        | otherwise = return $ SubsTy [(x, TVar y)]
unify m@(TVar x) b | elem x (freeTVars b) = throwError $ "Can't unify " ++ "(" ++ (show m) ++ ") with (" ++ (show b) ++ ")!"
                 | otherwise = return $ SubsTy [(x, b)]
unify v m@(TVar x) = unify m v
unify (a :-> b) (c :-> d) = do
                              (SubsTy v) <- unify b d
                              (SubsTy c) <- unify (appSubsTy (SubsTy v) a) (appSubsTy (SubsTy v) c)
                              return $ (SubsTy c) `mappend` (SubsTy v)

maxByLen ar = foldr (\elem suf -> if (length elem) > (length suf) then elem else suf) "" ar

newVar lst | length lst == 0 = "x"
           | otherwise = (maxByLen lst) ++ ("'")


gen_equations :: MonadError String m => [Symb] -> Env -> Expr -> Type -> m [(Type,Type)]

gen_equations _ env (Var t) c = do
                                  x <- appEnv env t
                                  return [(x, c)]
gen_equations busy env (ex1 :@ ex2) c = do
                                        let new_var = newVar busy
                                        left <- gen_equations (map ((++) "_left") (new_var : busy)) env ex1 (TVar new_var :-> c)
                                        right <- gen_equations (map ((++) "_right") (new_var : busy)) env ex2 (TVar new_var)
                                        return $ union left right
gen_equations busy env (Lam b ex2) c = do
                                        let alpha = newVar busy
                                        let beta = newVar (alpha : busy)
                                        let new_busy = [alpha, beta] ++ busy
                                        left <- gen_equations (map ((++) "_left") new_busy) (extendEnv env b (TVar alpha)) ex2 (TVar beta)
                                        return $ union left [((TVar alpha) :-> (TVar beta), c)]

equations :: MonadError String m => Env -> Expr -> Type -> m [(Type,Type)]
equations a b c = gen_equations (freeTVars c) a b c

term = Lam "y" $ Var "x"
env = Env [("x", TVar "a" :-> TVar "b")]

build_ar (x:[]) = x
build_ar (x:xs) = x :-> (build_ar xs)

freenames = [[i] ++ [j] ++ [k] | i <- ['a'..'z'], j <- ['a'..'z'], k <- ['a'..'z']]

principlePair :: MonadError String m => Expr -> m (Env,Type)
principlePair trm = do
                      let freeVariables = freeVars trm
                      let freeVariablesNames = take (length freeVariables) freenames
                      let forContextBuild = zip freeVariables (map (TVar) freeVariablesNames)
                      let context = foldr (\(e1, e2) suf -> extendEnv suf e1 e2) (Env []) forContextBuild
                      let alpha0 = newVar freeVariablesNames
                      let busy = alpha0 : freeVariablesNames
                      eqs <- gen_equations busy context trm (TVar alpha0)
                      let left_eq = build_ar (map fst eqs)
                      let right_eq = build_ar (map snd eqs)
                      subs <- unify left_eq right_eq
                      return (appSubsEnv subs context, appSubsTy subs (TVar alpha0))


