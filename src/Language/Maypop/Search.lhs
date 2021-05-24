This module is only for testing. Here, we try to implement
a basic logic programming language (which would be used
for something like type class search) using `UnifyT`.

> {-# LANGUAGE DeriveFoldable #-}
> {-# LANGUAGE DeriveFunctor #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> module Language.Maypop.Search where
> import Language.Maypop.Unification
> import Language.Maypop.InfiniteList
> import Control.Monad
> import Control.Monad.Logic
> import Control.Monad.Reader
> import Control.Monad.State
> import Control.Applicative
> import Data.Foldable
> import Data.List
> import Data.Maybe
>
> data Term k
>     = App String [Term k] | Lit Int | Ref k
>     deriving (Eq, Foldable, Functor, Show)
>
> type Rule = ([Term String], Term String)
>
> instantiate :: MonadUnify k (Term k) m => Rule -> m ([Term k], Term k)
> instantiate (pts, ct) = do
>     varMap <- mapM (\x -> (,) x <$> fresh) $ nub $ concatMap toList (ct:pts)
>     let resVar = fromJust . flip lookup varMap
>     let ts = map (fmap resVar) pts
>     let c = fmap resVar ct
>     return (ts, c)
>
> instance (Eq k, Infinite k) => Unifiable k (Term k) where
>     unify (App s1 xs1) (App s2 xs2) | s1 == s2 && length xs1 == length xs2 = App s2 <$> zipWithM unify xs1 xs2     
>     unify (Lit i1) (Lit i2) | i1 == i2 = return $ Lit i1
>     unify (Ref k1) (Ref k2) = merge k1 k2 >> return (Ref k1)
>     unify (Ref k1) t = bind k1 t
>     unify t (Ref k2) = bind k2 t
>     unify _ _ = mzero
>     occurs = elem
>     substitute k v = subst
>         where
>             subst (App s ts) = App s $ map subst ts
>             subst (Ref k') | k == k' = v
>             subst t = t
>
> runBacktrackEval :: (MonadPlus m, Unifiable k a, Infinite k) => UnifyT k a (LogicT m) a -> m a
> runBacktrackEval m = runLogicT (runUnifyT m) (const . return) mzero
>
> rule :: (MonadReader [Rule] m, MonadUnify k (Term k) m) => Term k -> Rule -> m (Term k)
> rule t r = do
>    (pts, c) <- instantiate r
>    rt <- unify t c
>    mapM satisfy pts
>    return rt
>
> satisfy :: (MonadReader [Rule] m, MonadUnify k (Term k) m) => Term k -> m (Term k)
> satisfy t = ask >>= asum . map (rule t)
>
> runSatisfy :: (Infinite k, Ord k) => [Rule] -> Term k -> Maybe (Term k)
> runSatisfy rs t = runReaderT (runBacktrackEval $ satisfy t) rs
