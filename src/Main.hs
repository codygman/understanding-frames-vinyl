{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Main where

import Data.Typeable (Proxy(..))
import Control.Applicative
import Data.Functor.Identity
import GHC.TypeLits (Symbol, KnownSymbol, symbolVal)

data Nat = Z | S !Nat

data Rec :: (u -> *) -> [u] -> * where
  RNil :: Rec f '[]
  (::&) :: !(f r) -> !(Rec f rs) -> Rec f (r ': rs)

infixr 7 ::&

type Record = Rec Identity

-- | A column's type includes a textual name and the data type of each
-- element.
newtype (:->) (s::Symbol) a = Col { getCol :: a }
  deriving (Eq,Ord,Num,Monoid,Real,RealFloat,RealFrac,Fractional,Floating)

-- | A partial relation that gives the index of a value in a list.
type family RIndex (r :: k) (rs :: [k]) :: Nat where
  RIndex r (r ': rs) = Z
  RIndex r (s ': rs) = S (RIndex r rs)

-- see: https://github.com/VinylRecords/Vinyl/blob/524a89c1644067c9def969a9565aa5076004a65b/Data/Vinyl/TypeLevel.hs#L21
class i ~ RIndex r rs => RElem (r :: k) (rs :: [k]) (i :: Nat) where
  rlensVinyl
    :: Functor g
    => sing r
    -> (f r -> g (f r))
    -> Rec f rs
    -> g (Rec f rs)

  rgetVinyl
    :: sing r
    -> Rec f rs
    -> f r

-- necessary instance for rgetVinyl (hence rget) to work
instance RElem r (r ': rs) Z where
  rlensVinyl _ f (x ::& xs) = fmap (::& xs) (f x)
  rgetVinyl k = getConst . rlensVinyl k Const

-- TODO see what breaks when this one isn't here to figure out what its for exactly
instance (RIndex r (s ': rs) ~ S i, RElem r rs i) => RElem r (s ': rs) (S i) where
  rlensVinyl p f (x ::& xs) = fmap (x ::&) (rlensVinyl p f xs)
  rgetVinyl k = getConst . rlensVinyl k Const

rlens' :: (i ~ RIndex r rs, RElem r rs i, Functor f, Functor g)
       => sing r
       -> (g r -> f (g r))
       -> Rec g rs
       -> f (Rec g rs)
rlens' = rlensVinyl

-- | Create a lens for accessing a field of a 'Record'.
rlens :: (Functor f, RElem (s :-> a) rs (RIndex (s :-> a) rs))
      => proxy (s :-> a) -> (a -> f a) -> Record rs -> f (Record rs)
rlens k f = rlens' k (fmap Identity . runIdentity . fmap f')
  where f' (Col x) = fmap Col (f x)

-- | A @cons@ function for building 'Record' values.
(&:) :: a -> Record rs -> Record (s :-> a ': rs)
x &: xs = frameCons (Identity x) xs
infixr 5 &:

pattern x :& xs <-  (frameUncons -> (x, xs)) where
  x :& xs = frameCons x xs
pattern Nil = RNil

-- | Used only for a show instance that parenthesizes the value.
newtype Col' s a = Col' (s :-> a)

frameCons :: Functor f => f a -> Rec f rs -> Rec f (s :-> a ': rs)
frameCons = (::&) . fmap Col

frameUncons :: Functor f => Rec f (s :-> r ': rs) -> (f r, Rec f rs)
frameUncons (x ::& xs) = (fmap getCol x, xs)

userId ::
  forall f rs. (Functor f, RElem UserId rs (RIndex UserId rs)) =>
  (Int -> f Int) -> Record rs -> f (Record rs)
userId = rlens (Proxy :: Proxy UserId)

rget :: (forall f. Functor f => (a -> f a) -> Record rs -> f (Record rs))
     -> Record rs -> a
rget l = getConst . l Const

-- now we can write application code
type UserId = "user id" :-> Int
type User = Record [UserId, "age" :-> Int, "gender" :-> String, "occupation" :-> String, "zip code" :-> String]

user :: User
user = 0 &: 25 &: "Male" &: "Programmer" &: "90210" &: Nil

main :: IO ()
main = do
  let uid = rget userId user
  putStrLn $ "user id is: " ++ show uid
