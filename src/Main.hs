{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}


module Main where

import GHC.Exts
import Data.Functor.Compose
import Data.Typeable (Proxy(..))
import Data.List (intercalate)
import Data.Monoid
import Control.Applicative
import Data.Functor.Identity
import GHC.TypeLits (Symbol, KnownSymbol, symbolVal)


-- NOTE All of this code is taken from the Vinyl record library and put into this single filie for simplicity of asking questions and giving a reproducible environment to others that can answer my questions.
-- see full versions here: https://github.com/VinylRecords/Vinyl/blob/29d7268fd46c4739e481786f80c6debb07ed8109/Data/Vinyl/Core.hs


data Rec :: (u -> *) -> [u] -> * where
  RNil :: Rec f '[]
  (::&) :: !(f r) -> !(Rec f rs) -> Rec f (r ': rs)

infixr 7 ::&

type family RecAll (f :: u -> *) (rs :: [u]) (c :: * -> Constraint) :: Constraint where
  RecAll f '[] c = ()
  RecAll f (r ': rs) c = (c (f r), RecAll f rs c)

 -- | Wrap up a value with a capability given by its type
data Dict c a where
  Dict
    :: c a
    => a
    -> Dict c a

type f :. g = Compose f g
infixr 9 :.

reifyConstraint
  :: RecAll f rs c
  => proxy c
  -> Rec f rs
  -> Rec (Dict c :. f) rs
reifyConstraint prx rec =
  case rec of
    RNil -> RNil
    (x ::& xs) -> Compose (Dict x) ::& reifyConstraint prx xs

rmap
  :: (forall x. f x -> g x)
  -> Rec f rs
  -> Rec g rs
rmap _ RNil = RNil
rmap η (x ::& xs) = η x ::& (η `rmap` xs)


newtype Lift (op :: l -> l' -> *) (f :: k -> l) (g :: k -> l') (x :: k)
  = Lift { getLift :: op (f x) (g x) }

rapply
  :: Rec (Lift (->) f g) rs
  -> Rec f rs
  -> Rec g rs
rapply RNil RNil = RNil
rapply (f ::& fs) (x ::& xs) = getLift f x ::& (fs `rapply` xs)


type Record = Rec Identity

-- | A column's type includes a textual name and the data type of each
-- element.
newtype (:->) (s::Symbol) a = Col { getCol :: a }
  deriving (Eq,Ord,Num,Monoid,Real,RealFloat,RealFrac,Fractional,Floating)


data Nat = Z | S !Nat

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

  rputVinyl
    :: f r
    -> Rec f rs
    -> Rec f rs

rappend
  :: Rec f as
  -> Rec f bs
  -> Rec f (as ++ bs)
rappend RNil ys = ys
rappend (x ::& xs) ys = x ::& (xs `rappend` ys)

frameCons :: Functor f => f a -> Rec f rs -> Rec f (s :-> a ': rs)
frameCons = (::&) . fmap Col

-- | A @cons@ function for building 'Record' values.
(&:) :: a -> Record rs -> Record (s :-> a ': rs)
x &: xs = frameCons (Identity x) xs
infixr 5 &:

-- | Append for type-level lists.
type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)

frameSnoc :: Rec f rs -> f r -> Rec f (rs ++ '[r])
frameSnoc r x = rappend r (x ::& RNil)

frameUncons :: Functor f => Rec f (s :-> r ': rs) -> (f r, Rec f rs)
frameUncons (x ::& xs) = (fmap getCol x, xs)

-- pattern x :& xs <- (frameUncons -> (x, xs))
pattern x :& xs <-  (frameUncons -> (x, xs)) where
  x :& xs = frameCons x xs

pattern Nil = RNil

type UserId = "user id" :-> Int

type User = Record [UserId, "age" :-> Int, "gender" :-> String, "occupation" :-> String, "zip code" :-> String]

user :: User
user = 0 &: 25 &: "Male" &: "Programmer" &: "90210" &: Nil

-- TODO make the show instance for user work
instance forall s a. (KnownSymbol s, Show a) => Show (s :-> a) where
  show (Col x) = symbolVal (Proxy::Proxy s)++" :-> "++Prelude.show x

-- | Used only for a show instance that parenthesizes the value.
newtype Col' s a = Col' (s :-> a)

-- | Helper for making a 'Col''
col' :: a -> Col' s a
col' = Col' . Col

instance (KnownSymbol s, Show a) => Show (Col' s a) where
show (Col' c) = "(" ++ Prelude.show c ++ ")"

class Functor f => ShowRec f rs where
  showRec' :: Rec f rs -> [String]

instance Functor f => ShowRec f '[] where
  showRec' _ = []

instance forall s f a rs. (KnownSymbol s, Show (f (Col' s a)), ShowRec f rs)
  => ShowRec f (s :-> a ': rs) where
  showRec' (x :& xs) = Prelude.show (col' <$> x :: f (Col' s a)) : showRec' xs
  showRec' _ = error "GHC coverage error"

-- | Pretty printing of 'Rec' values.
showRec :: ShowRec f rs => Rec f rs -> String
showRec r = "{" ++ intercalate ", " (showRec' r) ++ "}"

recordToList
  :: Rec (Const a) rs
  -> [a]
recordToList RNil = []
recordToList (x ::& xs) = getConst x : recordToList xs

instance RecAll f rs Show => Show (Rec f rs) where
  show xs =
    (\str -> "{" <> str <> "}")
      . intercalate ", "
      . recordToList
      . rmap (\(Compose (Dict x)) -> Const $ Prelude.show x)
      $ reifyConstraint (Proxy :: Proxy Show) xs


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

userId ::
  forall f rs. (Functor f, RElem UserId rs (RIndex UserId rs)) =>
  (Int -> f Int) -> Record rs -> f (Record rs)
userId = rlens (Proxy :: Proxy UserId)

rget :: (forall f. Functor f => (a -> f a) -> Record rs -> f (Record rs))
     -> Record rs -> a
rget l = getConst . l Const



-- TODO evidently we don't have enough machinery yet to deduce that there is indeed a UserId c olumn in the given record... WHY?
-- λ> rget userId user

-- <interactive>:629:6-11: error:
--     * Could not deduce (RElem
--                           UserId
--                           '[UserId, "age" :-> Int, "gender" :-> String,
--                             "occupation" :-> String, "zip code" :-> String]
--                           'Z)
--         arising from a use of `userId'
--       from the context: Functor f
--         bound by a type expected by the context:
--                    Functor f =>
--                    (Int -> f Int)
--                    -> Record
--                         '[UserId, "age" :-> Int, "gender" :-> String,
--                           "occupation" :-> String, "zip code" :-> String]
--                    -> f (Record
--                            '[UserId, "age" :-> Int, "gender" :-> String,
--                              "occupation" :-> String, "zip code" :-> String])
--         at <interactive>:629:1-16
--     * In the first argument of `rget', namely `userId'
--       In the expression: rget userId user
--       In an equation for `it': it = rget userId user



-- Questions:
-- Why is the forall x necessary? It seems it's just to tell GHC that the provided function must have the same input/output type? This means that annotating or being explicit about type constraints isn't necessary?

-- What is the reason that reifyConstraint is necessary? Is it because constraints are stored in a type level list and then only made real or "reified" when this function is called?

-- 

main :: IO ()
main = do
  putStrLn "hello world"
