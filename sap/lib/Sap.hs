{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | This module is intended to be imported as:
--
-- @
-- import Sap ((\\))
-- import qualified Sap
-- @

module Sap
 ( -- * Sum
   Sum
 , SumPrism(_Sum)
 , Run(run)
   -- * Prod
 , Prod
 , prod
 , (\\)
 , ProdLens(_Prod)
 , Pop(pop)
   -- * Both
 , Map(map)
   -- * Misc
 , Member
 , NotMember
 , All
 ) where

import Data.Profunctor (dimap, Choice)
import GHC.Exts (Constraint)
import GHC.TypeLits as GHC
import Prelude hiding (map)

--------------------------------------------------------------------------------

data Sum :: [*] -> * where
  This :: NotMember as a => a -> Sum (a ': as)
  That :: Sum as -> Sum (a ': as)

deriving instance All Eq as => Eq (Sum as)
deriving instance All Show as => Show (Sum as)
deriving instance (All Ord as, All Eq as) => Ord (Sum as)

--------------------------------------------------------------------------------

class (Member as a, Member bs b)
  => SumPrism as bs a b
  | as b -> bs, bs a -> as, as bs -> a b where
  _Sum :: Prism (Sum as) (Sum bs) a b

instance (NotMember as b) => SumPrism (a ': as) (b ': as) a b where
  _Sum = dimap (\(This a) -> a) (fmap This)
  {-# INLINE _Sum #-}

instance {-# OVERLAPPABLE #-}
  (SumPrism as bs a b, NotMember bs a, Member (a ': bs) b)
  => SumPrism (a ': as) (a ': bs) a b where
  _Sum = dimap (\(That as) -> as) (fmap That) . _Sum
  {-# INLINE _Sum #-}

--------------------------------------------------------------------------------

data Prod :: [*] -> * where
  Cons :: NotMember as a => a -> Prod as -> Prod (a ': as)
  Nil :: Prod '[]

prod :: Prod '[]
prod = Nil

(\\) :: NotMember as a => Prod as -> a -> Prod (a ': as)
(\\) = flip Cons
{-# INLINE (\\) #-}
infixl 5 \\

--------------------------------------------------------------------------------

class ProdLens as bs a b
  | as b -> bs, bs a -> as, as bs -> a b where
  _Prod :: Lens (Prod as) (Prod bs) a b

instance NotMember as b => ProdLens (a ': as) (b ': as) a b where
  _Prod f (Cons a as) = fmap (flip Cons as) (f a)
  {-# INLINE _Prod #-}

instance {-# OVERLAPPABLE #-}
  (ProdLens as bs a b, NotMember bs a)
  => ProdLens (a ': as) (a ': bs) a b where
  _Prod f (Cons a as) = fmap (Cons a) (_Prod f as)
  {-# INLINE _Prod #-}

--------------------------------------------------------------------------------

class Pop as bs a
  | as a -> bs, bs a -> as, bs as -> a where
  pop :: Prod as -> (a, Prod bs)

instance Pop (a ': as) as a where
  pop (Cons a as) = (a, as)
  {-# INLINE pop #-}

instance {-# OVERLAPPABLE #-}
  (Pop as bs a, NotMember bs b)
  => Pop (b ': as) (b ': bs) a where
  pop (Cons a as) = fmap (Cons a) (pop as)
  {-# INLINE pop #-}

--------------------------------------------------------------------------------

class Map fs as bs | fs -> as bs, as bs -> fs where
  map :: Prod fs -> Sum as -> Sum bs

instance
  (Map fs as bs, NotMember bs b)
  => Map ((a -> b) ': fs) (a ': as) (b ': bs) where
  map (Cons f _)  (This a)  = This (f a)
  map (Cons _ fs) (That as) = That (map fs as)
  {-# INLINE map #-}

--------------------------------------------------------------------------------

class Run (as :: [*]) a | as -> a where
  run :: Sum as -> a

instance Run as a => Run (a ': as) a where
  run (This a) = a
  run (That as) = run as
  {-# INLINE run #-}

--------------------------------------------------------------------------------

-- | Same as 'Control.Lens.Lens'.
type Lens s t a b
  = forall f. (Functor f) => (a -> f b) -> (s -> f t)

-- | Same as 'Control.Lens.Prism'.
type Prism s t a b
  = forall p f. (Choice p, Applicative f) => p a (f b) -> p s (f t)

--------------------------------------------------------------------------------

type Member (as :: [k]) (a :: k) = Member_ as as a
type family Member_ (as0 :: [k]) (as :: [k]) (a :: k) :: Constraint where
  Member_ as0 (a ': as) a = ()
  Member_ as0 (_ ': as) a = Member_ as0 as a
  Member_ as0 '[] a = GHC.TypeError
    ('GHC.ShowType a 'GHC.:<>:
     'GHC.Text " is not a member of " 'GHC.:<>:
     'GHC.ShowType as0)

type NotMember (as :: [k]) (a :: k) = NotMember_ as as a
type family NotMember_ (as0 :: [k]) (as :: [k]) (a :: k) :: Constraint where
  NotMember_ as0 (a ': _) a = GHC.TypeError
    ('GHC.ShowType a 'GHC.:<>:
     'GHC.Text " is a member of " 'GHC.:<>:
     'GHC.ShowType as0)
  NotMember_ as0 (_ ': as) a = NotMember_ as0 as a
  NotMember_ as0 '[] _ = ()

type family All (c :: k -> Constraint) (as :: [k]) :: Constraint where
  All c (a ': as) = (c a, All c as)
  All c '[] = ()


