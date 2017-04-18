{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
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
-- import Sums ((\\))
-- import qualified Sums
-- @

module Sums
 ( -- * Sum types
   Sum(This, That)
 , Put
 , put
 , get
 , _Sum
   -- * Cases analysis
 , match
--  , Unmatch
--  , unmatch
 , Cases
 , cases
 , foo
 , (\\)
 , absurd
 , Unique
   -- ** Overrides
 , Override
 , override
 ) where

import Data.Profunctor (dimap, Choice(right'))
import GHC.Exts (Constraint)
import GHC.TypeLits as GHC
import Prelude
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------

-- | @'Cases' as r@ encodes the elimination of all the elements of @as@ as @r@.
--
-- For example, if you wanted to be able to convert both an 'Char' and a 'Bool'
-- to 'String', then @'Cases' '[ 'Char', 'Bool'] 'String'@ encodes that idea.
-- That is, @'Cases' '[ 'Char', 'Bool'] 'String'@ is isomorphic to @'Either'
-- 'Char' 'Bool' -> 'String'@.
--
-- Let's compare how to implement these two. First, let's do it for 'Either' by
-- explicitely pattern matching on all possible constructors combinations:
--
-- @
-- showEither1 :: 'Either' ['Int'] 'Bool' -> 'String'
-- showEither1 x = case x of
--    'Left' [] -> "empty"
--    'Left' (_:_) -> "not empty"
--    'Right' 'True' -> "hello"
--    'Right' 'False' -> "bye"
-- @
--
-- Alternatively, we can pattern match on the outermost constructors 'Left' and
-- 'Right', and only then proceed to pattern matching on the inner constructors
-- of 'Bool' and '[]':
--
-- @
-- showEither2 :: 'Either' ['Int'] 'Bool' -> 'String'
-- showEither2 x = case x of
--    'Left' y -> case y
--       [] -> "empty"
--       (_:_) -> "not empty"
--    'Right' z -> case z of
--       'True' -> "hello"
--       'False' -> "bye"
-- @
--
-- In @showEither2@, even though we are being a bit more verbose, we are in fact
-- enabling the pattern match on the inner '[]' or 'Bool' to exist separately
-- from the pattern match on the outer 'Either', which is a good thing if we
-- would like to reuse this case analysis on '[]' or 'Bool' in different
-- scenarios:
--
-- @
-- showList1 :: ['Int'] -> 'String'
-- showList1 x = case x of
--    [] -> "empty"
--    (_:_) -> "not empty"
--
-- showBool1 :: 'Bool' -> 'String'
-- showBool1 x = case x of
--    'True' -> "hello"
--    'False' -> "bye"
--
-- showEither3 :: 'Either' ['Int'] 'Bool' -> 'String'
-- showEither3 x = case x of
--    'Left' y -> showList1 y
--    'Right' z -> showBool1 z
-- @
--
-- In fact, this pattern is so common and useful that Putkell provides the
-- function 'either' that does exactly this:
--
-- @
-- showEither4 :: 'Either' ['Int'] 'Bool' -> 'String'
-- showEither4 x = 'either' showList1 showBool1 x
-- @
--
-- 'Cases', by requiring you to use a "nested case analysis" approach like the
-- one seen here, allows you to combine one or more functions like `showList1`
-- and `showBool1` into a function like @showEither4@. However, whilst 'Either'
-- is limited to two diferent outer constructors, 'Cases' suports an unlimited
-- number of constructors. Let's rewrite our case analysis using 'Cases':
--
-- @
-- showCases1 :: 'Cases' '[['Int'], 'Bool'] 'String'
-- showCases1 = 'cases' \\ showList1 \\ showBool1
-- @
--
-- @'Cases' '[['Int'], 'Bool'] 'String'@ is not a function, but it can be easily
-- be turned into one using 'match', which takes a term of type @'Cases' xs r@
-- and returns a function @'Sum' xs -> r@, where 'Sum xs' is a sum type like
-- 'Either', but with an unlimited number of constructors:
--
-- @
-- showSum1 :: 'Sum' '[['Int'], 'Bool'] -> 'String'
-- showSum1 = 'match' showCases1
-- @
--
-- Most of the times, however, you'd

data Cases :: [*] -> * -> * where
  Case :: Unique as a => Cases as r -> (a -> r) -> Cases (a ': as) r
  Absurd :: Cases '[] r
  -- Match :: (Sum (a ': as) -> r) -> Cases (a ': as) r

instance Functor (Cases as) where
  {-# INLINE fmap #-}
  fmap f = \case
    Case cs g -> Case (fmap f cs) (f . g)
    Absurd -> Absurd
    -- Match g -> Match (f . g)

--------------------------------------------------------------------------------

data Sum :: [*] -> * where
  This :: Unique as a => a -> Sum (a ': as)
  That :: Sum as -> Sum (a ': as)

deriving instance All Eq as => Eq (Sum as)
deriving instance All Show as => Show (Sum as)
deriving instance (All Ord as, All Eq as) => Ord (Sum as)

--------------------------------------------------------------------------------

type Get = Get'
class Get' (as :: [*]) (a :: *) where
  get' :: Sum as -> Maybe a
instance Get' (a ': as) a where
  get' (This a) = Just a
  get' (That _) = Nothing
  {-# INLINE get' #-}
instance {-# OVERLAPPABLE #-} Get' as a => Get' (b ': as) a where
  get' (That as) = get' as
  get' (This _)  = Nothing
  {-# INLINE get' #-}

-- We don't want to export the 'Get'' class, just its name, so we give other
-- name to 'get'' here.
get :: Get as a => Sum as -> Maybe a
get = get'
{-# INLINE get #-}

--------------------------------------------------------------------------------

type Put as a = Put' as a
class Put' (as :: [*]) (a :: *) where
  put' :: a -> Sum as
instance Unique as a => Put' (a ': as) a where
  put' a = This a
  {-# INLINE put' #-}
instance {-# OVERLAPPABLE #-} Put' as a => Put' (b ': as) a where
  put' a = That (put' a)
  {-# INLINE put' #-}

-- We don't want to export the 'Put'' class, just its name, so we give other
-- name to 'put'' here.
put :: Put as a => a -> Sum as
put = put'
{-# INLINE put #-}

--------------------------------------------------------------------------------

_Sum :: (Get as a, Put bs b, Exclude as a ~ Exclude bs a)
     => Prism (Sum as) (Sum bs) a b
_Sum = prism put' $ \s -> case get' s of
   Just a  -> Right a
   Nothing -> Left (unsafeCoerce s)   -- This is in fact safe, as witnessed by
                                      -- the equality on `Exclude`s.
{-# INLINE _Sum #-}

--------------------------------------------------------------------------------

cases :: Cases '[] r
cases = Absurd
{-# INLINE cases #-}

infixl 5 \\
(\\) :: Unique as a => Cases as r -> (a -> r) -> Cases (a ': as) r
(\\) = Case
{-# INLINE (\\) #-}

-- type Unmatch = Unmatch'
-- class Unmatch' (as :: [*]) where
--   unmatch' :: (Sum as -> r) -> Cases as r
-- instance Unmatch' '[] where
--   unmatch' _ = Absurd
--   {-# INLINE unmatch' #-}
-- instance Unmatch' (a ': as) where
--   unmatch' f = Match f
--   {-# INLINE unmatch' #-}
--
-- -- | Build 'Cases' out of an 'Sum' elimination function.
-- --
-- -- @
-- -- 'match' . 'unmatch' = id
-- -- @
-- --
-- -- @
-- -- 'unmatch' . 'match' = id
-- -- @
-- unmatch :: Unmatch as => (Sum as -> r) -> Cases as r
-- unmatch = unmatch'
-- {-# INLINE unmatch #-}

--------------------------------------------------------------------------------

absurd :: Sum '[] -> r
absurd = \case{}
{-# INLINE absurd #-}

-- | Eliminate 'Sum' through 'Cases'.
--
-- @
-- 'match' . 'unmatch' = id
-- @
--
-- @
-- 'unmatch' . 'match' = id
-- @
match :: Cases as r -> Sum as -> r
match (Case cs f) = \case
  This a  -> f a
  That as -> match cs as
match Absurd = absurd
-- match (Match f) = f
{-# INLINE match #-}
--------------------------------------------------------------------------------

type Override = Override'
class Override' (as :: [*]) (a :: *) where
  override' :: (a -> r) -> Cases as r -> Cases as r
instance Override' '[] a where
  override' _ Absurd = Absurd
  {-# INLINE override' #-}
instance Unique as a => Override' (a ': as) a where
  override' f (Case cs _) = Case cs f
  -- override' f (Match g) = Match (\s -> maybe (g s) f (get s))
  {-# INLINE override' #-}
instance {-# OVERLAPPABLE #-} (Put as a, Override' as a) => Override' (b ': as) a where
  override' f (Case cs g) = Case (override' f cs) g
  -- override' f (Match g) = Match (\s -> maybe (g s) f (get s))
  {-# INLINE override' #-}

-- | @'override' (f :: a -> r) x@ overrides with @f@ the case analysis for @a@
-- in @x@.

-- We don't want to export the 'Override' class, just its name, so we give other
-- name to 'override'' here.
override :: Override as a => (a -> r) -> Cases as r -> Cases as r
override = override'
{-# INLINE override #-}

--------------------------------------------------------------------------------

-- | Same as 'Control.Lens.Prism'.
type Prism s t a b
  = forall p f. (Choice p, Applicative f) => p a (f b) -> p s (f t)

-- | Same as 'Control.Lens.prism'.
prism :: (b -> t) -> (s -> Either t a) -> Prism s t a b
prism bt seta pafb = dimap seta (either pure (fmap bt)) (right' pafb)
{-# INLINE prism #-}

--------------------------------------------------------------------------------

type Unique = Unique'
class Unique'' xs xs x => Unique' xs x
instance Unique'' xs xs x => Unique' xs x
type family Unique'' (xs0 :: [k]) (xs :: [k]) (x :: k) :: Constraint where
  Unique'' xs0 (x ': xs) x =
    GHC.TypeError
      ('GHC.ShowType x 'GHC.:<>: 'GHC.Text " is already a member of "
       'GHC.:<>: 'GHC.ShowType xs0)
  Unique'' xs0 (_ ': xs) x = Unique'' xs0 xs x
  Unique'' xs0 '[] x = ()

type family Exclude (xs :: [k]) (x :: k) :: [k] where
  Exclude (x ': xs) x = Exclude xs x
  Exclude '[] x = '[]

class Member (xs :: [k]) (x :: k)
instance Member (x ': xs) x
instance {-# OVERLAPPABLE #-} Member xs x => Member (y ': xs) x

type family All (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  All c (x ': xs) = (c x, All c xs)
  All c '[] = ()

infixr 5 ++
-- | Type-level list conccatenation.
type family (++) (xs :: [k]) (ys :: [k]) :: [k] where
  '[] ++ ys = ys
  (x ': xs) ++ ys = x ': xs ++ ys

-- data Dict :: Constraint -> * where
  -- Dict :: a => Dict a

