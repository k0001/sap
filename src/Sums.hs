{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
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
 , absurd
 , put
 , get
 , _Sum
   -- * Cases analysis
 , match
--  , Unmatch
--  , unmatch
 , Cases
 , singleCase
 , (\\)
 , override
   -- ** Misc
 , Get
 , Put
 , Unique
 , Override
 , MkCases
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
-- showCases1 = showList1 \\\\ showBool1
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
  Case :: Unique as a => (a -> r) -> Cases as r -> Cases (a ': as) r
  Absurd :: Cases '[] r

instance Functor (Cases as) where
  {-# INLINE fmap #-}
  fmap f = \case
    Case g cs -> Case (f . g) (fmap f cs)
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

type Put = Put'
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

_Sum :: (Get as a, Put bs b, Exclude as a ~ Exclude bs b)
     => Prism (Sum as) (Sum bs) a b
_Sum = prism put' $ \s -> case get' s of
   Just a  -> Right a
   Nothing -> Left (unsafeCoerce s)   -- This is in fact safe, as witnessed by
                                      -- the equality on `Exclude`s.
{-# INLINE _Sum #-}

--------------------------------------------------------------------------------

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

class MkCases' a x as r | as a r -> x, as x r -> a, a x -> as, x -> r where
  mkCases :: (a -> r) -> x -> Cases as r
instance Unique '[b] a => MkCases' a (b -> r) '[a, b] r where
  mkCases fa fb = Case fa (Case fb Absurd)
  {-# INLINE mkCases #-}
instance Unique (a1 ': a2 ': as) a
  => MkCases' a (Cases (a1 ': a2 ': as) r) (a ': a1 ': a2 ': as) r where
  mkCases fa cas = Case fa cas
  {-# INLINE mkCases #-}

type MkCases = MkCases'

infixr 5 \\
-- |
-- @
-- (\\\\) :: (a -> r) -> 'Cases' as -> 'Cases' (a ': as) r
-- (\\\\) :: (a -> r) -> (b -> r) -> 'Cases' '[a, b]   r
-- @
--
-- (\\\\) is intended to be used as an infix operator combining multiple @forall
-- x. x -> r@ functions into a single @'Cases' xs r@.
--
-- Note that in all of the following examples, the final 'Cases' type is
-- actually inferred by the compiler. We only give the explicit type signature
-- as an example.
--
-- @
-- (\\case True -> "a"
--        False -> "b" ) \\\\
-- (\\case () -> "c")
--     :: 'Cases' '[ 'Bool', ()] 'String'
-- @
--
-- Adding one more case:
--
-- @
-- (\\case True -> "a"
--        False -> "b" ) \\\\
-- (\\case () -> "c" ) \\\\
-- (\\case n -> show (n :: 'Int'))
--     :: 'Cases' '[ 'Bool', (), 'Int'] 'String'
-- @
--
-- Notice that we can't have 'Cases' listing the same type twice. For example,
-- the following does not compile. Instead, you get an error saying @() already is a
-- member of '[()]@.
--
--
-- @
-- (\\case () -> "c" ) \\\\
-- (\\case () -> "d" )
--     :: 'Cases' '[ (), ()] 'String'           -- Does not compile
-- @
--
-- We use and recommend the @\\case@ syntax from GHC's @LambdaCase@ extension
-- because it improves the pattern matching, as exemplified above, but it is not
-- necessary.
--
-- We can leave some of the cases polymorphic as well. However, in that case,
-- we'll have to give an explicit type signature adding the necessary
-- constraints, and we'll also need to give an explicit type to the 'Sum' we
-- will eventually 'match' against.
--
-- @
-- 'show' \\\\ 'const' :: ('Show' a, 'Unique' '[ 'String'] a) => 'Cases' '[a, 'String'] 'String'
-- @
(\\) :: MkCases a x as r => (a -> r) -> x -> Cases as r
(\\) fa x = mkCases fa x
{-# INLINE (\\) #-}

singleCase :: (a -> r) -> Cases '[a] r
singleCase fa = Case fa Absurd
{-# INLINE singleCase #-}

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
match (Case f cs) = \case
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
  override' f (Case _ cs) = Case f cs
  -- override' f (Match g) = Match (\s -> maybe (g s) f (get s))
  {-# INLINE override' #-}
instance {-# OVERLAPPABLE #-} (Put as a, Override' as a) => Override' (b ': as) a where
  override' f (Case g cs) = Case g (override' f cs)
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
      ('GHC.ShowType x 'GHC.:<>: 'GHC.Text " already is a member of "
       'GHC.:<>: 'GHC.ShowType xs0)
  Unique'' xs0 (_ ': xs) x = Unique'' xs0 xs x
  Unique'' xs0 '[] x = ()

type family Exclude (xs :: [k]) (x :: k) :: [k] where
  Exclude (x ': xs) x = Exclude xs x
  Exclude '[] x = '[]

type family All (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  All c (x ': xs) = (c x, All c xs)
  All c '[] = ()

