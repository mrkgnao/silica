{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeInType #-}
module Silica.Raw where
-- (
-- -- * Other
--   R_Equality, R_Equality', R_As
-- , R_Iso, R_Iso'
-- , R_Prism , R_Prism'
-- , R_Review , R_AReview
-- -- * R_Lenses, R_Folds and R_Traversals -- , R_Lens, R_Lens'
-- , R_Traversal, R_Traversal'
-- , R_Traversal1, R_Traversal1'
-- , R_Setter, R_Setter'
-- , R_Getter, R_Fold
-- , R_Fold1
-- -- * Indexed
-- , R_IndexedLens, R_IndexedLens'
-- , R_IndexedTraversal, R_IndexedTraversal'
-- , R_IndexedTraversal1, R_IndexedTraversal1'
-- , R_IndexedSetter, R_IndexedSetter'
-- , R_IndexedGetter, R_IndexedFold
-- , R_IndexedFold1
-- -- * Index-Preserving
-- , R_IndexPreservingLens, R_IndexPreservingLens'
-- , R_IndexPreservingTraversal, R_IndexPreservingTraversal'
-- , R_IndexPreservingTraversal1, R_IndexPreservingTraversal1'
-- , R_IndexPreservingSetter, R_IndexPreservingSetter'
-- , R_IndexPreservingGetter, R_IndexPreservingFold
-- , R_IndexPreservingFold1
-- -- * Common
-- , Simple
-- , R_LensLike, R_LensLike'
-- , R_Over, R_Over'
-- , R_IndexedLensLike, R_IndexedLensLike'
-- , R_Optical, R_Optical'
-- , R_Optic, R_Optic'
-- )

import Control.Applicative
import Silica.Internal.Setter
import Silica.Internal.Indexed
import Data.Bifunctor
import Data.Functor.Identity
import Data.Functor.Contravariant
import Data.Functor.Apply
import Data.Kind
import Data.Profunctor
import Data.Tagged
import Prelude
import Data.Semigroup

import GHC.TypeLits

{-# ANN module "HLint: ignore Use camelCase" #-}


-------------------------------------------------------------------------------
-- Lenses
-------------------------------------------------------------------------------

type R_Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t

-- | @
-- type 'R_Lens'' = 'Simple' 'R_Lens'
-- @
type R_Lens' s a = R_Lens s s a a

-- | Every 'R_IndexedLens' is a valid 'R_Lens' and a valid 'Control.R_Lens.R_Traversal.R_IndexedTraversal'.
type R_IndexedLens i s t a b = forall f p. (Indexable i p, Functor f) => p a (f b) -> s -> f t

-- | @
-- type 'R_IndexedLens'' i = 'Simple' ('R_IndexedLens' i)
-- @
type R_IndexedLens' i s a = R_IndexedLens i s s a a

-- | An 'R_IndexPreservingLens' leaves any index it is composed with alone.
type R_IndexPreservingLens s t a b = forall p f. (Conjoined p, Functor f) => p a (f b) -> p s (f t)

-- | @
-- type 'R_IndexPreservingLens'' = 'Simple' 'R_IndexPreservingLens'
-- @
type R_IndexPreservingLens' s a = R_IndexPreservingLens s s a a

------------------------------------------------------------------------------
-- R_Traversals
------------------------------------------------------------------------------

-- | A 'R_Traversal' can be used directly as a 'Control.R_Lens.R_Setter.R_Setter' or a 'R_Fold' (but not as a 'R_Lens') and provides
-- the ability to both read and update multiple fields, subject to some relatively weak 'R_Traversal' laws.
--
-- These have also been known as multilenses, but they have the signature and spirit of
--
-- @
-- 'Data.Traversable.traverse' :: 'Data.Traversable.Traversable' f => 'R_Traversal' (f a) (f b) a b
-- @
--
-- and the more evocative name suggests their application.
--
-- Most of the time the 'R_Traversal' you will want to use is just 'Data.Traversable.traverse', but you can also pass any
-- 'R_Lens' or 'R_Iso' as a 'R_Traversal', and composition of a 'R_Traversal' (or 'R_Lens' or 'R_Iso') with a 'R_Traversal' (or 'R_Lens' or 'R_Iso')
-- using ('.') forms a valid 'R_Traversal'.
--
-- The laws for a 'R_Traversal' @t@ follow from the laws for 'Data.Traversable.Traversable' as stated in \"The Essence of the Iterator Pattern\".
--
-- @
-- t 'pure' ≡ 'pure'
-- 'fmap' (t f) '.' t g ≡ 'Data.Functor.Compose.getCompose' '.' t ('Data.Functor.Compose.Compose' '.' 'fmap' f '.' g)
-- @
--
-- One consequence of this requirement is that a 'R_Traversal' needs to leave the same number of elements as a
-- candidate for subsequent 'R_Traversal' that it started with. Another testament to the strength of these laws
-- is that the caveat expressed in section 5.5 of the \"Essence of the Iterator Pattern\" about exotic
-- 'Data.Traversable.Traversable' instances that 'Data.Traversable.traverse' the same entry multiple times was actually already ruled out by the
-- second law in that same paper!
type R_Traversal s t a b = forall f. Applicative f => (a -> f b) -> s -> f t

-- | @
-- type 'R_Traversal'' = 'Simple' 'R_Traversal'
-- @
type R_Traversal' s a = R_Traversal s s a a

type R_Traversal1 s t a b = forall f. Apply f => (a -> f b) -> s -> f t
type R_Traversal1' s a = R_Traversal1 s s a a

-- | Every 'R_IndexedTraversal' is a valid 'Control.R_Lens.R_Traversal.R_Traversal' or
-- 'Control.R_Lens.R_Fold.R_IndexedFold'.
--
-- The 'Indexed' constraint is used to allow an 'R_IndexedTraversal' to be used
-- directly as a 'Control.R_Lens.R_Traversal.R_Traversal'.
--
-- The 'Control.R_Lens.R_Traversal.R_Traversal' laws are still required to hold.
--
-- In addition, the index @i@ should satisfy the requirement that it stays
-- unchanged even when modifying the value @a@, otherwise traversals like
-- 'indices' break the 'R_Traversal' laws.
type R_IndexedTraversal i s t a b = forall p f. (Indexable i p, Applicative f) => p a (f b) -> s -> f t

-- | @
-- type 'R_IndexedTraversal'' i = 'Simple' ('R_IndexedTraversal' i)
-- @
type R_IndexedTraversal' i s a = R_IndexedTraversal i s s a a

type R_IndexedTraversal1 i s t a b = forall p f. (Indexable i p, Apply f) => p a (f b) -> s -> f t
type R_IndexedTraversal1' i s a = R_IndexedTraversal1 i s s a a

-- | An 'R_IndexPreservingLens' leaves any index it is composed with alone.
type R_IndexPreservingTraversal s t a b = forall p f. (Conjoined p, Applicative f) => p a (f b) -> p s (f t)

-- | @
-- type 'R_IndexPreservingTraversal'' = 'Simple' 'R_IndexPreservingTraversal'
-- @
type R_IndexPreservingTraversal' s a = R_IndexPreservingTraversal s s a a

type R_IndexPreservingTraversal1 s t a b = forall p f. (Conjoined p, Apply f) => p a (f b) -> p s (f t)
type R_IndexPreservingTraversal1' s a = R_IndexPreservingTraversal1 s s a a

------------------------------------------------------------------------------
-- R_Setters
------------------------------------------------------------------------------

-- | The only 'R_LensLike' law that can apply to a 'R_Setter' @l@ is that
--
-- @
-- 'Control.R_Lens.R_Setter.set' l y ('Control.R_Lens.R_Setter.set' l x a) ≡ 'Control.R_Lens.R_Setter.set' l y a
-- @
--
-- You can't 'Control.R_Lens.R_Getter.view' a 'R_Setter' in general, so the other two laws are irrelevant.
--
-- However, two 'Functor' laws apply to a 'R_Setter':
--
-- @
-- 'Control.R_Lens.R_Setter.over' l 'id' ≡ 'id'
-- 'Control.R_Lens.R_Setter.over' l f '.' 'Control.R_Lens.R_Setter.over' l g ≡ 'Control.R_Lens.R_Setter.over' l (f '.' g)
-- @
--
-- These can be stated more directly:
--
-- @
-- l 'pure' ≡ 'pure'
-- l f '.' 'untainted' '.' l g ≡ l (f '.' 'untainted' '.' g)
-- @
--
-- You can compose a 'R_Setter' with a 'R_Lens' or a 'R_Traversal' using ('.') from the @Prelude@
-- and the result is always only a 'R_Setter' and nothing more.
--
-- >>> over traverse f [a,b,c,d]
-- [f a,f b,f c,f d]
--
-- >>> over _1 f (a,b)
-- (f a,b)
--
-- >>> over (traverse._1) f [(a,b),(c,d)]
-- [(f a,b),(f c,d)]
--
-- >>> over both f (a,b)
-- (f a,f b)
--
-- >>> over (traverse.both) f [(a,b),(c,d)]
-- [(f a,f b),(f c,f d)]
type R_Setter s t a b = forall f. Settable f => (a -> f b) -> s -> f t

-- | A 'R_Setter'' is just a 'R_Setter' that doesn't change the types.
--
-- These are particularly common when talking about monomorphic containers. /e.g./
--
-- @
-- 'sets' Data.Text.map :: 'R_Setter'' 'Data.Text.Internal.Text' 'Char'
-- @
--
-- @
-- type 'R_Setter'' = 'Simple' 'R_Setter'
-- @
type R_Setter' s a = R_Setter s s a a

-- | Every 'R_IndexedSetter' is a valid 'R_Setter'.
--
-- The 'R_Setter' laws are still required to hold.
type R_IndexedSetter i s t a b = forall f p.
  (Indexable i p, Settable f) => p a (f b) -> s -> f t

-- | @
-- type 'R_IndexedSetter'' i = 'Simple' ('R_IndexedSetter' i)
-- @
type R_IndexedSetter' i s a = R_IndexedSetter i s s a a

-- | An 'R_IndexPreservingSetter' can be composed with a 'R_IndexedSetter', 'R_IndexedTraversal' or 'R_IndexedLens'
-- and leaves the index intact, yielding an 'R_IndexedSetter'.
type R_IndexPreservingSetter s t a b = forall p f. (Conjoined p, Settable f) => p a (f b) -> p s (f t)

-- | @
-- type 'IndexedPreservingR_Setter'' i = 'Simple' 'IndexedPreservingR_Setter'
-- @
type R_IndexPreservingSetter' s a = R_IndexPreservingSetter s s a a

-----------------------------------------------------------------------------
-- R_Isomorphisms
-----------------------------------------------------------------------------

-- | R_Isomorphism families can be composed with another 'R_Lens' using ('.') and 'id'.
--
-- Since every 'R_Iso' is both a valid 'R_Lens' and a valid 'R_Prism', the laws for those types
-- imply the following laws for an 'R_Iso' 'f':
--
-- @
-- f '.' 'Control.R_Lens.R_Iso.from' f ≡ 'id'
-- 'Control.R_Lens.R_Iso.from' f '.' f ≡ 'id'
-- @
--
-- Note: Composition with an 'R_Iso' is index- and measure- preserving.
type R_Iso s t a b = forall p f. (Profunctor p, Functor f) => p a (f b) -> p s (f t)

-- | @
-- type 'R_Iso'' = 'Control.R_Lens.Type.Simple' 'R_Iso'
-- @
type R_Iso' s a = R_Iso s s a a

------------------------------------------------------------------------------
-- R_Review Internals
------------------------------------------------------------------------------

-- | This is a limited form of a 'R_Prism' that can only be used for 're' operations.
--
-- Like with a 'R_Getter', there are no laws to state for a 'R_Review'.
--
-- You can generate a 'R_Review' by using 'unto'. You can also use any 'R_Prism' or 'R_Iso'
-- directly as a 'R_Review'.
type R_Review t b = forall p f. (Choice p, Bifunctor p, Settable f) => R_Optic' p f t b

-- | If you see this in a signature for a function, the function is expecting a 'R_Review'
-- (in practice, this usually means a 'R_Prism').
type R_AReview t b = R_Optic' Tagged Identity t b

------------------------------------------------------------------------------
-- R_Prism Internals
------------------------------------------------------------------------------

-- | A 'R_Prism' @l@ is a 'R_Traversal' that can also be turned
-- around with 'Control.R_Lens.R_Review.re' to obtain a 'R_Getter' in the
-- opposite direction.
--
-- There are two laws that a 'R_Prism' should satisfy:
--
-- First, if I 'Control.R_Lens.R_Review.re' or 'Control.R_Lens.R_Review.review' a value with a 'R_Prism' and then 'Control.R_Lens.R_Fold.preview' or use ('Control.R_Lens.R_Fold.^?'), I will get it back:
--
-- @
-- 'Control.R_Lens.R_Fold.preview' l ('Control.R_Lens.R_Review.review' l b) ≡ 'Just' b
-- @
--
-- Second, if you can extract a value @a@ using a 'R_Prism' @l@ from a value @s@, then the value @s@ is completely described by @l@ and @a@:
--
-- If @'Control.R_Lens.R_Fold.preview' l s ≡ 'Just' a@ then @'Control.R_Lens.R_Review.review' l a ≡ s@
--
-- These two laws imply that the 'R_Traversal' laws hold for every 'R_Prism' and that we 'Data.Traversable.traverse' at most 1 element:
--
-- @
-- 'Control.R_Lens.R_Fold.lengthOf' l x '<=' 1
-- @
--
-- It may help to think of this as a 'R_Iso' that can be partial in one direction.
--
-- Every 'R_Prism' is a valid 'R_Traversal'.
--
-- Every 'R_Iso' is a valid 'R_Prism'.
--
-- For example, you might have a @'R_Prism'' 'Integer' 'Numeric.Natural.Natural'@ allows you to always
-- go from a 'Numeric.Natural.Natural' to an 'Integer', and provide you with tools to check if an 'Integer' is
-- a 'Numeric.Natural.Natural' and/or to edit one if it is.
--
--
-- @
-- 'nat' :: 'R_Prism'' 'Integer' 'Numeric.Natural.Natural'
-- 'nat' = 'Control.R_Lens.R_Prism.prism' 'toInteger' '$' \\ i ->
--    if i '<' 0
--    then 'Left' i
--    else 'Right' ('fromInteger' i)
-- @
--
-- Now we can ask if an 'Integer' is a 'Numeric.Natural.Natural'.
--
-- >>> 5^?nat
-- Just 5
--
-- >>> (-5)^?nat
-- Nothing
--
-- We can update the ones that are:
--
-- >>> (-3,4) & both.nat *~ 2
-- (-3,8)
--
-- And we can then convert from a 'Numeric.Natural.Natural' to an 'Integer'.
--
-- >>> 5 ^. re nat -- :: Natural
-- 5
--
-- Similarly we can use a 'R_Prism' to 'Data.Traversable.traverse' the 'Left' half of an 'Either':
--
-- >>> Left "hello" & _Left %~ length
-- Left 5
--
-- or to construct an 'Either':
--
-- >>> 5^.re _Left
-- Left 5
--
-- such that if you query it with the 'R_Prism', you will get your original input back.
--
-- >>> 5^.re _Left ^? _Left
-- Just 5
--
-- Another interesting way to think of a 'R_Prism' is as the categorical dual of a 'R_Lens'
-- -- a co-'R_Lens', so to speak. This is what permits the construction of 'Control.R_Lens.R_Prism.outside'.
--
-- Note: Composition with a 'R_Prism' is index-preserving.
type R_Prism s t a b = forall p f. (Choice p, Applicative f) => p a (f b) -> p s (f t)

-- | A 'Simple' 'R_Prism'.
type R_Prism' s a = R_Prism s s a a

-------------------------------------------------------------------------------
-- R_Equality
-------------------------------------------------------------------------------

-- | A witness that @(a ~ s, b ~ t)@.
--
-- Note: Composition with an 'R_Equality' is index-preserving.
type R_Equality (s :: k1) (t :: k2) (a :: k1) (b :: k2) = forall k3 (p :: k1 -> k3 -> *) (f :: k2 -> k3) .
    p a (f b) -> p s (f t)

-- | A 'Simple' 'R_Equality'.
type R_Equality' s a = R_Equality s s a a

-- | Composable `asTypeOf`. Useful for constraining excess
-- polymorphism, @foo . (id :: R_As Int) . bar@.
type R_As a = R_Equality' a a

-------------------------------------------------------------------------------
-- R_Getters
-------------------------------------------------------------------------------

-- | A 'R_Getter' describes how to retrieve a single value in a way that can be
-- composed with other 'R_LensLike' constructions.
--
-- Unlike a 'R_Lens' a 'R_Getter' is read-only. Since a 'R_Getter'
-- cannot be used to write back there are no 'R_Lens' laws that can be applied to
-- it. In fact, it is isomorphic to an arbitrary function from @(s -> a)@.
--
-- Moreover, a 'R_Getter' can be used directly as a 'Control.R_Lens.R_Fold.R_Fold',
-- since it just ignores the 'Applicative'.
type R_Getter s a = forall f. (Contravariant f, Functor f) => (a -> f a) -> s -> f s

-- | Every 'R_IndexedGetter' is a valid 'Control.R_Lens.R_Fold.R_IndexedFold' and can be used for 'Control.R_Lens.R_Getter.Getting' like a 'R_Getter'.
type R_IndexedGetter i s a = forall p f. (Indexable i p, Contravariant f, Functor f) => p a (f a) -> s -> f s

-- | An 'R_IndexPreservingGetter' can be used as a 'R_Getter', but when composed with an 'R_IndexedTraversal',
-- 'R_IndexedFold', or 'R_IndexedLens' yields an 'R_IndexedFold', 'R_IndexedFold' or 'R_IndexedGetter' respectively.
type R_IndexPreservingGetter s a = forall p f. (Conjoined p, Contravariant f, Functor f) => p a (f a) -> p s (f s)

--------------------------
-- R_Folds
--------------------------

-- | A 'R_Fold' describes how to retrieve multiple values in a way that can be composed
-- with other 'R_LensLike' constructions.
--
-- A @'R_Fold' s a@ provides a structure with operations very similar to those of the 'Data.R_Foldable.R_Foldable'
-- typeclass, see 'Control.R_Lens.R_Fold.foldMapOf' and the other 'R_Fold' combinators.
--
-- By convention, if there exists a 'foo' method that expects a @'Data.R_Foldable.R_Foldable' (f a)@, then there should be a
-- @fooOf@ method that takes a @'R_Fold' s a@ and a value of type @s@.
--
-- A 'R_Getter' is a legal 'R_Fold' that just ignores the supplied 'Data.Monoid.Monoid'.
--
-- Unlike a 'Control.R_Lens.R_Traversal.R_Traversal' a 'R_Fold' is read-only. Since a 'R_Fold' cannot be used to write back
-- there are no 'R_Lens' laws that apply.
type R_Fold s a = forall f. (Contravariant f, Applicative f) => (a -> f a) -> s -> f s

-- | Every 'R_IndexedFold' is a valid 'Control.R_Lens.R_Fold.R_Fold' and can be used for 'Control.R_Lens.R_Getter.Getting'.
type R_IndexedFold i s a = forall p f.  (Indexable i p, Contravariant f, Applicative f) => p a (f a) -> s -> f s

-- | An 'R_IndexPreservingFold' can be used as a 'R_Fold', but when composed with an 'R_IndexedTraversal',
-- 'R_IndexedFold', or 'R_IndexedLens' yields an 'R_IndexedFold' respectively.
type R_IndexPreservingFold s a = forall p f. (Conjoined p, Contravariant f, Applicative f) => p a (f a) -> p s (f s)

-- | A relevant R_Fold (aka 'R_Fold1') has one or more targets.
type R_Fold1 s a = forall f. (Contravariant f, Apply f) => (a -> f a) -> s -> f s
type R_IndexedFold1 i s a = forall p f.  (Indexable i p, Contravariant f, Apply f) => p a (f a) -> s -> f s
type R_IndexPreservingFold1 s a = forall p f. (Conjoined p, Contravariant f, Apply f) => p a (f a) -> p s (f s)

-------------------------------------------------------------------------------
-- Simple R_Overloading
-------------------------------------------------------------------------------

-- | A 'Simple' 'R_Lens', 'Simple' 'R_Traversal', ... can
-- be used instead of a 'R_Lens','R_Traversal', ...
-- whenever the type variables don't change upon setting a value.
--
-- @
-- 'Data.Complex.R_Lens._imagPart' :: 'Simple' 'R_Lens' ('Data.Complex.Complex' a) a
-- 'Control.R_Lens.R_Traversal.traversed' :: 'Simple' ('R_IndexedTraversal' 'Int') [a] a
-- @
--
-- Note: To use this alias in your own code with @'R_LensLike' f@ or
-- 'R_Setter', you may have to turn on @LiberalTypeSynonyms@.
--
-- This is commonly abbreviated as a \"prime\" marker, /e.g./ 'R_Lens'' = 'Simple' 'R_Lens'.
type Simple f s a = f s s a a

-------------------------------------------------------------------------------
-- R_Silica
-------------------------------------------------------------------------------

-- | A valid 'R_Optic' @l@ should satisfy the laws:
--
-- @
-- l 'pure' ≡ 'pure'
-- l ('Procompose' f g) = 'Procompose' (l f) (l g)
-- @
--
-- This gives rise to the laws for 'R_Equality', 'R_Iso', 'R_Prism', 'R_Lens',
-- 'R_Traversal', 'R_Traversal1', 'R_Setter', 'R_Fold', 'R_Fold1', and 'R_Getter' as well
-- along with their index-preserving variants.
--
-- @
-- type 'R_LensLike' f s t a b = 'R_Optic' (->) f s t a b
-- @
type R_Optic p f s t a b = p a (f b) -> p s (f t)

-- | @
-- type 'R_Optic'' p f s a = 'Simple' ('R_Optic' p f) s a
-- @
type R_Optic' p f s a = R_Optic p f s s a a

-- | @
-- type 'R_LensLike' f s t a b = 'R_Optical' (->) (->) f s t a b
-- @
--
-- @
-- type 'R_Over' p f s t a b = 'R_Optical' p (->) f s t a b
-- @
--
-- @
-- type 'R_Optic' p f s t a b = 'R_Optical' p p f s t a b
-- @
type R_Optical p q f s t a b = p a (f b) -> q s (f t)

-- | @
-- type 'R_Optical'' p q f s a = 'Simple' ('R_Optical' p q f) s a
-- @
type R_Optical' p q f s a = R_Optical p q f s s a a


-- | Many combinators that accept a 'R_Lens' can also accept a
-- 'R_Traversal' in limited situations.
--
-- They do so by specializing the type of 'Functor' that they require of the
-- caller.
--
-- If a function accepts a @'R_LensLike' f s t a b@ for some 'Functor' @f@,
-- then they may be passed a 'R_Lens'.
--
-- Further, if @f@ is an 'Applicative', they may also be passed a
-- 'R_Traversal'.
type R_LensLike f s t a b = (a -> f b) -> s -> f t

-- | @
-- type 'R_LensLike'' f = 'Simple' ('R_LensLike' f)
-- @
type R_LensLike' f s a = R_LensLike f s s a a

-- | Convenient alias for constructing indexed lenses and their ilk.
type R_IndexedLensLike i f s t a b = forall p. Indexable i p => p a (f b) -> s -> f t

-- | Convenient alias for constructing simple indexed lenses and their ilk.
type R_IndexedLensLike' i f s a = R_IndexedLensLike i f s s a a

-- | This is a convenient alias for use when you need to consume either indexed or non-indexed lens-likes based on context.
type R_Over p f s t a b = p a (f b) -> s -> f t

-- | This is a convenient alias for use when you need to consume either indexed or non-indexed lens-likes based on context.
--
-- @
-- type 'R_Over'' p f = 'Simple' ('R_Over' p f)
-- @
type R_Over' p f s a = R_Over p f s s a a

--------------------------------------------------------------------------------
