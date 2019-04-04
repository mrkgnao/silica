{-# LANGUAGE CPP #-}

{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2016 Edward Kmett and Eric Mertens
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module provides a shim around 'coerce' that defaults to 'unsafeCoerce'
-- on GHC < 7.8
-----------------------------------------------------------------------------
module Silica.Internal.Coerce
  ( coerce
  , coerce'
  ) where

import Data.Coerce

coerce' :: forall a b. Coercible a b => b -> a
coerce' = coerce (id :: a -> a)
{-# INLINE coerce' #-}
