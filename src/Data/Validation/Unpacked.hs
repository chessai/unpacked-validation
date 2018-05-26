--------------------------------------------------------------------------------

-- Copyright © 2018 chessai

-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
-- 
--     * Redistributions of source code must retain the above copyright
--       notice, this list of conditions and the following disclaimer.
-- 
--     * Redistributions in binary form must reproduce the above
--       copyright notice, this list of conditions and the following
--       disclaimer in the documentation and/or other materials provided
--       with the distribution.
-- 
--     * Neither the name of chessai nor the names of other
--       contributors may be used to endorse or promote products derived
--       from this software without specific prior written permission.
-- 
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
-- "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
-- LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
-- A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
-- OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
-- SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
-- LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
-- DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
-- THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
-- (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

--------------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall #-}

--------------------------------------------------------------------------------

{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE CPP                #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE UnboxedSums        #-}
{-# LANGUAGE UnboxedTuples      #-}

--------------------------------------------------------------------------------

{-|
-}

module Data.Validation.Unpacked
  ( AccValidation(..)
  , isAccSuccess
  , isAccFailure
  , failures
  , successes
  , fromFailure
  , fromSuccess
  ) where

--------------------------------------------------------------------------------

import Prelude
  ()

import           Control.Applicative (Alternative((<|>)), Applicative((<*>), pure))
import           Control.Monad (return)

import           Data.Bifoldable (Bifoldable(bifoldMap))
import           Data.Bifunctor (Bifunctor(bimap))
import           Data.Bitraversable (Bitraversable(bitraverse))

import           Data.Eq             (Eq((==)))
import           Data.Foldable
  (Foldable(foldMap, foldr, foldl, length, null, product, sum))

import           Data.Function       (const, id, flip, (.), ($))
import           Data.Functor        (Functor(fmap))
import           Data.Functor.Classes
  ( Eq1(liftEq)
  , Ord1(liftCompare)
  , Read1(liftReadPrec, liftReadListPrec, liftReadList)
  , Show1(liftShowsPrec)
  , readData
  , readUnaryWith
  , liftReadListPrecDefault
  , liftReadListDefault
  , showsUnaryWith
  
  , Eq2(liftEq2)
  , Ord2(liftCompare2)
  , Read2(liftReadPrec2, liftReadListPrec2, liftReadList2)
  , Show2(liftShowsPrec2) 
  , liftReadList2Default  
  , liftReadListPrec2Default  
  )

import           Data.Monoid         (Monoid(mempty,mappend))
import           Data.Ord            (Ord(compare, (>=)), Ordering(GT, LT))
import           Data.Semigroup      (Semigroup((<>)))
import           Data.Traversable    (Traversable(sequenceA, traverse))

import           GHC.Base            (Bool(False,True))
import           GHC.Read            (Read(readPrec, readList), expectP)
import           GHC.Show            (Show(showsPrec, showList), showString, showParen, showList__)

import           Text.Read           (parens, Lexeme(Ident), (+++), readListPrec, readListDefault, readListPrecDefault)
import           Text.ParserCombinators.ReadPrec (prec, step)

--------------------------------------------------------------------------------

data AccValidation a b = AccValidation (# a | b #)

pattern AccFailure :: a -> AccValidation a b
pattern AccFailure a = AccValidation (# a | #)

pattern AccSuccess :: b -> AccValidation a b
pattern AccSuccess b = AccValidation (# | b #)

{-# COMPLETE AccFailure, AccSuccess #-}

-- | This is the same as 'AccFailure'.
accFailure :: a -> AccValidation a b
accFailure a = AccValidation (# a | #)
{-# INLINE accFailure #-}

-- | This is the same as 'AccSuccess'.
accSuccess :: b -> AccValidation a b
accSuccess b = AccValidation (# | b #)
{-# INLINE accSuccess #-}

accValidate :: (a -> c) -> (b -> c) -> AccValidation a b -> c
accValidate fa fb (AccValidation x) = case x of
  (# a | #) -> fa a
  (# | b #) -> fb b
{-# INLINE accValidate #-}

isAccFailure :: AccValidation a b -> Bool
isAccFailure = accValidate (const True) (const False)
{-# INLINE isAccFailure #-}

isAccSuccess :: AccValidation a b -> Bool
isAccSuccess = accValidate (const False) (const True)
{-# INLINE isAccSuccess #-}

failures :: [AccValidation a b] -> [a]
failures x = [a | AccFailure a <- x]

successes :: [AccValidation a b] -> [b]
successes x = [b | AccSuccess b <- x]

fromFailure :: a -> AccValidation a b -> a
fromFailure def = accValidate id (const def)

fromSuccess :: b -> AccValidation a b -> b
fromSuccess def = accValidate (const def) id

--------------------------------------------------------------------------------

-- this is what happens when you can't derive things
instance (Eq a, Eq b) => Eq (AccValidation a b) where
  AccFailure  a == AccFailure  b = a == b
  AccSuccess a == AccSuccess b = a == b
  _       == _       = False
  {-# INLINE (==) #-}

-- this is what happens when you can't derive things
instance (Ord a, Ord b) => Ord (AccValidation a b) where
  compare x y
    = case x of
        AccFailure a -> case y of
          AccFailure b -> compare a b
          _      -> LT
        AccSuccess a -> case y of
          AccSuccess b -> compare a b
          _       -> GT
  {-# INLINE compare #-}

-- this is what happens when you can't derive things
instance (Read a, Read b) => Read (AccValidation a b) where
  readPrec
    = parens (prec 10
          (do expectP (Ident "AccFailure")
              a <- step readPrec
              return (AccFailure a))
          +++
            prec
              10
              (do expectP (Ident "AccSuccess")
                  b <- step readPrec
                  return (AccSuccess b)))
  readList = readListDefault
  readListPrec = readListPrecDefault

-- this is what happens when you can't derive things
instance (Show b, Show a) => Show (AccValidation a b) where
  showsPrec i (AccFailure a)
    = showParen
        (i >= 11)
        ((.)
           (showString "AccFailure ") (showsPrec 11 a))
  showsPrec i (AccSuccess b)
    = showParen
        (i >= 11)
        ((.)
           (showString "AccSuccess ") (showsPrec 11 b))
  showList = showList__ (showsPrec 0)

instance Semigroup a => Semigroup (AccValidation a b) where
  AccFailure e1 <> AccFailure e2 = AccFailure (e1 <> e2)
  AccFailure _  <> AccSuccess a2 = AccSuccess a2
  AccSuccess a1 <> AccFailure _  = AccSuccess a1
  AccSuccess a1 <> AccSuccess _  = AccSuccess a1
  {-# INLINE (<>) #-}

instance (Monoid a) => Monoid (AccValidation a b) where
  mempty = AccFailure mempty
  {-# INLINE mempty #-}
  mappend (AccFailure e1) (AccFailure e2) = AccFailure (mappend e1 e2)
  mappend (AccFailure  _) (AccSuccess a2) = AccSuccess a2
  mappend (AccSuccess a1) (AccFailure  _) = AccSuccess a1
  mappend (AccSuccess a1) (AccSuccess  _) = AccSuccess a1

instance Functor (AccValidation a) where
  fmap f = accValidate accFailure (accSuccess . f)
  {-# INLINE fmap #-}

instance Semigroup e => Applicative (AccValidation e) where
  pure = accSuccess
  {-# INLINE pure #-} 
  AccFailure e1 <*> AccFailure e2 = AccFailure (e1 <> e2)
  AccFailure e1 <*> AccSuccess _  = AccFailure e1
  AccSuccess _  <*> AccFailure e2 = AccFailure e2
  AccSuccess f  <*> AccSuccess a  = AccSuccess (f a)
  
  ef <*> ex = accValidate accFailure (\f -> fmap f ex) ef
  {-# INLINE (<*>) #-}

instance Foldable (AccValidation a) where
  foldMap f e = accValidate (const mempty) f e
  {-# INLINE foldMap #-}
  foldr f z e = accValidate (const z) ((flip f) z) e
  {-# INLINE foldr #-}
  foldl f z e = accValidate (const z) (f z) e
  {-# INLINE foldl #-}
  length = accValidate (const 0) (const 1)
  {-# INLINE length #-}
  null = isAccFailure
  {-# INLINE null #-}
  product = accValidate (const 0) id
  {-# INLINE product #-}
  sum = accValidate (const 0) id
  {-# INLINE sum #-}

instance Traversable (AccValidation a) where
  sequenceA ea = accValidate (pure . accFailure) (fmap accSuccess) ea
  {-# INLINE sequenceA #-}
  traverse f ea = accValidate (pure . accFailure) (fmap accSuccess . f) ea 
  {-# INLINE traverse #-}

instance (Eq a) => Eq1 (AccValidation a) where
    liftEq = liftEq2 (==)

instance (Ord a) => Ord1 (AccValidation a) where
    liftCompare = liftCompare2 compare

instance (Read a) => Read1 (AccValidation a) where
    liftReadPrec = liftReadPrec2 readPrec readListPrec

    liftReadListPrec = liftReadListPrecDefault
    liftReadList     = liftReadListDefault

instance (Show a) => Show1 (AccValidation a) where
    liftShowsPrec = liftShowsPrec2 showsPrec showList

instance Eq2 AccValidation where
    liftEq2 e1 _ (AccFailure  x) (AccFailure  y) = e1 x y
    liftEq2 _  _ (AccFailure  _) (AccSuccess _) = False
    liftEq2 _  _ (AccSuccess _) (AccFailure  _) = False
    liftEq2 _ e2 (AccSuccess x) (AccSuccess y) = e2 x y

instance Ord2 AccValidation where
    liftCompare2 comp1 _ (AccFailure x) (AccFailure y) = comp1 x y
    liftCompare2 _ _ (AccFailure _) (AccSuccess _) = LT
    liftCompare2 _ _ (AccSuccess _) (AccFailure _) = GT
    liftCompare2 _ comp2 (AccSuccess x) (AccSuccess y) = comp2 x y

instance Read2 AccValidation where
    liftReadPrec2 rp1 _ rp2 _ = readData $
         readUnaryWith rp1 "AccFailure" AccFailure <|>
         readUnaryWith rp2 "AccSuccess" AccSuccess

    liftReadListPrec2 = liftReadListPrec2Default
    liftReadList2     = liftReadList2Default

instance Show2 AccValidation where
    liftShowsPrec2 sp1 _ _ _ d (AccFailure x) = showsUnaryWith sp1 "AccFailure" d x
    liftShowsPrec2 _ _ sp2 _ d (AccSuccess x) = showsUnaryWith sp2 "AccSuccess" d x

instance Bifunctor AccValidation where
  bimap f g = accValidate (accFailure . f) (accSuccess . g)
  {-# INLINE bimap #-}

instance Bifoldable AccValidation where
  bifoldMap f g = accValidate f g 
  {-# INLINE bifoldMap #-}

instance Bitraversable AccValidation where
  bitraverse f g = accValidate (fmap accFailure . f) (fmap accSuccess . g) 
  {-# INLINE bitraverse #-}
