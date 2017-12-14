{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Data.Generic.Church where

import           Data.Proxy
import           Data.Void
import           GHC.Generics
import           Data.Coerce

infixr 9 .#, #.

(.#) :: Coercible a b => (b -> c) -> (a -> b) -> a -> c
(.#) f _ = coerce f

(#.) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(#.) _ = coerce

absurd1 :: V1 a -> b
absurd1 = absurd . to .# M1

type family Sum (c :: * -> *) (a :: *) (r :: *) :: * where
        Sum (M1 i t c) a r = Sum c a r
        Sum (K1 i c) a r = (c -> a) -> r
        Sum U1 a r = a -> r
        Sum V1 a r = r
        Sum (li :+: ri) a r = Sum li a (Sum ri a r)
        Sum (li :*: ri) a r = Prod li (Prod ri a) -> r

type family Prod (c :: * -> *) (r :: *) :: * where
        Prod (M1 i t c) r = Prod c r
        Prod U1 r = r
        Prod (K1 i c) r = c -> r
        Prod V1 r = Void
        Prod (li :*: ri) a = Prod li (Prod ri a)

type family GenFold (c :: * -> *) (a :: *) :: * where
        GenFold (M1 i t c) a = GenFold c a
        GenFold (K1 i c) a = (c -> a) -> a
        GenFold U1 a = a -> a
        GenFold V1 a = a
        GenFold (li :+: ri) a = Sum li a (Sum ri a a)
        GenFold (li :*: ri) a = Prod li (Prod ri a) -> a

class Disj c  where
    elim :: c p -> (a -> r) -> Sum c a r
    expand :: Proxy (c a) -> r -> Sum c a r

class Conj c  where
    strip :: c p -> Prod c r -> r

class ChurchGen c  where
    foldGen :: c a -> GenFold c a

instance Disj c =>
         Disj (M1 i t c) where
    elim = elim .# unM1
    expand (_ :: Proxy (M1 i t c a)) = expand (Proxy :: Proxy (c a))
    {-# INLINE elim #-}
    {-# INLINE expand #-}

instance Conj c =>
         Conj (M1 i t c) where
    strip = strip .# unM1
    {-# INLINE strip #-}

instance ChurchGen c =>
         ChurchGen (M1 i t c) where
    foldGen = foldGen .# unM1
    {-# INLINE foldGen #-}

instance Disj (K1 i c) where
    elim (K1 x) k f = k (f x)
    expand _ r _ = r
    {-# INLINE elim #-}
    {-# INLINE expand #-}

instance Disj U1 where
    elim U1 = ($)
    expand _ r _ = r
    {-# INLINE elim #-}
    {-# INLINE expand #-}

instance Conj U1 where
    strip U1 = id
    {-# INLINE strip #-}

instance ChurchGen U1 where
    foldGen U1 = id
    {-# INLINE foldGen #-}

instance ChurchGen V1 where
    foldGen = absurd1

instance Disj V1 where
    elim = absurd1
    expand = const id
    {-# INLINE elim #-}
    {-# INLINE expand #-}

instance Conj V1 where
    strip = absurd1
    {-# INLINE strip #-}

instance Conj (K1 i c) where
    strip (K1 x) f = f x
    {-# INLINE strip #-}

instance ChurchGen (K1 i c) where
    foldGen (K1 x) f = f x
    {-# INLINE foldGen #-}

instance (Disj li, Disj ri) =>
         Disj (li :+: ri) where
    elim (L1 x) (k :: a -> r) = elim x (expand (Proxy :: Proxy (ri a)) . k)
    elim (R1 x) (k :: a -> r) = expand (Proxy :: Proxy (li a)) (elim x k)
    {-# INLINE elim #-}
    expand (_ :: Proxy ((li :+: ri) a)) x =
        expand (Proxy :: Proxy (li a)) (expand (Proxy :: Proxy (ri a)) x)
    {-# INLINE expand #-}

instance (Disj li, Disj ri) =>
         ChurchGen (li :+: ri) where
    foldGen (x :: (li :+: ri) a) = elim x (id :: a -> a)
    {-# INLINE foldGen #-}

instance (Conj li, Conj ri) =>
         Conj (li :*: ri) where
    strip (li :*: ri) f = strip ri (strip li f)
    {-# INLINE strip #-}

instance (Conj li, Conj ri) =>
         ChurchGen (li :*: ri) where
    foldGen (li :*: ri) f = strip ri (strip li f)
    {-# INLINE foldGen #-}

instance (Conj li, Conj ri) =>
         Disj (li :*: ri) where
    elim x k = k . strip x
    expand _ r _ = r
    {-# INLINE elim #-}
    {-# INLINE expand #-}

class Church c  where
    type Fold c a :: *
    type Fold c a = GenFold (Rep c) a
    fold :: c -> Proxy a -> Fold c a
    default fold :: (Generic c
                    ,ChurchGen (Rep c)
                    ,GenFold (Rep c) a ~ Fold c a) => c -> Proxy a -> Fold c a
    fold = genericFold

genericFold :: (Generic c, ChurchGen (Rep c)) => c -> Proxy a -> GenFold (Rep c) a
genericFold (x :: c) (_ :: Proxy a) = foldGen (from x :: Rep c a)
{-# INLINE genericFold #-}

instance Church Bool
instance Church Ordering
instance Church ()
instance Church [a]
instance Church Void
instance Church (Maybe a)
instance Church (Either a b)
instance Church (a,b)
instance Church (a,b,c)
instance Church (a,b,c,d)
instance Church (a,b,c,d,e)
instance Church (a,b,c,d,e,f)
