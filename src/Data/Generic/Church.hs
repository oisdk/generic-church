{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE MagicHash              #-}

module Data.Generic.Church where


import           Data.Proxy
import           Data.Void
import           GHC.Generics
import           Data.Coerce
import           GHC.Prim

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
        Prod V1 r = Void -> r
        Prod (li :*: ri) a = Prod li (Prod ri a)

type family GenFold (c :: * -> *) (a :: *) :: * where
        GenFold (M1 i t c) a = GenFold c a
        GenFold (K1 i c) a = (c -> a) -> a
        GenFold U1 a = a -> a
        GenFold (li :+: ri) a = Sum li a (Sum ri a a)
        GenFold (li :*: ri) a = Prod li (Prod ri a) -> a

class Disj c  where
    elim :: c p -> (a -> r) -> Sum c a r
    ignore :: Proxy# (c a) -> r -> Sum c a r

class Prodable c  where
    strip :: c p -> Prod c r -> r

class ChurchGen c  where
    foldGen :: c a -> GenFold c a

instance Disj c =>
         Disj (M1 i t c) where
    elim = elim .# unM1
    ignore (_ :: Proxy (M1 i t c a)) = ignore (Proxy :: Proxy (c a))

instance Prodable c =>
         Prodable (M1 i t c) where
    strip = strip .# unM1

instance ChurchGen c =>
         ChurchGen (M1 i t c) where
    foldGen = foldGen .# unM1

instance Disj (K1 i c) where
  elim (K1 x) k f = k (f x)
  ignore _ r _ = r

instance Disj U1 where
    elim U1 = ($)
    ignore _ r _ = r

instance Prodable U1 where
    strip U1 x = x

instance ChurchGen U1 where
    foldGen U1 x = x

instance Disj V1 where
    elim = absurd1
    ignore _ = id

instance Prodable V1 where
    strip = absurd1

instance Prodable (K1 i c) where
    strip (K1 x) f = f x

instance ChurchGen (K1 i c) where
    foldGen (K1 x) f = f x

instance (Disj li, Disj ri) =>
         Disj (li :+: ri) where
    elim (L1 x) (k :: a -> r) = elim x (ignore (Proxy :: Proxy (ri a)) . k)
    elim (R1 x) (k :: a -> r) = ignore (Proxy :: Proxy (li a)) (elim x k)
    ignore (_ :: Proxy ((li :+: ri) a)) x =
        ignore (Proxy :: Proxy (li a)) (ignore (Proxy :: Proxy (ri a)) x)

instance (Disj li, Disj ri) =>
         ChurchGen (li :+: ri) where
    foldGen (x :: (li :+: ri) a) = elim x (id :: a -> a)

instance (Prodable li, Prodable ri) =>
         Prodable (li :*: ri) where
    strip (li :*: ri) f = strip ri (strip li f)

instance (Prodable li, Prodable ri) =>
         ChurchGen (li :*: ri) where
    foldGen (li :*: ri) f = strip ri (strip li f)

instance (Prodable li, Prodable ri) =>
         Disj (li :*: ri) where
    elim x k = k . strip x
    ignore _ r _ = r

class Church c  where
    type Fold c a :: *
    type Fold c a = GenFold (Rep c) a
    fold :: Proxy a -> c -> Fold c a
    default fold :: (Generic c
                    ,ChurchGen (Rep c)
                    ,GenFold (Rep c) a ~ Fold c a) => proxy a -> c -> Fold c a
    fold = genericFold

genericFold :: (Generic c, ChurchGen (Rep c)) => proxy a -> c -> GenFold (Rep c) a
genericFold (_ :: proxy a) (x :: c) = foldGen (from x :: Rep c a)

