{-# LANGUAGE NoImplicitPrelude #-}

(.) :: (b -> c) -> (a -> b) -> (a -> c)
f . g = \x -> f (g x)

id :: a -> a
id x = x

($) :: (a -> b) -> a -> b
f $ x = f x

-- 2 FUNCTIONNAL ITERATION
-- 2.1 Origami

class Bifunctor s where
  -- should satisfy these laws:
  -- bimap id id = id -- identity
  -- bimap (f . h) (g . k) = bimap f g ◦ bimap h k -- composition
  bimap :: (a -> b) -> (c -> d) -> s a c -> s b d

data Fix s a = In { out :: s a (Fix s a) }

mapFix :: Bifunctor s => (a -> b) -> Fix s a -> Fix s b
mapFix f = In . bimap  f (mapFix f) . out

foldFix :: Bifunctor s => (s a b -> b) -> Fix s a -> b
foldFix f = f . bimap id (foldFix f) . out

unfoldFix :: Bifunctor s =>  (b -> s a b) -> b -> Fix s a
unfoldFix f  = In . bimap id (unfoldFix f) . f



-- 2.2 Crush

-- 2.3 Monadic map

class Functor f where
  -- should satisfy these laws:
  -- fmap id      = id              -- identity
  -- fmap (f . g) = fmap f . fmap g -- composition
  fmap :: (a -> b) -> f a -> f b

class Functor m => Monad m where
  -- should satisfy these laws:
  -- return a >>= f   = f a                     -- left unit
  -- mx >>= return    = mx                      -- right unit
  -- (mx >>= f) >>= g = mx >>= (\x -> f x >>= g) -- associativity
  (>>=) :: m a -> (a -> m b) -> m b
  return :: a -> m a

-- 3. APPLICATIVE FUNCTORS

class Functor m => Applicative m where
  -- should satisfy these laws:
  -- pure id <*> u              = u                      -- identiy
  -- pure (.) <*> u <*> v <*> w = u <*> v <*> w          -- composition
  -- pure f <*> pure x          = pure (f x)             -- homomorphism
  -- u <*> pure x               = pure (\f -> f x) <*> u  -- interchange
  pure :: a -> m a
  (<*>) :: m (a -> b) -> m a -> m b

-- 3.1 Monadic applicative functors

newtype M m a = Wrap { unWrap :: m a }

instance Monad m => Functor (M m) where
  fmap f (Wrap ma) = Wrap (ma >>= (return . f))

ap :: Monad m => m (a -> b) -> m a -> m b
mf `ap` mx = mf >>= (\f -> mx >>= (return . f))

instance Monad m => Applicative (M m) where
  pure x = Wrap (return x)
  f <*> x = let f' = unWrap f
                x' = unWrap x
                i = f' >>= (\g -> x' >>= (\y -> return (g y)))
            in Wrap i

newtype State s a = State { runState :: s -> (a, s) }

data Stream a = SCons a (Stream a)

instance Functor Stream where
  fmap f (SCons x xs)  = SCons (f x) (fmap f xs)

instance Applicative Stream where
  pure x = xs where xs = SCons x xs
  (SCons f fs) <*> (SCons x xs) = SCons (f x) (fs <*> xs)


newtype Reader r a = Reader { runReader :: r -> a }

-- 3.2 Monoidal applicative functors

newtype Const b a = Const { unConst :: b }

class Monoid a where
  mempty :: a
  mappend :: a -> a -> a
  mconcat :: [a] -> a

instance Functor (Const b) where
  fmap _ (Const x) = Const x

instance Monoid b => Applicative (Const b) where
  pure _ = Const mempty
  f <*> x = Const (unConst f `mappend` unConst x)

instance Functor [] where
  fmap f (x:xs) = f x : (fmap f xs)
  fmap f _ = []

instance Applicative [] where
  pure x = xs where xs = x:xs
  (f:fs) <*> (x:xs) = f x : (fs <*> xs)
  _ <*> _ = []
