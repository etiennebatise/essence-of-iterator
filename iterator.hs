{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

import Data.Monoid
import Data.Monoid (Sum)
import Prelude (Integer, Num, Maybe(..), curry, uncurry, fst, snd, (+), flip)


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

newtype Const a b = Const { unConst :: a }

-- class Monoid a where
--   mempty :: a
--   mappend :: a -> a -> a
--   mconcat :: [a] -> a

instance Functor (Const a) where
  fmap _ (Const x) = Const x

instance Monoid a => Applicative (Const a) where
  pure _ = Const mempty
  f <*> x = Const (unConst f `mappend` unConst x)

instance Functor [] where
  fmap f (x:xs) = f x : (fmap f xs)
  fmap f _ = []

instance Applicative [] where
  pure x = xs where xs = x:xs
  (f:fs) <*> (x:xs) = f x : (fs <*> xs)
  _ <*> _ = []

-- 3.3 Combining applicative functors

data (Prod m n) a = Prod { pfst :: m a, psnd :: n a }

(<&>) :: (Functor m, Functor n) => (a -> m b) -> (a -> n b) -> (a -> (Prod m n) b)
(<&>) f g x = Prod (f x) (g x)

instance (Functor m, Functor n) => Functor (Prod m n) where
  fmap f x = Prod (fmap f (pfst x)) (fmap f (psnd x))


instance (Applicative m, Applicative n) => Applicative (Prod m n) where
  pure x = Prod (pure x) (pure x)
  f <*> x = Prod (pfst f <*> pfst x) (psnd f <*> psnd x)

data (Comp m n) a = Comp { unComp :: m (n a) }

(<.>) :: (Functor n, Functor m) => (b -> n c) -> (a -> m b) -> (a -> (Comp m n) c)
f <.> g = Comp . fmap f . g

instance (Functor m, Functor n) => Functor (Comp m n) where
  fmap f = Comp . fmap (fmap f) . unComp

instance (Applicative m, Applicative n) => Applicative (Comp m n) where
  pure = Comp . pure . pure
  f <*> x = Comp (pure (<*>) <*> unComp f <*> unComp x)

-- 3.4 Idiomatic Traversal

traverseList :: Applicative m => (a -> m b) -> [a] -> m [b]
traverseList _ [] = pure []
traverseList f (x:xs) = pure (:) <*> f x <*> traverseList f xs

distList :: Applicative m => [m a] -> m [a]
distList = traverseList id

class (Functor t) => Traversable t where
  traverse :: Applicative m => (a -> m b) -> t a -> m (t b)
  traverse f = dist . fmap f

  dist :: Applicative m => t (m a) -> m (t a)
  dist = traverse id

data Tree a = Leaf a | Bin (Tree a) (Tree a)

instance Functor Tree where
  fmap f (Leaf x) = Leaf (f x)
  fmap f (Bin x y) = Bin (fmap f x) (fmap f y)

instance Traversable Tree where
  traverse f (Leaf x) = pure Leaf <*> (f x)
  traverse f (Bin x y) = pure Bin <*> traverse f x <*> traverse f y

class Bifunctor s => Bitraversable s where
  bidist :: Applicative m => s (m a) (m b) -> m (s a b)

instance Bifunctor s => Functor (Fix s) where
  fmap = mapFix

instance Bitraversable s => Traversable (Fix s) where
  traverse f = foldFix(fmap In . bidist . bimap f id)

newtype Id a = Id { unId :: a }

instance Functor Id where
  fmap f = Id . f . unId

instance Applicative Id where
  pure = Id
  f <*> x = Id (unId f $ unId x)

reduce :: (Traversable t, Monoid m) => (a -> m) -> t a -> m
reduce f = unConst . traverse (Const . f)

crush :: (Traversable t, Monoid m)  => t m -> m
crush = reduce id

tsum :: (Traversable t) => t (Sum Integer) -> Sum Integer
tsum = crush

-- 4 TRAVERSALS AS ITERATORS 

class Coerce a b | a -> b where
  down ::  a -> b
  up :: b -> a

instance Coerce (Id a) a where
  down = unId
  up = Id

instance Coerce (Const a b) a where
  down = unConst
  up = Const

instance (Coerce (m a) b, Coerce (n a) c) => Coerce (Prod m n a) (b, c) where
  down x = (down $ pfst x, down $ psnd x)
  up (x, y)= Prod (up x) (up y)

instance (Functor m, Functor n, Coerce (m b) c, Coerce (n a) b) => Coerce (Comp m n a) c where
  down = down . fmap down . unComp
  up =  Comp . fmap up . up

instance Coerce (m a) b => Coerce (M m a) b where
  down = down . unWrap
  up = Wrap . up

 -- 4.1 Shape and contents

-- monoid
contentsBody :: a -> Const [a] b
contentsBody a = up [a]

contents :: Traversable t => t a -> Const [a] (t b)
contents = traverse contentsBody

run :: (Traversable t, Coerce b c) => (t a -> b) -> t a -> c
run f = down . f

runContents :: (Traversable t) => t a -> [a]
runContents = run contents
-- = reduce (:[])

shapeBody :: a -> Id ()
shapeBody _ = Id ()

shape :: Traversable t => t a -> Id (t ())
shape = traverse shapeBody

runShape :: (Traversable t) => t a -> t ()
runShape = run shape

decompose :: Traversable t => t a -> ((Prod Id (Const [a])) (t ()))
-- decompose = shape <&> contents -- NAIVE
decompose = traverse (shapeBody <&> contentsBody)


instance Coerce (State s a) (s -> (a, s)) where
  down = runState
  up = State

instance Coerce (Maybe a) (Maybe a) where
  down = id
  up = id

instance Functor (State s) where
  fmap f sa = State(\s -> let (a, s') = runState sa s
                     in (f a, s'))

instance Monad (State s) where
  return a = State(\s -> (a, s))
  sa >>= f = State(\s -> let (a, s') = runState sa s
                      in runState (f a) s')

instance Functor (Maybe) where
  fmap f (Just a) = Just (f a)
  fmap f Nothing = Nothing

instance Monad (Maybe) where
  return a = Just a

  Just a >>= f = f a
  Nothing >>= _ = Nothing

reassembleBody :: () -> Comp (M (State [a])) (M Maybe) a
reassembleBody = let in up . takeHead
  where takeHead _ []     = (Nothing, [])
        takeHead _ (x:xs) = (Just x, xs)


reassemble :: Traversable t => t () -> Comp (M (State [a])) (M Maybe) (t a)
reassemble = traverse reassembleBody

runReassemble :: Traversable t => (t (), [a]) -> Maybe (t a)
runReassemble = fst . uncurry (run reassemble) -- magic

-- run reassemble t = (s, c) <=> run reassemble s c = (Just t, [])

-- 4.2 Collection and dispersal

-- accumulates elements effectfully (a -> m ()), but modifies elements purely and
-- independently of accumulation
collect ::  (Traversable t, Applicative m) => (a -> m ()) -> (a -> b) -> t a -> m (t b)
collect f g = traverse (\a -> pure (\_ -> g a) <*> f a)

get :: State a a
get = State(\s -> (s, s))

put :: s -> State s ()
put s = State(\_ -> ((), s))

loop :: Traversable t => (a -> b) -> t a -> M (State Integer) (t b)
-- loop = collect (\a -> up (\i -> ((), i+1)))
loop = collect (\_ -> Wrap (get >>= (put . (1+))))

-- modifies elements purely (a -> b -> c) but dependent on the state
disperse :: (Traversable t, Applicative m) => m b -> (a -> b -> c) -> t a -> m (t c)
disperse mb g = traverse (\a -> pure (g a) <*> mb )

label :: Traversable t => t a -> M (State Integer) (t Integer)
label = disperse (Wrap (step)) (curry snd) 

step :: State Integer Integer
step = get >>= (\i -> put (i+1)
               >>= (\_ -> return i))

-- 4.3 Backward Traversal
newtype Backwards m a = Backwards { runBackwards :: m a }

instance Functor m => Functor (Backwards m) where
  fmap f = Backwards . fmap f . runBackwards

instance Applicative m => Applicative (Backwards m) where
  pure = Backwards . pure
  f <*> a = Backwards (pure (flip ($)) <*> (runBackwards a) <*> (runBackwards f))

data AppAdapter m where
  AppAdapter ::  Applicative (g m) => (forall a. m a -> g m a) -> (forall a. g m a -> m a) -> AppAdapter m

backwards :: Applicative m => AppAdapter m
backwards = AppAdapter Backwards runBackwards

ptraverse :: (Applicative m, Traversable t) => AppAdapter m -> (a -> m b) -> t a -> m (t b)
ptraverse (AppAdapter insert retrieve) f = retrieve . traverse (insert . f)


-- 5. LAWS OF TRAVERSE

-- 5.1 Free theorems of traversal

{-
| A parametrically polymorphic function enjoys a property that follows entirely
  from its type, without any consideration of its implementation

(1) dist . fmap (fmap k) == fmap (fmap k) . dist (2)
(1) t (m a) => t (m b) => m (t b)
(2) t (m a) => m (t a) => m (t b)

| Corollaries, theorem for traverse:

traverse (g . h) = traverse g . fmap h
traverse (fmap k . f) = fmap (fma k) . traverse f
-}

-- 5.2 Sequential composition of traversals

{-
| dist should respect identity A.F. and composition A.F. :

dist . fmap Id = Id
dist . fmap Comp = Comp . fmap dist .dist

| Corollaries, properties of traverse:

(1) traverse (Id . f) = Id . fmap f
(2) traverse (Comp . fmap f . g) = Comp . fmap (traverse f) . traverse g

Which means:
(1) => traverse in the Id A.F. is essentially just fmap
(2) => provides a fusion rule for sequential composition of 2 traversals
(2) => traverse (f <.> g) = traverse f <.> traverse g
-}

