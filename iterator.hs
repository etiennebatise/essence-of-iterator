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
import Prelude (Integer, Num, Maybe(..), curry, uncurry, fst, snd, (+), (*), flip, const, Char, String, Bool (True, False), Show,  (==), not, (&&))
import Data.Char (isSpace)


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

newtype Const a b = Const { unConst :: a } deriving Show

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

data (Prod m n) a = Prod { pfst :: m a, psnd :: n a } deriving Show

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
reassembleBody = up . takeHead
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

(1) dist . fmap Id = Id
(2) dist . fmap Comp = Comp . fmap dist . dist

(1) dist . fmap Id (t a) => dist (t (Id a)) => Id (t a)
(2) dist . fmap Comp (t (m (n a))) => dist (t (Comp m n a)) => Comp m n (t a)
(2) Comp . fmap dist . dist (t (m (n a))) => Comp . fmap dist (m (t (n a))) => Comp (m (n (t a))) => Comp m n (t a)

| Corollaries, properties of traverse:

(1) traverse (Id . f) = Id . fmap f
(2) traverse (Comp . fmap f . g) = Comp . fmap (traverse f) . traverse g

Which means:
(1) => traverse in the Id A.F. is essentially just fmap
(2) => provides a fusion rule for sequential composition of 2 traversals
(2) => traverse (f <.> g) = traverse f <.> traverse g
-}

-- 5.3 Idiomatic naturality

{-
| Preserving Purity Law

| This definition of traverse in which the two children are swapped on traversal
  breaks the Purity Law.

instance Traversable Tree where
  traverse f (Leaf x)  = pure Leaf <*> f x
  traverse f (Bin l r) = pure Bin <*> traverse f r <*> traverse f l

| This definition of traverse doesn't break the Purity Law. The two children are
  swapped on traversal but the 'Bin' operater is flipped to compensate. The
  effect of the reversal is that the elements of the tree are traversed from
  right to left.

instance Traversable Tree where
  traverse f (Leaf x)  = pure Leaf <*> f x
  traverse f (Bin l r) = pure (flip Bin) <*> traverse f r <*> traverse f l

| Consequence of naturality
traverse (f <&> g) == traverse f <&> traverse g

| Btw, we can use 'Backwards' to achieve the same reversed traversal.
-}


-- 5.4 Seqential composition of monadic traversals

(<=<) :: Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
(<=<) f g x = g x >>= (f)


(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
(>=>) = flip (<=<)

{-
| The monad m is commutative if for all mx and my
do {x <- mx; y <- my; return (x, y)} == do { y <- my; x <- mx; return (x, y)}

f :: b -> m c
g :: a -> m b
traverse f <=< traverse g = traverse (f <=< g)

 => join . Comp == (>>= id) . Comp :: Comp m m -> m
-}
update1 :: a -> State Integer a
update1 x = get >>= (\i -> put (i*2) >>= (\_ -> return x))

update2 :: a -> State Integer a
update2 x = get >>= (\i -> put (i+1) >>= (\_ -> return x))


instance Applicative (State s) where
  pure a  = State(\s -> (a, s))
  sf <*> sa = State(\s -> let (g, s') = runState sf s
                              (a, s'') = runState sa s'
                 in (g a, s''))

monadic1 :: Traversable t => t a -> State Integer (t a)
monadic1 = traverse update1 <=< traverse update2

monadic2 :: Traversable t => t a -> State Integer (t a)
monadic2 = traverse (update1 <=< update2)

applicative1 :: Traversable t => t a -> Comp (State Integer) (State Integer) (t a)
applicative1 = traverse update1 <.> traverse update2

applicative2 :: Traversable t => t a -> Comp (State Integer) (State Integer) (t a)
applicative2 = traverse (update1 <.> update2)

{-
| update1 and update2 don't commute. So monadic1 != monadic2 in general.
  Nevertheless applicative1= == applicative2.

| The only advantage of the monadic law it the number of levels (1 level of
  monad vs 2 levels of A.F.)
-}

{-
how to use :
> runState (fmap (flip runState 2) $ unComp $ applicative1 [0]) 2
> (([0], 4), 3)

> runState (fmap (flip runState 1) $ unComp $ applicative1 [0, 0]) 1
> (([0], 4), 3)
-}

-- 5.5 No duplication of elements

-- Satisfies purity but behaves strangely
weirdTraverse :: Applicative m => (a -> m b) -> [a] -> m [b]
weirdTraverse f [] = pure []
weirdTraverse f (x:xs) = pure (const (:)) <*> f x <*> f x <*> weirdTraverse f xs

index :: Traversable t => t a -> (t Integer, Integer)
index xs = run label xs 0

-- if Traversable for list is defined with weirdTraverse, then
-- index "abc" == (ys,6) and runContents ys == [1, 1, 3, 3, 5, 5]

-- 6 MODULAR PROGRAMING WITH APPLICATIVE FUNCTORS

-- 6.1 An example: wordcount

-- 6.2 Modular iterations idiomatically

-- instance Functor [] where
--   fmap f [] = []
--   fmap f (x:xs) = f x : fmap f xs
instance Traversable [] where
  traverse f [] = pure []
  traverse f (x:xs) = pure (:) <*> f x <*> traverse f xs

-- Integer as Monoid-af
-- Reminder 3.2 : Const a is an A.F iff a is a monoid
-- Integer is not an ovious monoid because you can have (0,+) or (1,*)
-- type Count = Const (Sum Integer)
type Count = Const (Sum Integer)

count :: Integer -> Count b
count n = Const (Sum n)

-- Count Character Idiomatically
cciBody :: Char -> Count a
cciBody _ = count 1

cci :: String -> Count [a]
cci = traverse cciBody

test :: Bool -> Integer
test b = if b then 1 else 0

lciBody :: Char -> Count a
lciBody c = count $ test ('\n' == c)

lci :: String -> Count [a]
lci = traverse lciBody

wciBody :: Char -> Comp (M (State Bool)) Count a
wciBody c = up (updateState c)
  where
    updateState :: Char -> Bool -> (Sum Integer, Bool)
    updateState c b = let s = not (isSpace c) in (Sum $ test (not b && s), s)

wci :: String -> Comp (M (State Bool)) Count [a]
wci = traverse wciBody

runWci :: String -> Integer
runWci s = getSum $ fst (run wci s False)

clci :: String -> Prod Count Count [a]
-- clci = cci <&> lci -- inefficient
clci = traverse (cciBody <&> lciBody)

clwci :: String -> Prod (Prod Count Count) (Comp (M (State Bool)) Count) [a]
clwci = traverse (cciBody <&> lciBody <&> wciBody)

runCclwi :: String -> (Integer, Integer, Integer)
runCclwi s = uncurry f (run clwci s)
  where
    f (Sum cc, Sum lc) wcs = (cc, lc, getSum . fst $ wcs False)

-- Note: character and line-counting are monoidal,whereas word-counting is monadic

-- Next is an experiment using a Naperian A.F.
-- Goal: Determine if the distribution of the letters 'q' and 'u' in a text are correlated.

newtype Pair a = P (a, a) deriving Show

instance Functor Pair where
  fmap f (P (x, x')) = P(f x, f x')

instance Applicative Pair where
  pure x = P (x, x)
  P (f, f') <*> P (x, x') = P (f x, f' x)

quiBody :: Char -> Pair Bool
quiBody c = P (c == 'q', c == 'u')

quiString :: String -> Pair [Bool]
quiString = traverse quiBody

ccqui :: String -> (Prod Count Pair) [Bool]
ccqui = traverse (cciBody <&> quiBody)

type WordCount = Comp (M (State Bool)) Count

wcqui :: String -> (Prod Pair WordCount) [Bool]
wcqui = traverse (quiBody <&> wciBody)

wcqui' :: String -> (Comp (Prod Id WordCount) Pair) [Bool]
wcqui' = traverse (quiBody <.> (Id <&> wciBody))
