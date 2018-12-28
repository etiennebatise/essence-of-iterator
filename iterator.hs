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
  -- fmap id = id -- identity
  -- fmap (f . g) = fmap f . fmap g -- composition
  fmap :: (a -> b) -> f a -> f b

class Main.Functor m => Monad m where
  -- should satisfy these laws:
  -- return a >>= f = f a -- left unit
  -- mx >>= return = mx -- right unit
  -- (mx >>= f) >>= g = mx >>= (\x -> f x >>= g) -- associativity
  (>>=) :: m a -> (a -> m b) -> m b
  return :: a -> m a

-- 3. APPLICATIVE FUNCTORS

class Main.Functor m => Applicative m where
  pure :: a -> m a
  (<*>) :: m (a -> b) -> m a -> m b
