-- 2 FUNCTIONNAL ITERATION
-- 2.1 Origami

class Bifunctor s where
  -- Should satisfy :
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
