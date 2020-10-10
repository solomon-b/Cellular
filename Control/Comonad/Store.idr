module Control.Comonad.Store

import Syntax.PreorderReasoning
import Interfaces.Verified
import Control.Comonad

cong2 : {f : t -> u -> v} -> (a1 = a2) -> b1 = b2 -> f a1 b1 = f a2 b2
cong2 Refl Refl = Refl

funext : (f, g : a -> b) -> ((x : a) -> f x = g x) -> f = g
funext f g = believe_me

public export
data Store : Type -> Type -> Type where
  Store' : (s -> a) -> s -> Store s a

export
Functor (Store s) where
  map g (Store' f s) = Store' (\s' => g (f s')) s

VerifiedFunctor (Store s) where
  functorIdentity g p (Store' f x) = cong2 {f = Store'} (funext (g . f) f (\x => p (f x))) Refl
  functorComposition (Store' f x) g1 g2 = cong2 {f = Store'} Refl Refl

export
Comonad (Store s) where
  extract (Store' f s) = f s
  duplicate (Store' f s) = Store' (Store' f) s
  extend f (Store' g s) = Store' (\s' => f (Store' g s')) s

VerifiedComonad (Store s) where
  extendExtractId (Store' f x) = Refl
  extractExtendF (Store' g y) f = Refl
  extendExtend (Store' x y) g f = Refl

export
pos : Store s a -> s
pos (Store' f s) = s

export
peek : s -> Store s a -> a
peek s (Store' f s') = f s

-- peek x . extend (peek y) = peek y
peekExtendLaw :
  {s, a : Type} ->
  (x, y : s) ->
  (store : Store s a) ->
  peek x ((extend (peek y)) store) = peek y store
peekExtendLaw x y (Store' f z) = Refl

export
peeks : (s -> s) -> Store s a -> a
peeks f (Store' g s) = g $ f s

export
seek : s -> Store s a -> Store s a
seek s (Store' f _) = Store' f s

-- seek s = peek s . duplicate
seekDuplicateLaw :
  {s, a : Type} ->
  (s' : s) ->
 (store : Store s a) ->
  seek s' store = peek s' (duplicate store)
seekDuplicateLaw s' (Store' f x) = Refl

export
seeks : (s -> s) -> Store s a -> Store s a
seeks f (Store' g s) = Store' g (f s)

--seeks f = peeks f . duplicate
seeksDuplicateLaw :
  {s, a : Type} ->
  (f : s -> s) ->
  (store : Store s a) ->
  seeks f store = peeks f (duplicate store)
seeksDuplicateLaw f (Store' g x) = Refl

export
experiment : Functor f => (s -> f s) -> Store s a -> f a
experiment f w = map (`peek` w) (f (pos w))

-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
