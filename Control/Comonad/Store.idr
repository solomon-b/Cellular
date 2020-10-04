module Control.Comonad.Store

import Interfaces.Verified
import Control.Comonad

--cong : {f : t -> u} -> (a = b) -> f a = f b
cong2 : {f : t -> u -> v} -> (a1 = a2) -> b1 = b2 -> f a1 b1 = f a2 b2
cong2 Refl Refl = Refl

funext : (f, g : a -> b) -> ((x : a) -> f x = g x) -> f = g
funext f g = believe_me

interface Comonad w => VerifiedComonad (w : Type -> Type) where
--extend extract = id
  extendExtractId :
    {a : Type} ->
    (wa : w a) ->
    extend Comonad.extract wa = wa
--extract . extend f  = f
  extractExtendF :
    {a, b : Type} ->
    (wa : w a) ->
    (x : b) ->
    (f : w a -> b) ->
    (Comonad.extract . extend f) wa = x
--extend f . extend g = extend (f . extend g)
  extendExtend :
    {a, b, c : Type} ->
    (wa : w a) ->
    (g : w a -> b) ->
    (f : w b -> c) ->
    (extend f . extend g) wa = extend (f . extend g) wa

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
  --extend f (Store' g s) = Store' (\s' => f (Store' g s')) s

VerifiedComonad (Store s) where
  extendExtractId (Store' f x) = Refl
  extractExtendF (Store' g y) b f = ?hole
  extendExtend (Store' x y) g f = Refl

export
pos : Store s a -> s
pos (Store' f s) = s

export
peek : s -> Store s a -> a
peek s (Store' f s') = f s

export
peeks : (s -> s) -> Store s a -> a
peeks f (Store' g s) = g $ f s

export
seek : s -> Store s a -> Store s a
seek s (Store' f _) = Store' f s

export
seeks : (s -> s) -> Store s a -> Store s a
seeks f (Store' g s) = Store' g (f s)

export
experiment : Functor f => (s -> f s) -> Store s a -> f a
experiment f (Store' g s) = g <$> f s



-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
