module Data.Representable.Store

import Control.Comonad
import Data.Representable

public export
data Store : (Type -> Type) -> Type -> Type -> Type where
  MkStore : rep -> (f a) -> Store f rep a

public export
Functor f => Functor (Store f rep) where
  map func (MkStore rep fa) = MkStore rep (map func fa)

public export
Representable f rep => Comonad (Store f rep) where
  extract (MkStore rep fa) = index fa rep
  extend func (MkStore rep' fa) = MkStore rep' (tabulate (\rep'' => func (MkStore rep'' fa)))

export
pos : Store f rep a -> rep
pos (MkStore rep' fa) = rep'

export
peek : Representable f rep => rep -> Store f rep a -> a
peek rep' (MkStore _ fa) = index fa rep'

export
peeks : Representable f rep => (rep -> rep) -> Store f rep a -> a
peeks f (MkStore rep' fa) = index fa (f rep')

export
seek : Representable f rep => rep -> Store f rep a -> Store f rep a
seek rep' (MkStore _ fa) = MkStore rep' fa

export
seeks : Representable f rep => (rep -> rep) -> Store f rep a -> Store f rep a
seeks func (MkStore rep' fa) = MkStore (func rep') fa

export
experiment : (Representable f rep, Functor g) => (rep -> g rep) -> Store f rep a -> g a
experiment f s = map (`peek` s) (f (pos s))
