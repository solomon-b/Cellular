module Control.Comonad

public export
interface Functor w => Comonad (w : Type -> Type) where
  extract : w a -> a
  duplicate : w a -> w (w a)
  duplicate = extend id
  extend : (w a -> b) -> w a -> w b
  extend f = map f . duplicate

infixr 1 =>=
export
(=>=) : Comonad w => (w a -> b) -> (w b -> c) -> w a -> c
(=>=) f g = g . extend f

infixr 1 =<=
export
(=<=) : Comonad w => (w b -> c) -> (w a -> b) -> w a -> c
(=<=) = flip (=>=)

infixr 1 <<=
export
(<<=) : Comonad w => (w a -> b) -> w a -> w b
(<<=) f = extend f

infixr 1 =>>
export
(=>>) : Comonad w => w a -> (w a -> b) -> w b
(=>>) x f = extend f x
