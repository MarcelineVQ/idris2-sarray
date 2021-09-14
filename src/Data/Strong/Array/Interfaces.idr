module Data.Strong.Array.Interfaces

import Data.Strong.Array
import Numeric.Floating

-- Separated interfaces due to needing `{s:_} ->` everywhere

export
{s:_} -> Num a => Num (Array s a) where
  (+) = Array.(+)
  (*) = Array.(*)
  fromInteger = Array.fromInteger

export
{s:_} -> FromDouble a => FromDouble (Array s a) where
  fromDouble = Array.fromDouble

export
{s:_} -> Neg a => Neg (Array s a) where
  (-) = Array.(-)
  negate = Array.negate

export
{s:_} -> Abs a => Abs (Array s a) where
  abs = Array.abs

export
{s:_} -> Fractional a => Fractional (Array s a) where
  (/) = Array.(/)
  recip x = 1 / x -- Get a weird error if I don't supply this myself

export
{s:_} -> Integral a => Integral (Array s a) where
  div = Array.div
  mod = Array.mod

export
{s:_} -> Floating a => Floating (Array s a) where
  pi = Array.pi
  euler = Array.euler
  exp = Array.exp
  log = Array.log
  pow = Array.pow
  sin = Array.sin
  cos = Array.cos
  tan = Array.tan
  asin = Array.asin
  acos = Array.acos
  atan = Array.atan
  sinh = Array.sinh
  cosh = Array.cosh
  tanh = Array.tanh
  sqrt = Array.sqrt
