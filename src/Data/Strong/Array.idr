module Data.Strong.Array

import public Data.IOArray.Prims
import Data.Nat

import Control.Monad.Identity
import Data.Zippable

import public Numeric.Floating

--------------------------------------------------

-- No good reason to hide the constructor just yet, safety can come later on
public export
data Array : Nat -> Type -> Type where
  MkArray : (size : Nat) -> (intSize : Int) -> (content : ArrayData a) -> Array size a

-- 0 so I don't have to remember where to erase it
0 lteReflexive : (j : Nat) -> LTE j j
lteReflexive j = reflexive {x=j}

export
size : Array s a -> Nat
size (MkArray s' intSize content) = s'

export
intSize : Array s a -> Int
intSize (MkArray s intSize' content) = intSize'

content : Array s a -> ArrayData a
content (MkArray s intSize c) = c

--------------------------------------------------

export
newArray : (s : Nat) -> (def : a) -> Array s a
newArray s x = unsafePerformIO $ do
    let intsize = cast s
    pure (MkArray s intsize !(primIO (prim__newArray intsize x)))

-- Consider relegating new array construction to ST, requiring a 'freeze' to say
-- we're done making it. This would make the mutable* methods below unneccesary
-- and we could remove them from public facing. I don't want to be that strict
-- until we have fusion though.
export
%inline
newArray' : {s:_} -> (def : a) -> Array s a
newArray' = newArray s

export
%inline
newUnintializedArray : (s : Nat) -> Array s a
newUnintializedArray s = newArray s (believe_me (the Int 0))

export
%inline
newUnintializedArray' : {s : Nat} -> Array s a
newUnintializedArray' = newUnintializedArray s

export
||| You shouldn't need this yourself, other operations use this.
newArrayCopy : Array s a -> Array s a
newArrayCopy (MkArray s i contents) = unsafePerformIO $ do
    let new = newUnintializedArray s
    copyFrom contents (content new) (i - 1)
    pure new
  where
    copyFrom : ArrayData elem ->
               ArrayData elem ->
               Int -> IO ()
    copyFrom old new pos
        = if pos < 0
             then pure ()
             else do el <- primIO $ prim__arrayGet old pos
                     primIO $ prim__arraySet new pos el
                     copyFrom old new $ assert_smaller pos (pos - 1)

--------------------------------------------------

export
||| This won't always be here
unsafeMutableWriteArray : HasIO io => Array s a -> (i : Nat) -> a -> io ()
unsafeMutableWriteArray arr i x = primIO (prim__arraySet (content arr) (cast i) x)

-- Consider an interface based on Int and So as an alternative.
export
%inline
||| This won't always be here
mutableWriteArray : HasIO io => Array s a -> (i : Nat) -> (0 prf : LTE i s) => a -> io ()
mutableWriteArray arr i x = unsafeMutableWriteArray arr i x

export
||| Don't use this unless you really just have one infrequent thing to change,
||| unsafeWriteArray copies the array every use.
unsafeWriteArray : Array s a -> (i : Nat) -> a -> Array s a
unsafeWriteArray arr i x = unsafePerformIO $ do
  let new = newArrayCopy arr
  unsafeMutableWriteArray new i x
  pure new

export
%inline
||| Don't use this unless you really just have one infrequent thing to change,
||| writeArray copies the array every use.
writeArray : Array s a -> (i : Nat) -> (0 prf : LTE i s) => a -> Array s a
writeArray arr i x = unsafeWriteArray arr i x

--------------------------------------------------

export
||| To match with unsafeMutableWriteArray in that it has io for
||| ordering ease-of-use.
unsafeMutableReadArray : HasIO io => Array s a -> (i : Nat) -> io a
unsafeMutableReadArray arr i = primIO (prim__arrayGet (content arr) (cast i))

export
unsafeReadArray : Array s a -> (i : Nat) -> a
unsafeReadArray arr i = unsafePerformIO $ unsafeMutableReadArray arr i

export
%inline
||| To match with unsafeMutableWriteArray in that it has io for
||| ordering ease-of-use, 'mutable' in name only.
mutableReadArray : HasIO io => Array s a -> (i : Nat) -> (0 prf : LTE i s) => io a
mutableReadArray arr i = unsafeMutableReadArray arr i

export
%inline
readArray : Array s a -> (i : Nat) -> (0 prf : LTE i s) => a
readArray arr i = unsafeReadArray arr i

--------------------------------------------------

export
||| Same caveat as writeArray
modifyArray : (a -> a) -> Array s a -> (i : Nat) -> LTE i s => Array s a
modifyArray f arr i = writeArray arr i (f (readArray arr i))

-- Keeping this around for now, Applicative version does the same job, but I'm
-- a little unsure about how I've written its `go`
export
imapArrayM' : Monad m => ((i : Nat) -> a -> m b) -> Array s a -> m (Array s b)
imapArrayM' f arr = case arr of
    MkArray s _ _ => do
      let new = newUnintializedArray {a=b} s
      let 0 prf = lteReflexive s
      go new s
  where
    go : Array s b -> (i : Nat) -> (0 prf : LTE i s) => m (Array s b)
    go new 0 = pure new
    go new (S k) = do
      let 0 newprf = lteSuccLeft prf
      let v = readArray arr k
      r <- f k v
      let () = unsafePerformIO $ mutableWriteArray new k r
      go new k

export
imapArrayM : Applicative f => ((i : Nat) -> a -> f b) -> Array s a -> f (Array s b)
imapArrayM g arr = case arr of
    MkArray s _ _ =>
      let new = newUnintializedArray {a=b} s
          0 prf = lteReflexive s
      in  go new s
  where
    go : Array s b -> (i : Nat) -> (0 prf : LTE i s) => f (Array s b)
    go new 0 = pure new
    go new (S k) =
      let 0 newprf = lteSuccLeft prf
          v = readArray arr k
          r = g k v
      in (\b => let () = unsafePerformIO $ mutableWriteArray new k b in id) <$> r <*> go new k

export
%inline
imapArray : ((i : Nat) -> a -> b) -> Array s a -> Array s b
imapArray f arr = runIdentity $ imapArrayM (Id .: f) arr

-- extra copy, but easy to write
export
%inline
inewArrayFillM : Monad m => (s : Nat) -> ((i : Nat) -> m a) -> m (Array s a)
inewArrayFillM s g = imapArrayM (\i,_ => g i) (newUnintializedArray {a} s)

export
%inline
inewArrayFill : (s : Nat) -> ((i : Nat) -> a) -> Array s a
inewArrayFill s g = runIdentity $ imapArrayM (\i,_ => Id (g i)) (newUnintializedArray {a} s)

-- this isn't really foldl, it's foldr but just reading the array in reverse, this should
-- be changed in the future so it's not surprising.
ifoldlArray : (b -> (i : Nat) -> a -> b) -> b -> Array s a -> b
ifoldlArray f acc arr = case arr of
    MkArray s _ _ => let 0 prf = lteReflexive s in go s
  where
    go : (i : Nat) -> (0 prf : LTE i s) => b
    go 0 = acc
    go (S k) =
      let 0 newprf = lteSuccLeft prf
      in f (go k) k (readArray arr k)

export
||| I expect this will dissapear from the api once fusion exists
ifoldl2Array : (b -> (i1,i2 : Nat) -> a -> a -> b) -> b -> Array s a -> Array s a -> b
ifoldl2Array f acc arr1 arr2 = case arr1 of
    MkArray s _ _ => let 0 prf = lteReflexive s in go s
  where
    go : (i : Nat) -> (0 prf : LTE i s) => b
    go 0 = acc
    go (S k) = let 0 p = lteSuccLeft prf in f (go k) k k (readArray arr1 k) (readArray arr2 k)

export
%inline
foldlArray : (b -> a -> b) -> b -> Array s a -> b
foldlArray f = ifoldlArray (\acc,_,x => f acc x)

export
%inline
||| I expect this will dissapear from the api once fusion exists
foldl2Array : (b -> a -> a -> b) -> b -> Array s a -> Array s a -> b
foldl2Array f = ifoldl2Array (\acc,_,_,x,y => f acc x y)

-- bleh, see ifoldlArray note above
-- exported via Foldable
%inline
foldrArray : (a -> b -> b) -> b -> Array s a -> b
foldrArray f = foldlArray (flip f)

export
%inline
mapArray : (a -> b) -> Array s a -> Array s b
mapArray f arr = imapArray (\_,x => f x) arr

export
zipWithArray : (a -> b -> c) -> Array s a -> Array s b -> Array s c
zipWithArray f arr1 arr2 = case arr1 of
    MkArray s _ _ =>
      let new = newUnintializedArray {a=c} s
          0 prf = lteReflexive s
      in  go new s
  where
    go : Array s c -> (i : Nat) -> (0 prf : LTE i s) => Array s c
    go new 0 = new
    go new (S k) =
      let 0 newprf = lteSuccLeft prf
          v1 = readArray arr1 k
          v2 = readArray arr2 k
          () = unsafePerformIO $ mutableWriteArray new k (f v1 v2)
      in  go new k

export
Functor (Array s) where
  map = mapArray

-- do we really want this?
export
{s:_} -> Applicative (Array s) where
  pure a = newArray' a
  f <*> fa = zipWithArray (\f,x => f x) f fa

-- exported via Foldable
toList : Array s a -> List a
toList xs = foldlArray (\b,a => b . (a ::)) id xs []

-- TODO: toVect, to delistify while preserving size

export
fromList : (xs : List a) -> Array (length xs) a
fromList xs with (length xs)
  fromList xs | s =
      let new = newUnintializedArray {a} s
      in  go new xs 0
  where -- this used mutableWriteArray to prove
    go : Array s a -> (xs : List a) -> (i : Nat) -> Array s a
    go new (x :: xs) k =
      let () = unsafePerformIO $ unsafeMutableWriteArray new k x
      in  go new xs (S k)
    go new _ _ = new

export
fromList' : (xs : List a) -> (s : Nat ** Array s a)
fromList' xs =
    let s = length xs
        new = newUnintializedArray {a} s
    in  (s ** go new xs 0)
  where -- this used mutableWriteArray to prove
    go : Array s a -> (xs : List a) -> (i : Nat) -> Array s a
    go new (x :: xs) k =
      let () = unsafePerformIO $ unsafeMutableWriteArray new k x
      in  go new xs (S k)
    go new _ _ = new

-- TODO: fromVect, to listify while preserving size

export
Show a => Show (Array s a) where
  showPrec p x = showCon p "fromList" (showArg (Array.toList x))

export
sumArray : Num a => Array s a -> a
sumArray = foldlArray (+) 0

-- The quintessential example for where you'd want fusion, but we don't have it yet.
export
dotArray : Num a => Array s a -> Array s a -> a
dotArray a b = sumArray (zipWithArray (*) a b)

------------ Foldable ------------

export
Foldable (Array s) where
  foldr = foldrArray
  toList = Array.toList

------------ Traversable ------------

export
Traversable (Array s) where
  traverse f = imapArrayM (\_,x => f x)

------------ Semigroup / Monoid ------------

export
Semigroup a => Semigroup (Array s a) where
  a <+> b = zipWithArray (<+>) a b

export
{s:_} -> Monoid a => Monoid (Array s a) where
  neutral = newArray' neutral

------------ Cast ------------

export
Cast a b => Cast (Array s a) (Array s b) where
  cast = mapArray cast

------------ FromString ------------

||| :exec printLn $ the (s ** Array s Char) "abcde"
||| (5 ** fromList ['a', 'b', 'c', 'd', 'e'])
||| :exec printLn $ the (s ** Array s Bits8) "abcde"
||| (5 ** fromList [97, 98, 99, 100, 101])
||| :exec printLn $ snd $ the (s ** Array s Bits8) "abcde"
||| fromList [97, 98, 99, 100, 101]
export
Cast Char a => FromString (s ** Array s a) where
  fromString str = let (s ** arr) = fromList' (unpack str) in (s ** cast arr)

------------ Eq ------------

export
Eq a => Eq (Array s a) where
  x == y = foldl2Array (\b,x,y => x == y && b) True x y

------------ Ord ------------

export
Ord a => Ord (Array s a) where
  compare x y = foldl2Array (\b,x,y => compare x y <+> b) neutral x y


--------------------------------------------------
-- Forcing particular operations into these numerical interfaces makes
-- over-restrictive functions, e.g. fromInteger forces us to create a specific
-- array, requiring us to know what 's' is, but + and * don't need this
-- restriction since things like zipWith rediscovers what `s` was via pattern
-- matching. We thus provide the operations below without an accompanying
-- interface.
--------------------------------------------------
-- These interfaces are provided in Data.Strong.Array.Interfaces
--------------------------------------------------

------------ Num ------------

export
%inline
(+) : Num a => Array s a -> Array s a -> Array s a
x + y = zipWithArray (+) x y

export
%inline
(*) : Num a => Array s a -> Array s a -> Array s a
x * y = zipWithArray (*) x y

export
%inline
fromInteger : {s:_} -> Num a => Integer -> Array s a
fromInteger x = newArray' (fromInteger x)

------------ FromDouble ------------

export
%inline
fromDouble : {s : _} -> FromDouble a => Double -> Array s a
fromDouble x = newArray' (fromDouble x)

------------ Neg ------------

export
%inline
negate : Neg a => Array s a -> Array s a
negate = mapArray negate

export
%inline
(-) : Neg a => Array s a -> Array s a -> Array s a
x - y = zipWithArray (-) x y

------------ Abs ------------

export
%inline
abs : Abs a => Array s a -> Array s a
abs = mapArray abs

------------ Fractional ------------

export
%inline
(/) : Fractional a => Array s a -> Array s a -> Array s a
x / y = zipWithArray (/) x y
-- recip : Fractional a => Array s a -> Array s a

------------ Integral ------------

export
%inline
div : Integral a => Array s a -> Array s a -> Array s a
div x y = zipWithArray div x y

export
%inline
mod : Integral a => Array s a -> Array s a -> Array s a
mod x y = zipWithArray mod x y

------------ Floating ------------

export
%inline
exp : Floating a => Array s a -> Array s a
exp x = mapArray exp x

export
%inline
pi : {s:_} -> Floating a => Array s a
pi = newArray' pi

export
%inline
euler : {s:_} -> Floating a => Array s a
euler = newArray' euler

export
%inline
log : Floating a => Array s a -> Array s a
log x = mapArray log x

export
%inline
pow : Floating a => Array s a -> Array s a -> Array s a
pow x y = zipWithArray pow x y

export
%inline
sin : Floating a => Array s a -> Array s a
sin x = mapArray sin x

export
%inline
cos : Floating a => Array s a -> Array s a
cos x = mapArray cos x

export
%inline
tan : Floating a => Array s a -> Array s a
tan x = mapArray tan x

export
%inline
asin : Floating a => Array s a -> Array s a
asin x = mapArray asin x

export
%inline
acos : Floating a => Array s a -> Array s a
acos x = mapArray acos x

export
%inline
atan : Floating a => Array s a -> Array s a
atan x = mapArray atan x

export
%inline
sinh : Floating a => Array s a -> Array s a
sinh x = mapArray sinh x

export
%inline
cosh : Floating a => Array s a -> Array s a
cosh x = mapArray cosh x

export
%inline
tanh : Floating a => Array s a -> Array s a
tanh x = mapArray tanh x

export
%inline
sqrt : Floating a => Array s a -> Array s a
sqrt x = mapArray sqrt x

export
%inline
floor : Array s Double -> Array s Double
floor x = mapArray floor x

export
%inline
ceiling : Array s Double -> Array s Double
ceiling x = mapArray ceiling x


------------ Zippable ------------

export
%inline
zipWith : (a -> b -> c) -> Array s a -> Array s b -> Array s c
zipWith = zipWithArray

export
%inline
||| pretty wasteful array copying here, probably best to avod until we have fusion
zipWith3 : (a -> b -> c -> d) -> Array s a -> Array s b -> Array s c -> Array s d
zipWith3 f x y z = zipWithArray (\f',x' => f' x') (zipWithArray f x y) z

export
unzipWith : (f : a -> (b, c)) -> Array s a -> (Array s b, Array s c)
unzipWith f arr = case arr of
    MkArray s _ _ =>
      let new1 = newUnintializedArray s
          new2 = newUnintializedArray s
          () = ifoldlArray (\_,i,x' => unsafePerformIO $ do
                 let (x,y) = f x'
                 unsafeMutableWriteArray new1 i x
                 unsafeMutableWriteArray new2 i y) () arr
          in (new1,new2)

export
unzipWith3 : (func : a -> (b, c, d)) -> Array s a -> (Array s b, Array s c, Array s d)
unzipWith3 f arr = case arr of
    MkArray s _ _ =>
      let new1 = newUnintializedArray s
          new2 = newUnintializedArray s
          new3 = newUnintializedArray s
          () = ifoldlArray (\_,i,x' => unsafePerformIO $ do
                 let (x,y,z) = f x'
                 unsafeMutableWriteArray new1 i x
                 unsafeMutableWriteArray new2 i y
                 unsafeMutableWriteArray new3 i z) () arr
          in (new1,new2,new3)

export
Zippable (Array s) where
  zipWith = Array.zipWith
  zipWith3 = Array.zipWith3
  unzipWith = Array.unzipWith
  unzipWith3 = Array.unzipWith3
