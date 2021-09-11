module Data.Strong.Array.Fusion

import Data.Strong.Array

import Language.Reflection

-- import Generics.Derive
%language ElabReflection


-- %hide Prelude.Basics.(.)

-- This is probably a lost cause currently, inlining occurs _after_ %transforms
-- so we can't use them to fuse things like blar. Perhaps elaborator reflection
-- can do something, but I'm not sure how far we can get with Check/Quote


data Step : Type -> Type -> Type where
  Yield : a -> s -> Step s a
  Skip : s -> Step s a
  Done : Step s a

data Stream : Nat -> Type -> Type where
  MkStream : (s -> Step s a) -> s -> (n : Nat) -> Stream n a

stream : Array n a -> Stream n a
stream arr = case arr of
    MkArray s _ _ => MkStream step 0 s
  where
    step : Int -> Step Int a
    step s = if s >= intSize arr
      then Done
      else Yield (unsafeReadArray arr (cast s)) (s+1)

-- dot : (b -> c) -> (a -> b) -> (a -> c)
-- dot f g x = f (g x)

unstream : Stream n a -> Array n a
unstream (MkStream step s' max) = inewArrayFill max (\_ => step' s')
  where
    step' : forall s. s -> a

mapS : (a -> b) -> Stream n a -> Stream n b
mapS f (MkStream step s i) = MkStream (\s' => case step s' of
  (Yield x y) => Yield (f x) y
  (Skip x) => Skip x
  Done => Done) s i

-- braf : Elab ((b -> c) -> (a -> b) -> (a -> c))

%inline
export
map' : (f : (a -> b)) -> Array s a -> Array s b
map' f =  unstream . mapS f . stream

-- -- %inline
export  
blar : Array s Double -> Array s Double 
blar = map' (+1) . map' (+2)

foo : TTImp
foo = `( stream . unstream)

spider : TTImp -> TTImp
spider `((~f . ~g) ~x) = `(~(spider f) (~(spider g) x))
spider r = r

fuse : TTImp -> TTImp
fuse `(stream (unstream ~x)) = x
fuse r = r

-- `(unstream . map1 . stream . unstream . map 2 . stream)
-- LOG declare.type:1: Processing Data.Strong.Array.Fusion.14044:1647:it
-- IApp (IApp (IVar (UN ".")) (IVar (UN "unstream"))) (IApp (IApp (IVar (UN ".")) (IVar (UN "map1"))) (IApp (IApp (IVar (UN ".")) (IVar (UN "stream"))) (IApp (IApp (MkFC (Virtual Interactive) (0, 29) (0,
-- 54)) (IVar (MkFC (Virtual Interactive) (0, 38) (0,
-- 39)) (UN ".")) (IVar (MkFC (Virtual Interactive) (0, 29) (0,
-- 37)) (UN "unstream"))) (IApp (MkFC (Virtual Interactive) (0, 40) (0,
-- 54)) (IApp (MkFC (Virtual Interactive) (0, 40) (0,
-- 54)) (IVar (MkFC (Virtual Interactive) (0, 46) (0,
-- 47)) (UN ".")) (IApp (MkFC (Virtual Interactive) (0, 40) (0,
-- 45)) (IVar (MkFC (Virtual Interactive) (0, 40) (0,
-- 43)) (UN "map")) (IApp (MkFC (Virtual Interactive) (0, 44) (0,
-- 45)) (IVar (MkFC (Virtual Interactive) (0, 44) (0,
-- 45)) (UN "fromInteger")) (IPrimVal (MkFC (Virtual Interactive) (0, 44) (0,
-- 45)) (BI 2))))) (IVar (MkFC (Virtual Interactive) (0, 48) (0,
-- 54)) (UN "stream"))))))
-- Data.Strong.Array.Fusion> 



dot : (b -> c) -> (a -> b) -> (a -> c)
dot f g x = %runElab do
  z <- quote $ blar {s=1}
  q <- quote $ Fusion.map' (+1) {a=Int} {b=Int} {s=1}
  logTerm "" 1 "blar" z
  logTerm "" 1 "map'" q
  logTerm "" 1 "spider" $ spider `(unstream . map1 . stream . unstream . map 2 . stream)
  pure (f (g x))
  --?sdffd

foo2 : Elab ()
foo2 = do
  ?asSDfsfd

-- %transform "vectStreamFusion3" Fusion.map' f . Fusion.map' g = Fusion.map' (f . g)
 
main : IO ()
main = pure ()
-- main = do
  -- let xvar = nak $ MkStream {a=Int} (\_ => Done) 'a' 1
  -- printLn (blar $ fromList [1.0,2.0,3.0])
