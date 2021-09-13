module Data.Strong.Array.Fusion

import Data.Strong.Array

import Language.Reflection

-- import public Language.Reflection.Pretty
-- import public Language.Reflection.Syntax
-- import public Language.Reflection.Types
-- 
-- import public Text.PrettyPrint.Prettyprinter
-- 
-- -- import Generics.Derive
%language ElabReflection



-- I can get elab to inline and fuse for me but not quite as
-- nicely/automatically as I prefer so far, work continues.




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
-- stream arr = case arr of
    -- MkArray s _ _ => MkStream step 0 s
  -- where
    -- step : Int -> Step Int a
    -- step s = if s >= intSize arr
      -- then Done
      -- else Yield (unsafeReadArray arr (cast s)) (s+1)

unstream : Stream n a -> Array n a

-- %transform "what" Prelude.(.) = Fusion.gop

mapS : (a -> b) -> Stream n a -> Stream n b
mapS f (MkStream step s i) = MkStream (\s' => case step s' of
  (Yield x y) => Yield (f x) y
  (Skip x) => Skip x
  Done => Done) s i

-- braf : Elab ((b -> c) -> (a -> b) -> (a -> c))


-- I just want this to wrap in stream/unstream
-- export
-- streamWrap : (Stream a -> Stream b) -> Array s a -> Elab (Array s a -> Array s b)
-- streamWrap f arr = pure (newUnintializedArray 2)

-- %macro
-- streamWrap : {s,n,a,b:_} -> (Stream n a -> Stream n b) -> Elab (Array s a -> Array s b)
-- streamWrap f = do
--   r <- quote f
--   check `(unstream . ~r . stream)

-- %macro
-- map' : {s,a,b:_} -> (a -> b) -> Elab (Array s a -> Array s b)
-- map' f = do
--   r <- quote f
--   check `(unstream . mapS ~r . stream)

-- `(stream (unstream ~x))
spider : TTImp -> TTImp
spider `(stream (unstream ~x)) = spider x
spider (IPi x y z w argTy retTy) = IPi x y z w (spider argTy) (spider retTy)
spider (ILam x y z w argTy lamTy) = (ILam x y z w (spider argTy) (spider lamTy))
spider (ILet x lhsFC y z nTy nVal scope) = (ILet x lhsFC y z (spider  nTy) (spider nVal) (spider scope))
spider (ICase x y ty xs) = (ICase x y (spider ty) xs) -- do clauses?
spider (ILocal x xs y) = (ILocal x xs (spider y)) -- do decls?
spider (IUpdate x xs y) = (IUpdate x xs (spider y))
spider `(Data.Strong.Array.Fusion.stream {a = _} {n = _} (Data.Strong.Array.Fusion.unstream {a = _} {n = _} ~x)) = x
spider (INamedApp x y z w) = (INamedApp x (spider y) z (spider w))
spider (IApp x y z) = (IApp x (spider y) (spider z))
spider (IAutoApp x y z) = (IAutoApp x (spider y) (spider z))
spider (IWithApp x y z) = (IWithApp x (spider y) (spider z))
spider (IAlternative x y xs) = (IAlternative x y (map spider xs))
spider (IRewrite x y z) = (IRewrite x (spider y) (spider z))
spider (IBindHere x y z) = (IBindHere x y (spider z))
spider (IAs x nameFC y z w) = (IAs x nameFC y z (spider w))
spider (IMustUnify x y z) = (IMustUnify x y (spider z))
spider (IDelayed x y z) = (IDelayed x y (spider z))
spider (IDelay x y) = (IDelay x (spider y))
spider (IForce x y) = (IForce x (spider y))
spider (IQuote x y) = (IQuote x (spider y))
spider (IUnquote x y) = (IUnquote x (spider y))
spider (IWithUnambigNames x xs y) = (IWithUnambigNames x xs (spider y))
spider x = x 
 
infixr 9 `dot`

-- fuse : x -> x
-- fuse x = %runElab do
--   r <- quote x
--   logTerm "" 1 "faf" r
--   check (spider r)

infixr 9 `dott`

%macro
dott : {c:_} -> (b -> c) -> (a -> b) -> Elab (a -> c)
dott f g  = lambda _ $ \x => do
  -- let r = g x
  -- let r' = f r
  -- d <- quote r
  -- `(Data.Strong.Array.Fusion.stream {a = _} {n = _} (Data.Strong.Array.Fusion.unstream {a = _} {n = _} ~y)) <- quote r
    -- | _ => pure r'
  -- _ <- check d
  pure (f (g x))
  -- ?dfdf

-- %transform "stream fusion1" Fusion.stream . Fusion.unstream = Prelude.id

-- %macro
-- dot : {c:_} -> (b -> c) -> (a -> b) -> a -> Elab c
-- dot f g x = do
--   r <- quote (f (g x))
--   check (spider r)

%macro
map' : (a -> b) -> Elab (Array s a -> Array s b)
map' f = lambda _ $ \x => pure $ unstream (mapS f (stream x))

-- %macro
-- streamWrap : {s,a,b:_} -> (Stream s a -> Stream s b) -> Elab (Array s a -> Array s b)
-- streamWrap f = lambda _ $ \x => pure $ unstream (f (stream x))

-- map' : (a -> b) -> Array s a -> Array s b
-- map' f = streamWrap (mapS f)
 
-- %inline
-- map' : (a -> b) -> Array s a -> Array s b
-- map' f = unstream `dot` mapS f `dot` stream
 
export
blar : Array s Double -> Array s Double
blar = map' {s} (Prelude.(+) 1.0) `dott` map' (Prelude.(+) 2.0) `dott` Prelude.id
 
 
-- export
-- blar : Array s Double -> Array s Double
-- blar arr =
--   let f = map' {s} (Prelude.(+) 1.0) `dott` map' (Prelude.(+) 2.0) `dott` id
--   in %runElab do
--     z <- quote (f arr)
--     let r = spider z 
--     logTerm "" 1 "wah" r
--     check r
    -- pure z

-- farf : Int -> Int
-- farf = dot (+1) (+1)

-- I need map' to inline before our fusion rule fires so I get the below
-- which the rule should match:
-- ^ unstream . mapS (+1) . stream . unstream . mapS (+2) . stream
-- ^ unstream . (mapS (+1) . (stream . (unstream . (mapS (+2) . stream))))

-- So, how do we unroll map' via elab?


-- (IApp EmptyFC (INamedApp EmptyFC (INamedApp EmptyFC (IVar EmptyFC (NS (MkNS ["Fusion","Array","Strong","Data"]) (UN "stream"))) (UN "a") (IPrimVal EmptyFC DoubleType)) (UN "n") (IHole (MkFC (Virtual Interactive) (0,15) (0, 20)) "s")) (IApp EmptyFC (INamedApp EmptyFC (INamedApp EmptyFC (IVar EmptyFC (NS (MkNS ["Fusion","Array","Strong","Data"]) (UN "unstream"))) (UN "a") (IPrimVal EmptyFC DoubleType)) (UN "n") (IHole (MkFC (Virtual Interactive) (0,15) (0,20)) "s")) (UN "x")

-- (IApp EmptyFC
--   (INamedApp EmptyFC
--     (INamedApp EmptyFC
--       (IVar EmptyFC (NS (MkNS ["Fusion","Array","Strong","Data"]) (UN "stream")))
--       (UN "a")
--       (IPrimVal EmptyFC DoubleType))
--     (UN "n")
--     (IHole "s"))
--   (IApp EmptyFC
--     (INamedApp EmptyFC
--       (INamedApp EmptyFC
--         (IVar EmptyFC (NS (MkNS ["Fusion","Array","Strong","Data"]) (UN "unstream")))
--         (UN "a")
--         (IPrimVal EmptyFC DoubleType))
--       (UN "n")
--       (IHole "s"))

-- (IApp _ (INamedApp _ (INamedApp _ (IVar _ (NS (MkNS ["Fusion","Array","Strong","Data"]) (UN "stream"))) _ _) _ _) (IApp _ (INamedApp _ (INamedApp _ (IVar EmptyFC (NS (MkNS ["Fusion","Array","Strong","Data"]) (UN "unstream"))) _ _) _ _) w))



-- foo : TTImp
-- foo = `( stream . unstream)
-- 
-- spider : TTImp -> TTImp
-- spider `((~f . ~g) ~x) = `(~(spider f) (~(spider g) x))
-- spider r = r
-- 
-- fuse : TTImp -> TTImp
-- fuse `(stream (unstream ~x)) = x
-- fuse r = r

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


-- 
-- dot : (b -> c) -> (a -> b) -> (a -> c)
-- dot f g x = %runElab do
--   z <- quote $ blar {s=1}
--   q <- quote $ Fusion.map' (+1) {a=Int} {b=Int} {s=1}
--   logTerm "" 1 "blar" z
--   logTerm "" 1 "map'" q
--   logTerm "" 1 "spider" $ spider `(unstream . map1 . stream . unstream . map 2 . stream)
--   pure (f (g x))
--   --?sdffd
-- 
-- foo2 : Elab ()
-- foo2 = do
--   ?asSDfsfd

-- %transform "vectStreamFusion3" Fusion.map' f . Fusion.map' g = Fusion.map' (f . g)
 
main : IO ()
-- main = pure ()
main = do
  -- let xvar = nak $ MkStream {a=Int} (\_ => Done) 'a' 1
  printLn (blar $ fromList [1.0,2.0,3.0])
