{-# LANGUAGE FlexibleInstances, TupleSections #-}
module Golforth where

import Control.Arrow

f0 = flip (,)
f1 :: (a -> b) -> ((z,a) -> (z,b))
f1 = second
f2 k ~((z,a),b) = (z, k a b)
f3 k ~(((z,a),b),c) = (z, k a b c)
f4 k ~((((z,a),b),c),d) = (z, k a b c d)
f5 k ~(((((z,a),b),c),d),e) = (z, k a b c d e)
f6 k ~((((((z,a),b),c),d),e),f) = (z, k a b c d e f)
f7 k ~(((((((z,a),b),c),d),e),f),g) = (z, k a b c d e f g)

c0 w = snd . w $ ()
c1 w a = snd . w . (,a) $ ()
c2 w a b = snd . w . (,b) . (,a) $ ()
c3 w a b c = snd . w . (,c) . (,b) . (,a) $ ()

qu = f0

r0 w = fst . w
r1 w = w
r2 w s = case w s of ~(z,(a,b)) -> ((z,a),b)

p0 = (>>> qu ())
p1 = id
p2 = (>>> f2 (,))

plus = f2 (+)
minus = f2 (-)
times = f2 (*)
divide = f2 div
modulus = f2 mod
eudiv = r2 (f2 divMod)
pair = f2 (,)
cons = f2 (flip (:))
uncons (z,(x:xs)) = ((z,xs),x)
empty ~s@(z,xs) = (s,null xs)
fi (((z,b),t),e) = if b then t z else e z

pop = fst

-- this should really be f1'd but ... it's easier to use in haskell this way
dip :: (a -> b) -> ((a,c) -> (b,c))
dip = first

swap ~((z,a),b) = ((z,b),a)
dup ~(z,a) = ((z,a),a)

apply ~(z,f) = f z

eumul = dip swap >>> times >>> plus

-- same comment as dip
red f = dup >>> dip f
