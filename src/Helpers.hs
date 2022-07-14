module Helpers where

{-# INLINE assoc #-}
assoc :: ((a,b),c) -> (a,(b,c))
assoc ~(~(a,b),c) = (a,(b,c))

{-# INLINE cossa #-}
cossa :: (a,(b,c)) -> ((a,b),c)
cossa ~(a,~(b,c)) = ((a,b),c)

{-# INLINE juggle #-}
juggle :: ((a,b),c) -> ((a,c),b)
juggle ~(~(a,b),c) = ((a,c),b)

{-# INLINE squish #-}
squish :: (a,(b,c)) -> (b,(a,c))
squish ~(a,~(b,c)) = (b,(a,c))

{-# INLINE distribute #-}
distribute :: ((a,b),(c,d)) -> ((a,c),(b,d))
distribute ~(~(a,b),~(c,d)) = ((a,c),(b,d))

multiRun :: (arr -> a -> (b, arr)) -> arr -> [a] -> [b]
multiRun _ _ [] = []
multiRun run prog (a : as) =
    let (b, prog') = run prog a
    in b : multiRun run prog' as