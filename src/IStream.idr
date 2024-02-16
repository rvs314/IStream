module IStream

import Data.Fuel
import Data.Zippable

%default total

public export
data IStream a = (::) a (IStream a)
               | Nil
               | Wait (Inf (IStream a))

public export
immature : IStream a
immature  = Wait immature

public export
mature : IStream a -> IStream a
mature (x :: y) = x :: y
mature []       = []
mature (Wait x) = x

public export
repeat : a -> IStream a
repeat x = x :: Wait (repeat x)

public export
split : Fuel -> Nat -> IStream a -> (List a, IStream a)
split _ _ [] = ([], [])
split _ 0 y = ([], y)
split x (S k) (y :: z) = let (head, tail) = split (More x) k z 
                         in (y :: head, tail)
split (More x) k (Wait y) = split x k y
split Dry _ y = ([], y)

public export
take : Fuel -> Nat -> IStream a -> List a 
take x k y = fst $ split x k y

public export
toList : Fuel -> IStream a -> List a
toList Dry y = []
toList (More x) (y :: z) = y :: toList (More x) z
toList (More x) [] = []
toList (More x) (Wait y) = toList x y

mapApp : (a -> b) -> IStream a -> IStream b -> IStream b
mapApp f (x :: z) y = f x :: mapApp f z y
mapApp f [] y       = y
mapApp f (Wait x) y = Wait (mapApp f x y)

public export
Semigroup (IStream a) where
  (x :: y) <+> ys = x :: (y <+> ys)
  [] <+> ys       = ys
  (Wait x) <+> ys = Wait (x <+> ys)

public export
Functor IStream where
  map f k = mapApp f k []

public export
Applicative IStream where
  pure x = [x]

  (x :: y) <*> k = mapApp x k (y <*> k)
  []       <*> k = []
  (Wait x) <*> k = Wait (x <*> k)

public export
Monad IStream where
  (x :: y) >>= fasb = fasb x <+> (y >>= fasb)
  []       >>= fasb = []
  (Wait x) >>= fasb = Wait (x >>= fasb)

public export
Alternative IStream where
  empty = []

  (x :: y) <|> r = x :: (y <|> r)
  []       <|> r = r
  (Wait x) <|> r = r <|> x

public export
Zippable IStream where
  zipWith fabc [] bs = []
  zipWith fabc as [] = []
  zipWith fabc as (Wait bs) = Wait (zipWith fabc as bs)
  zipWith fabc (Wait as) bs = Wait (zipWith fabc as bs)
  zipWith fabc (a :: as) (b :: bs) = fabc a b :: zipWith fabc as bs

  unzipWith fabc (x :: y) = let rst : (IStream b, IStream c)
                                rst = unzipWith fabc y 
                                head : (b, c)
                                head = fabc x
                            in (fst head :: fst rst, snd head :: snd rst)
  unzipWith fabc [] = ([], [])
  unzipWith fabc (Wait x) = let rst : Inf (IStream b, IStream c)
                                rst = unzipWith fabc x
                            in (Wait (fst $ Force rst), Wait (snd $ Force rst))

  zipWith3 fabcd as bs cs = zipWith (uncurry . fabcd) as (zip bs cs)

  unzipWith3 fabcd as = let (bs, cds) = unzipWith fabcd as
                            (cs, ds)  = unzip cds
                        in (bs, cs, ds)
