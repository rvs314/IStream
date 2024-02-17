module IStream

import Data.Fuel
import Data.Zippable

%default total

||| A potentially infinite, lazy stream of values
||| Unlike some stream formulations, IStream separates the laziness aspect
||| from the production of values, so each evaluation step can return zero
||| or more values.
||| The `I` in `IStream` stands for \'Interlacing\'. While the semigroup operation
||| performs an order-preserving append, the dijunction operator `<|>` interlaces
||| the two streams, creating a new stream which preserves the invariant that
||| any value that can be reached from either stream in finite time can be
||| be reached in the interlacing in finite time.
public export
data IStream : Type -> Type where
  ||| The 'cons' operation, prepending a new item onto to the stream
  ||| Note: this isn't a lazy operation
  (::) : a -> IStream a -> IStream a
  ||| The empty stream
  Nil : IStream a
  ||| Delays the evaluation of a stream
  Wait : Inf (IStream a) -> IStream a

||| A stream of values which will never produce anything
public export
immature : IStream a
immature  = Wait immature

||| Do a small, constant amount of work towards producing a value
public export
mature : IStream a -> IStream a
mature (x :: y) = x :: y
mature []       = []
mature (Wait x) = x

||| The stream of a single value, repeated infinitely
public export
repeat : a -> IStream a
repeat x = x :: Wait (repeat x)

||| Do `f` units of work to reify the first `n` items of the stream `s`.
||| Returns the values which were reified, and the rest of the stream.
public export
split : (f : Fuel) -> (n : Nat) -> (s : IStream a) -> (List a, IStream a)
split _ _ [] = ([], [])
split _ 0 y = ([], y)
split x (S k) (y :: z) = let (head, tail) = split (More x) k z 
                         in (y :: head, tail)
split (More x) k (Wait y) = split x k y
split Dry _ y = ([], y)

||| Do `f` units of work to reify the first `n` elements of the stream `s`.
||| Returns the list of values which were reified, which may be fewer than `n`.
public export
take : (f : Fuel) -> (n : Nat) -> (i : IStream a) -> List a 
take x k y = fst $ split x k y

||| Do `f` units of work to turn the stream into a list
public export
toList : (f : Fuel) -> (s : IStream a) -> List a
toList _        []       = []
toList x        (y :: z) = y :: toList x z
toList (More x) (Wait y) = toList x y
toList Dry      y        = []

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
