module Main where

newtype Dist a = Dist [(a, Double)] deriving Show
instance Functor Dist where fmap f (Dist xs) = Dist [(f x, p) | (x, p) <- xs]
instance Applicative Dist where
  pure x = Dist [(x, 1.0)]
  Dist fs <*> Dist xs = Dist [(f x, pf*px) | (f,pf) <- fs, (x,px) <- xs]
instance Monad Dist where
  Dist xs >>= f = Dist [(y, px*py) | (x,px) <- xs, (y,py) <- let Dist ys = f x in ys]

bernoulli :: Double -> Dist Bool
bernoulli p = Dist [(True, p), (False, 1-p)]

circuit :: () -> Dist [Bool]
circuit () = do
  v0 <- bernoulli 0.5
  v1 <- bernoulli 0.5
  return [v1, v1, v0, v0]

main :: IO ()
main = do
  let result = circuit ()
  putStrLn "Distribution:"
  mapM_ print (let Dist xs = result in xs)
