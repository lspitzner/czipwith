{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Main where



import Data.CZipWith
import Data.Functor.Identity



data A f = A
  { a_str :: f String
  , a_bool :: f Bool
  }

data B f = B
  { b_int :: f Int
  , b_float :: f Float
  , b_a :: A f
  }

deriving instance Show (A Identity)
deriving instance Eq (A Identity)


deriveCZipWith ''A
deriveCZipWith ''B

main :: IO ()
main = do
  let x1 = A (Identity "string") (Identity True)
  let x2 = A (Just "just") Nothing
  let x3 = cZipWith
        ( \x my -> case my of
          Nothing -> x
          Just y  -> Identity y
        )
        x1
        x2
  errorIf (x3 /= A (Identity "just") (Identity True)) $ return ()

errorIf :: Bool -> a -> a
errorIf False = id
errorIf True  = error "errorIf"
