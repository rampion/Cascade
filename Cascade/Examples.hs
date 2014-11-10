{-# LANGUAGE DataKinds              #-}
module Cascade.Examples where

import Cascade
import Cascade.Debugger

import Control.Category
import Control.Monad
import Data.Char (toUpper)
import Prelude hiding (id, (.))
import System.Environment (getEnv, setEnv, getProgName)

-- examples
fc, gc :: Cascade '[String, Int, Double, Double]
fc =  read          :>>>
      fromIntegral  :>>>
      (1/)          :>>> Done
gc =  length        :>>>
      (2^)          :>>>
      negate        :>>> Done

mc, nc :: CascadeM IO '[ String, (), String, String, () ]
mc =  putStrLn                >=>:
      const getLine           >=>:
      return . map toUpper    >=>:
      putStrLn                >=>: Done
nc =  print . length          >=>:
      const getProgName       >=>:
      getEnv                  >=>:
      setEnv "foo"            >=>: Done

wc, vc :: CascadeW ((,) Char) '[ Int, Char, Int, String ]
wc =  fst                       =>=:
      fromEnum . snd            =>=:
      uncurry (flip replicate)  =>=: Done
vc =  toEnum . snd              =>=:
      const 5                   =>=:
      show                      =>=: Done

rundmc :: IO (DebuggerM IO '[String, String, (), [Char]] () '[])
rundmc = debugM >>> use "walk this way" >=> step >=> step >=> step $ mc

