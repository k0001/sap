module Main where

import qualified Test.Tasty as Tasty
import qualified Test.Tasty.Runners as Tasty

--------------------------------------------------------------------------------

main :: IO ()
main = Tasty.defaultMainWithIngredients
  [ Tasty.consoleTestReporter
  , Tasty.listingTests
  ] tt

tt :: Tasty.TestTree
tt = Tasty.testGroup "main"
  [
  ]
