module RecursiveTypes.Value where

open import Data.Integer
  using ( ℤ )

-- Values are either integers or pairs of values.
data Value : Set where
  int : ℤ → Value
  _,_ : (x y : Value) → Value
