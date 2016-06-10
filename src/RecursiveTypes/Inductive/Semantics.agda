module RecursiveTypes.Inductive.Semantics where

open import RecursiveTypes.Coinductive.Type
  using ( ∞unfold )

import RecursiveTypes.Coinductive.Semantics
  as Coinductive

open import RecursiveTypes.Inductive.WellFormed
  using ( WellFormed )

open import RecursiveTypes.Value

⟦_⟧ : ∀ {A} → WellFormed _ A → Set
⟦ p ⟧ = Coinductive.⟦ ∞unfold p ⟧

_×_ : ∀ {A B} → WellFormed _ A → WellFormed _ B → Set
p × q = ∞unfold p Coinductive.× ∞unfold q

embed : ∀ {A} {p : WellFormed _ A} → ⟦ p ⟧ → Value
embed = Coinductive.embed
