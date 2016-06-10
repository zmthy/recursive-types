module RecursiveTypes.Inductive.Subtyping where

open import RecursiveTypes.Inductive.Semantics

open import RecursiveTypes.Coinductive.Subtyping

open import RecursiveTypes.Coinductive.Type

open import RecursiveTypes.Inductive.WellFormed

infix 8 _<:_

_<:_ : ∀ {A B} → WellFormed _ A → WellFormed _ B → Set
p <: q = ∞unfold p ≤ ∞unfold q

<:-sound : ∀ {A B} {p : WellFormed _ A} {q : WellFormed _ B}
          → p <: q → ⟦ ∞unfold p ⟧⊆⟦ ∞unfold q ⟧
<:-sound = ≤-sound
