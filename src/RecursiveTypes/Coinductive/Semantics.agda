module RecursiveTypes.Coinductive.Semantics where

open import Data.Integer
  using ( ℤ )

open import Data.Sum
  using ( _⊎_ ; inj₁ ; inj₂ )

open import RecursiveTypes.Coinductive.Type

open import RecursiveTypes.Value

-- Coinductive types are given meaning by describing their embedding into Agda
-- types.  Because the types can be infinite in size, the embedding might not
-- terminate, so the typical pair type is replaced with a custom data type that
-- delays the application of ⟦_⟧.
mutual
  ⟦_⟧ : Type → Set
  ⟦ Int ⟧   = ℤ
  ⟦ A ⨯ B ⟧ = type A × type B
  ⟦ A ∨ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧

  -- A specialised form of the Rec type defined in the Coinduction module, which
  -- was originally defined in the ΠΣ calculus.  This is necessary to have the
  -- ⟦_⟧ function terminate.
  data _×_ (A : Type) (B : Type) : Set where
    _,_ : ⟦ A ⟧ → ⟦ B ⟧ → A × B

-- Given a value from the meaning of a type, that value can be embedded in the
-- Value type.  This essentially erases the sum types from the type embedding.
embed : ∀ {A} → ⟦ A ⟧ → Value
embed {Int}   x        = int x
embed {A ⨯ B} (x , y)  = embed x , embed y
embed {A ∨ B} (inj₁ x) = embed x
embed {A ∨ B} (inj₂ y) = embed y
