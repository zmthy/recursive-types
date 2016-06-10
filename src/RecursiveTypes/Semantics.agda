module RecursiveTypes.Semantics where

open import Data.Bool
  using ( true )

open import Data.Empty
  using ( ⊥-elim )

open import Data.Integer
  using ( ℤ )

open import Data.Fin
  using ( Fin ; zero ; suc ; fromℕ )

open import Data.Nat
  using ( ℕ ; zero ; suc )

open import Data.Product
  using ( _,_ ; proj₁ ; proj₂ )

open import Data.Sum
  using ( _⊎_ ; inj₁ ; inj₂ )

import RecursiveTypes.Syntax
  as Syntax

open import RecursiveTypes.WellFormed

-- A coinductively defined type, with the recursive references now
-- encoded by a coinductive reference to a Type in the components of a
-- pair.
mutual
  data Type : Set where
    Int : Type
    _⨯_ : (A B : ∞Type) → Type
    _∨_ : (A B : Type) → Type

  -- A coinductive record is used to encode the recursive reference:
  -- this differs from the definition in the paper, which uses the
  -- musical notation of coinduction.
  record ∞Type : Set where
    coinductive
    constructor delay
    field type : Type

infixl 10 _∨_
infixl 11 _⨯_

open ∞Type public

-- A list of substitutions: essentially a length-indexed vector, but the
-- type of each element in the list is indexed by the reverse index (the
-- length of the tail after it) that it appears at.
data Substs : ℕ → Set where
  [] : Substs 0
  _∷_ : ∀ {n A} → WellFormed (fromℕ n) A → Substs n → Substs (suc n)

-- Any well-formed syntactic type can be infinitely unfolded into a
-- defined type.  The unfolding includes a list of substitutions to
-- apply once a coinductive point is encountered: this is necessary to
-- ensure the points of recursion occur behind such a point, convincing
-- the Agda termination checker that the operation is productive.  An
-- initial unfolding begins with an empty list of substitutions.
--
-- The type of the unfolding isn't a formal proposition of the statement
-- above, because there is no relationship between the syntactic and
-- coinductive type expressed in the type.  The property that the
-- resulting type represents the expected meaning of the syntactic type
-- can be manually verified by observing that each of the base
-- constructors of the coinductive type is only constructed by a
-- corresponding constructor in the syntax.
mutual
  ∞-unfold : ∀ {n B} → WellFormed (fromℕ n) B → Substs n → Type
  ∞-unfold int         v = Int
  ∞-unfold (pair p q)  v = apply-substs p v ⨯ apply-substs q v
  ∞-unfold (union p q) v = ∞-unfold p v ∨ ∞-unfold q v
  ∞-unfold (rec p)     v = ∞-unfold p (rec p ∷ v)
  ∞-unfold (ref p)     v = ⊥-elim (<-bound p)

  -- This definition uses Agda's copattern syntax to show productivity.
  -- The base case applies ∞-unfold in a way that will not terminate, so
  -- we assert that the result will be productive by nesting the
  -- definition in the copattern of the field for the resulting ∞Type.
  apply-substs : ∀ {n} {B : Syntax.Type n}
                 → WellFormed zero B → Substs n → ∞Type
  type (apply-substs p []) = ∞-unfold p []
  apply-substs p (q ∷ v)   = apply-substs (wf p [ weaken! q ]) v

-- Coinductive types are given meaning by describing their embedding
-- into Agda types.  Because the types can be infinite in size, the
-- embedding might not terminate, so the typical pair type is replaced
-- with a custom data type that delays the application of ⟦_⟧.
mutual
  ⟦_⟧ : Type → Set
  ⟦ Int ⟧   = ℤ
  ⟦ A ⨯ B ⟧ = type A × type B
  ⟦ A ∨ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧

  -- A specialised form of the Rec type defined in the Coinduction
  -- module, which was originally defined in the ΠΣ calculus.  This is
  -- necessary to have the ⟦_⟧ function terminate.
  data _×_ (A : Type) (B : Type) : Set where
    _,_ : ⟦ A ⟧ → ⟦ B ⟧ → A × B

-- Values are either integers or pairs of values.
data Value : Set where
  int : ℤ → Value
  _,_ : (x y : Value) → Value

-- Given a value from the meaning of a type, that value can be embedded
-- in the Value type.  This essentially erases the sum types from the
-- type embedding.
embed : ∀ {A} → ⟦ A ⟧ → Value
embed {Int}   x        = int x
embed {A ⨯ B} (x , y)  = embed x , embed y
embed {A ∨ B} (inj₁ x) = embed x
embed {A ∨ B} (inj₂ y) = embed y
