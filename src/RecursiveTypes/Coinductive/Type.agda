module RecursiveTypes.Coinductive.Type where

open import Data.Empty
  using ( ⊥-elim )

open import Data.Fin
  using ( zero ; fromℕ )

import RecursiveTypes.Inductive.Type
  as Inductive

open import RecursiveTypes.Inductive.WellFormed

-- A coinductively defined type, with the recursive references now encoded by a
-- coinductive reference to a Type in the components of a pair.
mutual
  data Type : Set where
    Int : Type
    _⨯_ : (A B : ∞Type) → Type
    _∨_ : (A B : Type) → Type

  -- A coinductive record is used to encode the recursive reference: this
  -- differs from the definition in the paper, which uses the musical notation
  -- of coinduction.
  record ∞Type : Set where
    coinductive
    constructor delay
    field type : Type

infixl 10 _∨_
infixl 11 _⨯_

open ∞Type public

-- Any well-formed syntactic type can be infinitely unfolded into a defined
-- type.  The unfolding includes a list of substitutions to apply once a
-- coinductive point is encountered: this is necessary to ensure the points of
-- recursion occur behind such a point, convincing the Agda termination checker
-- that the operation is productive.  An initial unfolding begins with an empty
-- list of substitutions.  The type of the unfolding isn't a formal proposition
-- of the statement above, because there is no relationship between the
-- syntactic and coinductive type expressed in the type.  The property that the
-- resulting type represents the expected meaning of the syntactic type can be
-- manually verified by observing that each of the base constructors of the
-- coinductive type is only constructed by a corresponding constructor in the
-- syntax.
mutual
  ∞unfold′ : ∀ {n B} → WellFormed (fromℕ n) B → Substs n (fromℕ n) → Type
  ∞unfold′ int         v = Int
  ∞unfold′ (pair p q)  v = apply-substs p v ⨯ apply-substs q v
  ∞unfold′ (union p q) v = ∞unfold′ p v ∨ ∞unfold′ q v
  ∞unfold′ (rec p)     v = ∞unfold′ p (rec p ∷ v)
  ∞unfold′ (ref p)     v = ⊥-elim (<-bound p)

  -- This definition uses Agda's copattern syntax to show productivity.  The
  -- base case applies ∞-unfold in a way that will not terminate, so we assert
  -- that the result will be productive by nesting the definition in the
  -- copattern of the field for the resulting ∞Type.
  apply-substs : ∀ {n} {B : Inductive.Type n}
                 → WellFormed zero B → Substs n (fromℕ n) → ∞Type
  type (apply-substs {0} p []) = ∞unfold′ p []
  apply-substs p (q ∷ v)   = apply-substs (wf p [ weaken! q ]) v

∞unfold : ∀ {A} → WellFormed _ A → Type
∞unfold p = ∞unfold′ p []
