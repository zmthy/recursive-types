module RecursiveTypes.Inductive.Type where

open import Data.Empty
  using ( ⊥-elim )

open import Data.Fin
  using ( Fin ; zero ; suc ; fromℕ )

open import Data.Nat
  using ( ℕ ; zero ; suc )

open import Function
  using ( _∘_ )

open import Relation.Nullary
  using ( ¬_ ; Dec ; yes ; no )

-- A syntactic type uses De-Bruijn indices to refer to recursive references
-- introduced by μ-binders.  A Type is indexed by the number of free variables
-- in scope, and a Ref is restricted to only referring to one of those
-- variables.
data Type (n : ℕ) : Set where
  Int : Type n
  _⨯_ : (A B : Type n) → Type n
  _∨_ : (A B : Type n) → Type n
  μ_ : (A : Type (suc n)) → Type n
  Ref : (x : Fin n) → Type n

infix 9 μ_
infixl 10 _∨_
infixl 11 _⨯_

-- A substitution lemma: increment every reference in the type by one.  This is
-- used when a type is substituted into another type: every time the
-- substitution passes by a μ-binder, the variables this type referred to are
-- now an extra binder away, so all of the references must be incremented by
-- one.
inc : ∀ {n} → Type n → Type (suc n)
inc Int     = Int
inc (A ⨯ B) = inc A ⨯ inc B
inc (A ∨ B) = inc A ∨ inc B
inc (μ A)   = μ inc A
inc (Ref x) = Ref (suc x)

-- A proposition that the indexed number is the largest it can be, i.e. one less
-- than its exclusive upper bound.
data Max : ∀ {n} → Fin n → Set where
  max : ∀ {n} → Max {suc n} (fromℕ n)

-- A lemma on Max: if a number is max, then one less than that number with a
-- simultaneously lowered upper bound is also max.
max-pre : ∀ {n} {x : Fin (suc n)} → Max (suc x) → Max x
max-pre max = max

-- A lemma on Max: if a number is max, then one more than that number with a
-- simultaneously increased upper bound is also max.
max-suc : ∀ {n} {x : Fin n} → Max x → Max (suc x)
max-suc max = max

-- Given a proof that a number is not max, reduce its lower bound by one,
-- keeping the value of the number the same.
reduce : ∀ {n} {x : Fin (suc n)} → ¬ Max x → Fin n
reduce {zero}  {zero}   ¬p = ⊥-elim (¬p max)
reduce {zero}  {suc ()} ¬p
reduce {suc n} {zero}   ¬p = zero
reduce {suc n} {suc x}  ¬p = suc (reduce {x = x} (¬p ∘ max-suc))

-- Max is a decidable proposition: just compare the number value to the value of
-- the upper bound.
max? : ∀ {n} (x : Fin n) → Dec (Max x)
max? {zero}        ()
max? {suc zero}    zero     = yes max
max? {suc zero}    (suc ())
max? {suc (suc n)} zero     = no (λ ())
max? {suc (suc n)} (suc x)  with max? x
max? {suc (suc n)} (suc .(fromℕ n)) | yes max = yes max
max? {suc (suc n)} (suc x)          | no ¬p = no (¬p ∘ max-pre)

-- Substitute a type as the largest reference in another type, reducing the
-- number of references as a result.
_[_] : ∀ {n} → Type (suc n) → Type n → Type n
Int     [ A ] = Int
(B ⨯ C) [ A ] = B [ A ] ⨯ C [ A ]
(B ∨ C) [ A ] = B [ A ] ∨ C [ A ]
(μ B)   [ A ] = μ B [ inc A ]
Ref x   [ A ] with max? x
Ref ._  [ A ] | yes max  = A
Ref x   [ A ] | no ¬p    = Ref (reduce ¬p)

infix 12 _[_]
