module RecursiveTypes.Inductive.WellFormed where

open import Data.Fin
  using ( Fin ; zero ; suc
        ; toℕ ; fromℕ
        ; Fin′ ; inject ; inject! ; inject₁
        ; _≤_
        )

open import Data.Nat
  using ( ℕ ; zero ; suc ; z≤n ; s≤s )

open import Function
  using ( _∘_ )

open import Relation.Binary
  using ( Decidable )

open import Relation.Nullary
  using ( ¬_ ; Dec ; yes ; no )

open import RecursiveTypes.Inductive.Type

-- A well-formedness proof for a type guarantees the type's contractivity by
-- disallowing a set of references in scope until passing through a pair type
-- constructor.
data WellFormed {n} (m : Fin (suc n)) : Type n → Set where
  int : WellFormed m Int
  pair : ∀ {A B} → WellFormed zero A → WellFormed zero B
         → WellFormed m (A ⨯ B)
  union : ∀ {A B} → WellFormed m A → WellFormed m B
          → WellFormed m (A ∨ B)
  rec : ∀ {A} → WellFormed (suc m) A → WellFormed m (μ A)
  ref : ∀ {x} → m ≤ inject₁ x → WellFormed m (Ref x)

-- A lemma on numbers drawn from a finite set: no such number is ever equal to
-- or greater than its exclusive upper bound.
<-bound : ∀ {n} {x : Fin n} → ¬ (fromℕ n ≤ inject₁ x)
<-bound {zero} {()} p
<-bound {suc n} {zero} ()
<-bound {suc n} {suc x} (s≤s p) = <-bound p

-- Lift an equality between a Fin value and its injection over ≤.
inject-≤ : ∀ {n} {x y : Fin n} → x ≤ y → inject₁ x ≤ inject₁ y
inject-≤ {x = zero} z≤n = z≤n
inject-≤ {x = suc x} {zero} ()
inject-≤ {x = suc x} {suc y} (s≤s p) = s≤s (inject-≤ p)

-- Lift an equality between a Fin value and its reduction over ≤.
reduce-≤ : ∀ {n} {x y : Fin n} → inject₁ x ≤ inject₁ y → x ≤ y
reduce-≤ {x = zero} z≤n = z≤n
reduce-≤ {x = suc x} {zero} ()
reduce-≤ {x = suc x} {suc y} (s≤s p) = s≤s (reduce-≤ p)

-- A lemma on ≤: if x ≤ y, then x ≤ suc y.
suc-≤ : ∀ {n} {x y : Fin n} → x ≤ y → inject₁ x ≤ suc y
suc-≤ {x = zero} z≤n = z≤n
suc-≤ {x = suc x} {zero} ()
suc-≤ {x = suc x} {suc y} (s≤s p) = s≤s (suc-≤ p)

-- A lemma on ≤: if suc x ≤ y, then x ≤ y.
pred-≤ : ∀ {n} {x y : Fin n} → suc x ≤ inject₁ y → inject₁ x ≤ inject₁ y
pred-≤ {y = zero} ()
pred-≤ {y = suc x} (s≤s p) = suc-≤ p

-- A lemma on ≤: if x ≤ y, then for any z < x, z ≤ y.
trans-< : ∀ {n} {x y : Fin n} {z : Fin′ x} → x ≤ y → inject z ≤ y
trans-< {x = zero} {z = ()} p
trans-< {x = suc x} {zero} ()
trans-< {x = suc x} {suc y} {zero} (s≤s p) = z≤n
trans-< {x = suc x} {suc y} {suc z} (s≤s p) = s≤s (trans-< p)

-- ≤ is a decidable binary operator.
_≤?_ : ∀ {n} → Decidable {A = Fin n} _≤_
zero ≤? zero = yes z≤n
zero ≤? suc y = yes z≤n
suc x ≤? zero = no (λ ())
suc x ≤? suc y with x ≤? y
suc x ≤? suc y | yes p = yes (s≤s p)
suc x ≤? suc y | no ¬p = no (¬p ∘ (λ { (s≤s p) → p }))

-- Determining if a type is well formed under m invalid variables is decidable.
well-formed? : ∀ {n} m → (A : Type n) → Dec (WellFormed m A)
well-formed? m Int = yes int
well-formed? m (A ⨯ B) with well-formed? zero A | well-formed? zero B
... | yes p | yes q = yes (pair p q)
... | no ¬p | _     = no λ { (pair p q) → ¬p p }
... | _     | no ¬q = no λ { (pair p q) → ¬q q }
well-formed? m (A ∨ B) with well-formed? m A | well-formed? m B
... | yes p | yes q = yes (union p q)
... | no ¬p | _     = no λ { (union p q) → ¬p p }
... | _     | no ¬q = no λ { (union p q) → ¬q q }
well-formed? m (μ A) with well-formed? (suc m) A
... | yes p = yes (rec p)
... | no ¬p = no λ { (rec p) → ¬p p }
well-formed? m (Ref x) with m ≤? inject₁ x
... | yes p = yes (ref p)
... | no ¬p = no (λ { (ref p) → ¬p p })

-- A lemma on WellFormed: if a type A is well-formed under the variable
-- restriction m, then it is well-formed under any other restriction less than
-- m.
weaken : ∀ {n m} {A : Type n} (x : Fin′ m)
         → WellFormed m A → WellFormed (inject x) A
weaken x int = int
weaken x (pair p q) = pair p q
weaken x (union p q) = union (weaken x p) (weaken x q)
weaken x (rec p) = rec (weaken (suc x) p)
weaken {m = zero} () (ref p)
weaken {m = suc m} x (ref {zero} ())
weaken {m = suc m} zero (ref {suc y} p) = ref z≤n
weaken {m = suc m} (suc x) (ref {suc y} (s≤s p)) = ref (s≤s (trans-< p))

-- A lemma on WellFormed: if a type A is well-formed under the variable
-- restriction m, then it is well-formed under one less than m.
weaken₁ : ∀ {n m} {A : Type n}
          → WellFormed (suc m) A → WellFormed (inject₁ m) A
weaken₁ int = int
weaken₁ (pair p q) = pair p q
weaken₁ (union p q) = union (weaken₁ p) (weaken₁ q)
weaken₁ (rec p) = rec (weaken₁ p)
weaken₁ {m = zero} (ref p) = ref z≤n
weaken₁ {m = suc m} (ref p) = ref (pred-≤ p)

-- A lemma on WellFormed: if a type A is well-formed under any variable
-- restriction, then it is well-formed under no restrictions.
weaken! : ∀ {n m} {A : Type n}
          → WellFormed m A → WellFormed zero A
weaken! int = int
weaken! (pair p q) = pair p q
weaken! (union p q) = union (weaken! p) (weaken! q)
weaken! {m = zero} (rec p) = rec p
weaken! {m = suc m} (rec p) = rec (weaken (suc zero) p)
weaken! (ref p) = ref z≤n

-- The inc function preserves well-formedness.
wf-inc : ∀ {n m} {A : Type n}
         → WellFormed m A → WellFormed (suc m) (inc A)
wf-inc int = int
wf-inc (pair p q) = pair (weaken! (wf-inc p)) (weaken! (wf-inc q))
wf-inc (union p q) = union (wf-inc p) (wf-inc q)
wf-inc (rec p) = rec (wf-inc p)
wf-inc (ref p) = ref (s≤s p)

-- The reduce function preserves ≤.
reduce₁ : ∀ {n m} {x : Fin n} (¬p : ¬ Max (suc x))
          → m ≤ x → suc m ≤ inject₁ (reduce ¬p)
reduce₁ {m = zero} ¬p₁ z≤n = s≤s z≤n
reduce₁ {m = suc m} {zero} ¬p ()
reduce₁ {m = suc m₁} {suc x₁} ¬p₁ (s≤s q₁) =
  s≤s (reduce₁ (λ z → ¬p₁ (max-suc z)) q₁)

-- The reduce function preserves well-formedness.
wf-reduce : ∀ {n} {m : Fin (suc n)} {x}
            → inject₁ m ≤ inject₁ x → (¬p : ¬ Max x)
            → WellFormed m (Ref (reduce ¬p))
wf-reduce {m = zero} q ¬p = ref z≤n
wf-reduce {m = suc m} {zero} () ¬p
wf-reduce {m = suc m} {suc x} (s≤s q) ¬p = ref (reduce₁ ¬p (reduce-≤ q))

-- The substitution function preserves well-formedness.
wf_[_] : ∀ {n m A} {B : Type n}
         → WellFormed (inject₁ m) A → WellFormed m B → WellFormed m (A [ B ])
wf int       [ p ] = int
wf pair q r  [ p ] = pair (wf q [ weaken! p ]) (wf r [ weaken! p ])
wf union q r [ p ] = union (wf q [ p ]) (wf r [ p ])
wf rec q     [ p ] = rec (wf q [ wf-inc p ])
wf ref {x} q [ p ] with max? x
wf ref     q [ p ] | yes max = p
wf ref     q [ p ] | no ¬p   = wf-reduce q ¬p

-- Unfolding a recursive type by one level preserves well-formedness.
unfold : ∀ {n m} {A : Type (suc n)}
         → WellFormed (suc m) A → WellFormed m (A [ μ A ])
unfold p = wf weaken₁ p [ rec p ]
