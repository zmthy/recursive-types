-- Syntax of simple values.
open import RecursiveTypes.Value

-- Inductively defined syntax of recursive types.
open import RecursiveTypes.Inductive.Type

-- Well-formedness (contractivity) of inductively defined types.
open import RecursiveTypes.Inductive.WellFormed

-- Coinductively defined syntax of recursive types.
open import RecursiveTypes.Coinductive.Type

-- Meaning of the coinductive types over the values.
open import RecursiveTypes.Coinductive.Semantics

-- Subtyping between coinductive types, with proof of soundness and completeness
-- in relation to the subset relation between the semantic types.
open import RecursiveTypes.Coinductive.Subtyping
