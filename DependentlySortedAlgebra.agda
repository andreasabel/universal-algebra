-- To model dependently-sorted algebras, let us consider algebras indexed by algebras.


{-# OPTIONS --guardedness #-}  -- transitional, for Data.Container.Indexed.FreeMonad

open import Level

open import Data.Container.Indexed.Core            using (Container; ⟦_⟧; _◃_/_)
open import Data.Container.Indexed.FreeMonad       using (_⋆C_)
open import Data.W.Indexed                         using (W; sup)

open import Data.Product                           using (Σ; _×_; _,_; Σ-syntax); open Σ
open import Data.Sum                               using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty.Polymorphic                 using (⊥; ⊥-elim)

open import Function                               using (_∘_)
open import Function.Bundles                       using (Func)

open import Relation.Binary                        using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality  using (_≡_; refl)
open import Relation.Unary                         using (Pred)

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Setoid using (Carrier; _≈_; isEquivalence)
open Func renaming (f to apply)

open import MultiSortedAlgebra using
  (⟦_⟧s; Signature; SetoidModel)

-- Letter ℓ denotes universe levels.

variable
  ℓ ℓ' ℓˢ ℓᵒ ℓᵃ ℓᵐ ℓᵉ ℓⁱ ℓⁿᵐ ℓⁿᵉ : Level
  I : Set ℓⁱ
  S : Set ℓˢ

-- Example: vectors
--
-- We can formulate vectors over a model of the natural numbers.

record NatSort : Set where
  constructor natˢ

data NatOp : Set where
  zeroᵒ : NatOp
  sucᵒ  : NatOp
  -- Let us not consider varieties, only free algebras for now.
  -- oone  : NatOp
  -- oplus : NatOp

data Arity0 : Set where

record Arity1 : Set where
  constructor theArg

data Arity2 : Set where
  ar0 ar1 : Arity2

NatAr : NatOp → Set
NatAr zeroᵒ = Arity0
NatAr sucᵒ  = Arity1
-- NatAr oone  = Arity0
-- NatAr oplus = Arity2

NatSig : Signature 0ℓ 0ℓ 0ℓ
NatSig = record
  { Sort = NatSort
  ; Ops  = (λ _ → NatOp) ◃ NatAr / λ _ _ → natˢ
  }

module Vectors (NAT : SetoidModel NatSig ℓⁿᵐ ℓⁿᵉ) where
  open Setoid
  open SetoidModel
  -- open SetoidModel NAT renaming (Den to ⟦_⟧ⁿ; den to ⦅_⦆ⁿ)

  ⟦nat⟧  = NAT .Den natˢ .Carrier

  _≈ⁿ_ : (n m : ⟦nat⟧) → Set _
  _≈ⁿ_ = NAT .Den natˢ ._≈_

  ⦅zero⦆ = NAT .den .apply (zeroᵒ , λ())
  ⦅suc⦆ : ⟦nat⟧ → ⟦nat⟧
  ⦅suc⦆ ⦅n⦆ = NAT .den .apply (sucᵒ , λ _ → ⦅n⦆)

  -- We have two sorts, an element sort, and a family of vectors over these elements

  data VecSort : Set ℓⁿᵐ where
    elˢ  : VecSort
    vecˢ : (n : ⟦nat⟧) → VecSort

  -- These sorts are quotiented by _≈ⁿ_, so sorts should be a setoid rather than a set.

  -- We model some operations on vectors.

  -- Operations are subject to equality that ignores the proofs.
  -- So there should be a setoid of operations rather than a set...

  data VecOp : (s : VecSort) → Set (ℓⁿᵉ ⊔ ℓⁿᵐ) where
    nilᵒ  : (n : ⟦nat⟧)   (n=0   : n ≈ⁿ ⦅zero⦆)  → VecOp (vecˢ n)
    consᵒ : (n m : ⟦nat⟧) (n=m+1 : n ≈ⁿ ⦅suc⦆ m) → VecOp (vecˢ n)

  VecAr : ∀{s} → VecOp s → Set
  VecAr (nilᵒ  n   n=0  ) = Arity0
  VecAr (consᵒ n m n=m+1) = Arity2

  vecTyping : ∀{s} (o : VecOp s) → VecAr o → VecSort
  vecTyping (consᵒ n m n=m+1) ar0 = elˢ
  vecTyping (consᵒ n m n=m+1) ar1 = vecˢ m

  VecSig : Signature _ _ _
  VecSig = record
    { Sort = VecSort
    ; Ops  = VecOp ◃ VecAr / vecTyping
    }
