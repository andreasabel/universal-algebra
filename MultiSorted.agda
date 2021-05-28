-- Multi-sorted algebras as indexed containers
-- 2021-05-26

{-# OPTIONS --postfix-projections #-}

module _ where

open import Level
open import Size

open import Data.Container.Indexed              using (Container; ⟦_⟧; μ; _◃_/_); open Container
open import Data.Container.Indexed.FreeMonad    using (_⋆C_)
open import Data.W.Indexed                      using (W; iter)

open import Data.List.Base                      using (List; []; _∷_)
open import Data.List.Membership.Propositional  using (_∈_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

open import Data.Product                        using (Σ; _×_; _,_; Σ-syntax); open Σ
open import Data.Sum                            using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty.Polymorphic              using (⊥; ⊥-elim)

open import Function                            using (_∘_)
open import Function.Bundles                    using (Func)

open import Relation.Binary                     using (Setoid; IsEquivalence)
-- open import Relation.Binary.Structures          using (IsSetoid)
-- open import Relation.Binary.Bundles             using (Equivalence)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open Setoid using (Carrier; _≈_; isEquivalence)
open Func renaming (f to apply)

variable
  ℓ ℓ' ℓc ℓe ℓi ℓm ℓr ℓs ℓv : Level
  I O S : Set ℓ

-- Interpreting indexed containers on Setoids
-- This should go to the standard library...

⟦_⟧s : (C : Container I S ℓc ℓr) (ξ : I → Setoid ℓs ℓe) → S → Setoid _ _

⟦ C ⟧s ξ s .Carrier = ⟦ C ⟧ (Carrier ∘ ξ) s
-- ⟦ Op ◃ Ar / sort ⟧s ξ s .Carrier = Σ[ o ∈ Op s ] ((arg : Ar o) → ξ (sort _ arg) .Carrier)

⟦ Op ◃ Ar / sort ⟧s ξ s ._≈_ (op , args) (op' , args') = Σ[ eq ∈ op ≡ op' ] EqArgs eq args args'
  where
  EqArgs : (eq : op ≡ op')
           (args  : (i : Ar op)  → ξ (sort _ i) .Carrier)
           (args' : (i : Ar op') → ξ (sort _ i) .Carrier)
         → Set _
  EqArgs refl args args' = (i : Ar op) → ξ (sort _ i) ._≈_ (args i) (args' i)

⟦ Op ◃ Ar / sort ⟧s ξ s .isEquivalence .IsEquivalence.refl                        = refl , λ i → Setoid.refl  (ξ (sort _ i))
⟦ Op ◃ Ar / sort ⟧s ξ s .isEquivalence .IsEquivalence.sym   (refl , h)            = refl , λ i → Setoid.sym   (ξ (sort _ i)) (h i)
⟦ Op ◃ Ar / sort ⟧s ξ s .isEquivalence .IsEquivalence.trans (refl , g) (refl , h) = refl , λ i → Setoid.trans (ξ (sort _ i)) (g i) (h i)

-- A multi-sorted algebra is an indexed container.
--
-- * Sorts are indexes.
-- * Operators are commands.
-- * Arities/argument are responses.
--
-- Closed terms (initial model) are given by the W type for a container.

-- We assume a fixed signature (Sort, Ops).

module _ (Sort : Set ℓs) (Ops : Container Sort Sort ℓc ℓr) where
  open Container Ops renaming
    ( Command  to Op
    ; Response to Arity
    ; next     to sort
    )

  variable
    s s'   : Sort
    op op' : Op s

  -- Models

  -- A model is given by an interpretation (Den s) for each sort s
  -- plus an interpretation (den o) for each operator o.

  record SetModel ℓm : Set (ℓs ⊔ ℓc ⊔ ℓr ⊔ suc ℓm) where
    field
      Den : Sort → Set ℓm
      den : {s : Sort} → ⟦ Ops ⟧ Den s → Den s

  -- The setoid model requires operators to respect equality.

  record SetoidModel ℓm ℓe : Set (ℓs ⊔ ℓc ⊔ ℓr ⊔ suc (ℓm ⊔ ℓe)) where
    field
      Den : Sort → Setoid ℓm ℓe
      den : {s : Sort} → Func (⟦ Ops ⟧s Den s) (Den s)


-- Open terms

---------------------------------------------------------------------------
-- BRACKET BEGIN

  module Terms where

    Cxt = List Sort

    data Tm (Γ : Cxt) (s : Sort) : Set (ℓs ⊔ ℓc ⊔ ℓr) where
      var : (x : s ∈ Γ) → Tm Γ s
      app : (o : Op s) (args : (i : Arity o) → Tm Γ (sort o i)) → Tm Γ s

    record Eq : Set (ℓs ⊔ ℓc ⊔ ℓr) where
      constructor _≐_
      field
        {cxt} : Cxt
        {srt} : Sort
        lhs   : Tm cxt srt
        rhs   : Tm cxt srt

    variable
      Γ : Cxt
      t : Tm Γ s
      e : Eq

    module Interpretation (M : SetModel ℓm) where
      open SetModel M renaming (Den to ⟪_⟫)

      Env = All ⟪_⟫

      ⦅_⦆ : (t : Tm Γ s) (ρ : Env Γ) → ⟪ s ⟫
      ⦅ var x    ⦆ ρ = All.lookup ρ x
      ⦅ app o ts ⦆ ρ = den (o , λ i → ⦅ ts i ⦆ ρ)

      -- Validity of an equation needs a concept of equality


  -- Alternatively, we can model open terms by assuming new constants.

  module NewSymbols (Var : Sort → Set ℓv) where

    -- We keep the same sorts, but add a nullary operator for each variable

    C⁺ : Container Sort Sort (ℓc ⊔ ℓv) ℓr
    C⁺ = (λ s → Var s ⊎ Op s) ◃ [ (λ x → ⊥) , Arity ] / [ (λ x ()) , sort ]

    -- Terms are then given by the W-type for the extended container.

    Tm = W C⁺

    module Interpretation (M : SetModel ℓm) where
      open SetModel M renaming (Den to ⟪_⟫)

      Env = {s : Sort} (x : Var s) → ⟪ s ⟫

      -- Interpretation of terms is iteration on the W-type

      ⦅_⦆ : ∀{s} (t : Tm s) (ρ : Env) → ⟪ s ⟫
      ⦅ t ⦆ ρ = iter C⁺ step t
        where
        step : ⟦ C⁺ ⟧ ⟪_⟫ s' → ⟪ s' ⟫
        step (inj₁ x , _)    = ρ x
        step (inj₂ o , args) = den (o , args)

-- BRACKET END
---------------------------------------------------------------------------

  -- This is also covered in the standard library FreeMonad module,
  -- albeit with the restriction that the operator and variable sets
  -- have the same size.

  Cxt = Sort → Set ℓc

  variable
    Γ Δ : Cxt

  module NewSymbols' (Var : Cxt) where

    -- We keep the same sorts, but add a nullary operator for each variable

    Ops⁺ : Container Sort Sort ℓc ℓr
    Ops⁺ = Ops ⋆C Var

    -- Terms are then given by the W-type for the extended container.

    Tm = W Ops⁺

    pattern _∙_ op args = W.sup (inj₂ op , args)
    pattern var' x f    = W.sup (inj₁ x , f    )
    pattern var x       = var' x _

    module Interpretation (M : SetoidModel ℓm ℓe) where
      open SetoidModel M

      ⟪_⟫ : Sort → Set ℓm
      ⟪ s ⟫ = Den s .Carrier

      Env : Setoid _ _
      Env .Carrier  = {s : Sort} (x : Var s) → ⟪ s ⟫
      Env ._≈_ ρ ρ' = {s : Sort} (x : Var s) → Den s ._≈_ (ρ x) (ρ' x)
      Env .isEquivalence .IsEquivalence.refl  {s = s} x = Den s .Setoid.refl
      Env .isEquivalence .IsEquivalence.sym     h {s} x = Den s .Setoid.sym   (h x)
      Env .isEquivalence .IsEquivalence.trans g h {s} x = Den s .Setoid.trans (g x) (h x)

      -- Interpretation of terms is iteration on the W-type.
      -- The standard library offers `iter`, but we need this to be a Func.

      ⦅_⦆ : ∀{s} (t : Tm s) → Func Env (Den s)
      ⦅ var x     ⦆ .apply ρ    = ρ x
      ⦅ var x     ⦆ .cong  ρ=ρ' = ρ=ρ' x
      ⦅ op ∙ args ⦆ .apply ρ    = den .apply (op   , λ i → ⦅ args i ⦆ .apply ρ)
      ⦅ op ∙ args ⦆ .cong  ρ=ρ' = den .cong  (refl , λ i → ⦅ args i ⦆ .cong ρ=ρ')

      -- ⦅ t ⦆ .apply ρ = iter C⁺ step t
      --   where
      --   step : ⟦ C⁺ ⟧ ⟪_⟫ s' → ⟪ s' ⟫
      --   step (inj₁ x , _)    = ρ x
      --   step (inj₂ o , args) = den .apply (o , args)
      -- ⦅ t ⦆ .cong ρ=ρ' = {!!}

      -- TODO: make iter a Func in the standard library

      -- An equality between two terms holds in a model
      -- if the two terms are equal under all valuations of their free variables.

      Equal : ∀{s} (t t' : Tm s) → Set _
      Equal {s} t t' = ∀ (ρ : Env .Carrier) → ⦅ t ⦆ .apply ρ ~ ⦅ t' ⦆ .apply ρ
        where _~_ = Den s ._≈_

      -- This notion is an equivalence relation.

      isEquiv : IsEquivalence (Equal {s})
      isEquiv {s = s} .IsEquivalence.refl  ρ      = Den s .Setoid.refl
      isEquiv {s = s} .IsEquivalence.sym   e ρ    = Den s .Setoid.sym (e ρ)
      isEquiv {s = s} .IsEquivalence.trans e e' ρ = Den s .Setoid.trans (e ρ) (e' ρ)

  open NewSymbols' using (Tm; var; var'; _∙_; module Interpretation)
  open Interpretation using (Equal; isEquiv)

  -- Parallel substitutions

  Sub : (Γ Δ : Cxt) → Set _
  Sub Γ Δ = ∀{s} (x : Δ s) → Tm Γ s

  variable
    t t' t₁ t₂ t₃ : Tm Γ s
    ts ts' : (i : Arity op) → Tm Γ (sort _ i)
    σ σ' : Sub Γ Δ

  -- Definition of substitution.

  _[_] : (t : Tm Δ s) (σ : Sub Γ Δ) → Tm Γ s
  (var x  ) [ σ ] = σ x
  (op ∙ ts) [ σ ] = op ∙ λ i → ts i [ σ ]

  -- Substitution lemma

  module _ {M : SetoidModel ℓm ℓe} where
    open SetoidModel M

    -- The setoid of environments for context Γ

    Env = λ Γ → Interpretation.Env Γ M

    -- The interpretation function for terms in context Γ

    ⦅_⦆ : Tm Γ s → Func (Env Γ) (Den s)
    ⦅_⦆ {Γ = Γ} = Interpretation.⦅_⦆ Γ M

    -- The interpretation of substitutions.
    -- Evaluation of a substitution gives an environment.

    ⦅_⦆s : Sub Γ Δ → Env Γ .Carrier → Env Δ .Carrier
    ⦅ σ ⦆s ρ x = ⦅ σ x ⦆ .apply ρ

    -- Equality in M's interpretation of sort s.

    _~_ : Den s .Carrier → Den s .Carrier → Set _
    _~_ {s = s} = Den s ._≈_

    -- Substitution lemma: ⦅t[σ]⦆ρ ~ ⦅t⦆⦅σ⦆ρ

    substitution : (t : Tm Δ s) (σ : Sub Γ Δ) (ρ : Interpretation.Env Γ M .Carrier) →
      ⦅ t [ σ ] ⦆ .apply ρ ~ ⦅ t ⦆ .apply (⦅ σ ⦆s ρ)
    substitution (var x)   σ ρ = Den _ .Setoid.refl
    substitution (op ∙ ts) σ ρ = den .cong (refl , λ i → substitution (ts i) σ ρ)

  -- An equation is a pair of terms of the same sort in the same context.

  record Eq : Set (ℓs ⊔ suc ℓc ⊔ ℓr) where
    constructor _≐_
    field
      {cxt} : Sort → Set ℓc
      {srt} : Sort
      lhs   : Tm cxt srt
      rhs   : Tm cxt srt

  -- Equation t ≐ t' holds in model M

  _⊧_ : (M : SetoidModel ℓm ℓe) (eq : Eq) → Set _
  M ⊧ (t ≐ t') = Equal _ M t t'

  -- Entailment/consequence E ⊃ t ≐ t' when t ≐ t' holds in all models that satify equations E.

  module _ {ℓm ℓe} where

    _⊃_ : {I : Set ℓ} (E : I → Eq) (eq : Eq) → Set _
    E ⊃ eq = ∀ (M : SetoidModel ℓm ℓe) → (∀ i → M ⊧ E i) → M ⊧ eq

  -- Equational theory over a given set of equations

  data _⊢_▹_≡_ {I : Set ℓ} (E : I → Eq) : (Γ : Cxt) (t t' : Tm Γ s) → Set (ℓr ⊔ suc ℓc ⊔ ℓs ⊔ ℓ) where
    hyp   : ∀ i → let t ≐ t' = E i in E ⊢ _ ▹ t ≡ t'

    base  : ∀ (x : Γ s) {f f' : (i : ⊥) → Tm _ (⊥-elim i)} → E ⊢ Γ ▹ var' x f ≡ var' x f'
    app   : (es : ∀ i → E ⊢ Γ ▹ ts i ≡ ts' i) → E ⊢ Γ ▹ (op ∙ ts) ≡ (op ∙ ts')
    sub   : (e : E ⊢ Δ ▹ t ≡ t') (σ : Sub Γ Δ) → E ⊢ Γ ▹ (t [ σ ]) ≡ (t' [ σ ])

    refl  : (t : Tm Γ s) → E ⊢ Γ ▹ t ≡ t
    sym   : (e : E ⊢ Γ ▹ t ≡ t') → E ⊢ Γ ▹ t' ≡ t
    trans : (e : E ⊢ Γ ▹ t₁ ≡ t₂) (e' : E ⊢ Γ ▹ t₂ ≡ t₃) → E ⊢ Γ ▹ t₁ ≡ t₃

  -- Soundness of the inference rules

  module Soundness {I : Set ℓ} (E : I → Eq) (M : SetoidModel ℓm ℓe) (V : ∀ i → M ⊧ E i) where
    open SetoidModel M

    -- In any model M that satisfies the equations E, derived equality is actual equality.

    sound : E ⊢ Γ ▹ t ≡ t' → M ⊧ (t ≐ t')

    sound (hyp i) = V i
    sound (app {op = op} es) ρ = den .cong (refl , λ i → sound (es i) ρ)
    sound (sub {t = t} {t' = t'} e σ) ρ = begin
      ⦅ t  [ σ ] ⦆ .apply ρ  ≈⟨ substitution {M = M} t σ ρ ⟩
      ⦅ t  ⦆ .apply ρ'       ≈⟨ sound e ρ' ⟩
      ⦅ t' ⦆ .apply ρ'      ≈˘⟨ substitution {M = M} t' σ ρ ⟩
      ⦅ t' [ σ ] ⦆ .apply ρ ∎
      where
      open SetoidReasoning (Den _)
      ρ' = ⦅ σ ⦆s ρ

    sound (base x {f} {f'})                          = isEquiv _ M .IsEquivalence.refl {var' x λ()}

    sound (refl t)                                   = isEquiv _ M .IsEquivalence.refl {t}
    sound (sym {t = t} {t' = t'} e)                  = isEquiv _ M .IsEquivalence.sym {x = t} {y = t'} (sound e)
    sound (trans {t₁ = t₁} {t₂ = t₂} {t₃ = t₃} e e') = isEquiv _ M .IsEquivalence.trans {i = t₁} {j = t₂} {k = t₃} (sound e) (sound e')

  -- A term model for E and Γ interprets sort s by Tm Γ s quotiented by E⊢Γ▹_≡_.

  module TermModel {I : Set ℓ} (E : I → Eq) where
    open SetoidModel

    -- Tm Γ s quotiented by E⊢Γ▹_≡_

    TmSetoid : Cxt → Sort → Setoid _ _
    TmSetoid Γ s .Carrier = Tm Γ s
    TmSetoid Γ s ._≈_ = E ⊢ Γ ▹_≡_
    TmSetoid Γ s .isEquivalence .IsEquivalence.refl = refl _
    TmSetoid Γ s .isEquivalence .IsEquivalence.sym  = sym
    TmSetoid Γ s .isEquivalence .IsEquivalence.trans = trans

    -- The interpretation of an operator is simply the operator.
    -- This works because E⊢Γ▹_≡_ is a congruence.

    tmInterp : ∀ {Γ s} → Func (⟦ Ops ⟧s (TmSetoid Γ) s) (TmSetoid Γ s)
    tmInterp .apply (op , ts) = op ∙ ts
    tmInterp .cong (refl , h) = app h

    -- The term model per context Γ.

    M : Cxt → SetoidModel _ _
    M Γ .Den = TmSetoid Γ
    M Γ .den = tmInterp

    -- The identity substitution σ₀ maps variables to themselves.

    σ₀ : {Γ : Cxt} → Sub Γ Γ
    σ₀ x = var' x  λ()

    -- σ₀ acts indeed as identity.

    identity : (t : Tm Γ s) → E ⊢ Γ ▹ t [ σ₀ ] ≡ t
    identity (var x)   = base x
    identity (op ∙ ts) = app λ i → identity (ts i)

    -- Evaluation in the term model is substitution E ⊢ Γ ▹ ⦅t⦆σ ≡ t[σ].
    -- This would even hold "up to the nose" if we had function extensionality.

    evaluation : (t : Tm Δ s) (σ : Sub Γ Δ) → E ⊢ Γ ▹ (⦅_⦆ {M = M Γ} t .apply σ) ≡ (t [ σ ])
    evaluation (var x)   σ = refl (σ x)
    evaluation (op ∙ ts) σ = app (λ i → evaluation (ts i) σ)

    -- The term model satisfies all the equations it started out with.

    satisfies : ∀ i → M Γ ⊧ E i
    satisfies i σ = begin
      ⦅ tₗ ⦆ .apply σ  ≈⟨ evaluation tₗ σ ⟩
      tₗ [ σ ]         ≈⟨ sub (hyp i) σ ⟩
      tᵣ [ σ ]        ≈˘⟨ evaluation tᵣ σ ⟩
      ⦅ tᵣ ⦆ .apply σ ∎
      where
      open SetoidReasoning (TmSetoid _ _)
      tₗ  = E i .Eq.lhs
      tᵣ = E i .Eq.rhs

  -- Birkhoff's completeness theorem (1935):
  -- Any valid consequence is derivable in the equational theory.

  module Completeness {I : Set ℓ} (E : I → Eq) {Γ s} {t t' : Tm Γ s} where
    open TermModel E

    completeness : E ⊃ (t ≐ t') → E ⊢ Γ ▹ t ≡ t'
    completeness V = begin
      t                 ≈˘⟨ identity t ⟩
      t  [ σ₀ ]         ≈˘⟨ evaluation t σ₀ ⟩
      ⦅ t  ⦆ .apply σ₀  ≈⟨ V (M Γ) satisfies σ₀ ⟩
      ⦅ t' ⦆ .apply σ₀  ≈⟨ evaluation t' σ₀ ⟩
      t' [ σ₀ ]         ≈⟨ identity t' ⟩
      t' ∎
      where open SetoidReasoning (TmSetoid Γ s)

-- Q.E.D 2021-05-28

-- -}
-- -}
-- -}
-- -}
-- -}
