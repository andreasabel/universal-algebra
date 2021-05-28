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

⟦ Op ◃ Ar / sort ⟧s ξ s .isEquivalence .IsEquivalence.refl                        = refl , λ i → Setoid.refl (ξ (sort _ i))
⟦ Op ◃ Ar / sort ⟧s ξ s .isEquivalence .IsEquivalence.sym   (refl , h)            = refl , λ i → Setoid.sym  (ξ (sort _ i)) (h i)
⟦ Op ◃ Ar / sort ⟧s ξ s .isEquivalence .IsEquivalence.trans (refl , g) (refl , h) = refl , λ i → Setoid.trans (ξ (sort _ i)) (g i) (h i)

-- A multi-sorted algebra is an indexed container.
--
-- * Sorts are indexes.
-- * Operators are commands.
-- * Arities/argument are responses.
--
-- Closed terms (initial model) are given by the W type for a container.

-- Models

module _ (Sort : Set ℓs) (C : Container Sort Sort ℓc ℓr) where
  open Container C renaming
    ( Command  to Op
    ; Response to Arity
    ; next     to sort
    )

  variable
    s s'   : Sort
    op op' : Op s

  -- A model is given by an interpretation (Den s) for each sort s
  -- plus an interpretation (den o) for each operator o.

  record SetModel ℓm : Set (ℓs ⊔ ℓc ⊔ ℓr ⊔ suc ℓm) where
    field
      Den : Sort → Set ℓm
      den : {s : Sort} → ⟦ C ⟧ Den s → Den s
      -- den : {s : Sort} (o : Op s) (args : (i : Arity o) → Den (sort o i)) → Den s

  record SetoidModel ℓm ℓe : Set (ℓs ⊔ ℓc ⊔ ℓr ⊔ suc (ℓm ⊔ ℓe)) where
    field
      Den : Sort → Setoid ℓm ℓe

    -- ⟪_⟫ : Sort → Set ℓm
    -- ⟪ s ⟫ = Den s .Carrier

    field
      den : {s : Sort} → Func (⟦ C ⟧s Den s) (Den s)


-- Open terms

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

  -- This is also covered in the standard library FreeMonad module,
  -- albeit with the restriction that the operator and variable sets
  -- have the same size.

  Cxt = Sort → Set ℓc

  variable
    Γ Δ : Cxt

  module NewSymbols' (Var : Cxt) where

    -- We keep the same sorts, but add a nullary operator for each variable

    C⁺ : Container Sort Sort ℓc ℓr
    C⁺ = C ⋆C Var

    -- Terms are then given by the W-type for the extended container.

    Tm = W C⁺

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

      -- Interpretation of terms is iteration on the W-type

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

      Equal : ∀{s} (t t' : Tm s) → Set _
      Equal {s} t t' = ∀ (ρ : Env .Carrier) → ⦅ t ⦆ .apply ρ ~ ⦅ t' ⦆ .apply ρ
        where _~_ = Den s ._≈_

      isEquiv : IsEquivalence (Equal {s})
      isEquiv {s = s} .IsEquivalence.refl  ρ      = Den s .Setoid.refl
      isEquiv {s = s} .IsEquivalence.sym   e ρ    = Den s .Setoid.sym (e ρ)
      isEquiv {s = s} .IsEquivalence.trans e e' ρ = Den s .Setoid.trans (e ρ) (e' ρ)

    -- Equal terms in a model

    -- _⊧_≐_ = Interpretation.Equal

  open NewSymbols' using (Tm; var; var'; _∙_; module Interpretation)
  open Interpretation using (Equal; isEquiv)

  Sub : (Γ Δ : Cxt) → Set _
  Sub Γ Δ = ∀{s} (x : Δ s) → Tm Γ s

  variable
    t t' t₁ t₂ t₃ : Tm Γ s
    ts ts' : (i : Arity op) → Tm Γ (sort _ i)
    σ σ' : Sub Γ Δ

  -- Substitution

  _[_] : (t : Tm Δ s) (σ : Sub Γ Δ) → Tm Γ s
  (var x  ) [ σ ] = σ x
  (op ∙ ts) [ σ ] = op ∙ λ i → ts i [ σ ]

  -- Substitution lemma

  module _ {M : SetoidModel ℓm ℓe} where
    open SetoidModel M

    ⦅_⦆ : ∀{Γ s} → Tm Γ s → Func (Interpretation.Env Γ M) (Den s)
    ⦅_⦆ {Γ} = Interpretation.⦅_⦆ Γ M

    ⦅_⦆s : Sub Γ Δ → Interpretation.Env Γ M .Carrier → Interpretation.Env Δ M .Carrier
    ⦅ σ ⦆s ρ x = ⦅ σ x ⦆ .apply ρ

    _~_ : Den s .Carrier → Den s .Carrier → Set _
    _~_ {s = s} = Den s ._≈_

    substitution : (t : Tm Δ s) (σ : Sub Γ Δ) (ρ : Interpretation.Env Γ M .Carrier) →
      ⦅ t [ σ ] ⦆ .apply ρ ~ ⦅ t ⦆ .apply (⦅ σ ⦆s ρ)
    substitution (var x)   σ ρ = Den _ .Setoid.refl
    substitution (op ∙ ts) σ ρ = den .cong (refl , λ i → substitution (ts i) σ ρ)

  record Eq : Set (ℓs ⊔ suc ℓc ⊔ ℓr) where
    constructor _≐_
    field
      {cxt} : Sort → Set ℓc
      {srt} : Sort
      lhs   : Tm cxt srt
      rhs   : Tm cxt srt

  _⊧_ : (M : SetoidModel ℓm ℓe) (eq : Eq) → Set _
  M ⊧ (t ≐ t') = Equal _ M t t'

  module _ {ℓm ℓe} where

    Valid : Eq → Set _
    Valid eq = ∀ (M : SetoidModel ℓm ℓe) → M ⊧ eq

    Valids : {I : Set ℓ} (E : I → Eq) → Set _
    Valids E = ∀ i → Valid (E i)

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

  module Soundness {I : Set ℓ} (E : I → Eq) (M : SetoidModel ℓm ℓe) (V : ∀ i → M ⊧ E i) where
    open SetoidModel M

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

  -- data _⊢_∋_≡_ : (Γ Δ : Cxt) (σ σ' : Sub Γ Δ) → Set _ where

  module TermModel {I : Set ℓ} (E : I → Eq) where
    open SetoidModel

    TmSetoid : Cxt → Sort → Setoid _ _
    TmSetoid Γ s .Carrier = Tm Γ s
    TmSetoid Γ s ._≈_ = E ⊢ Γ ▹_≡_
    TmSetoid Γ s .isEquivalence .IsEquivalence.refl = refl _
    TmSetoid Γ s .isEquivalence .IsEquivalence.sym  = sym
    TmSetoid Γ s .isEquivalence .IsEquivalence.trans = trans

    tmInterp : ∀ {Γ s} → Func (⟦ C ⟧s (TmSetoid Γ) s) (TmSetoid Γ s)
    tmInterp .apply (op , ts) = op ∙ ts
    tmInterp .cong (refl , h) = app h

    M : Cxt → SetoidModel _ _
    M Γ .Den = TmSetoid Γ
    M Γ .den = tmInterp

    -- Identity substitution

    σ₀ : {Γ : Cxt} → Sub Γ Γ
    σ₀ x = W.sup (inj₁ x , λ())

    identity : (t : Tm Γ s) → E ⊢ Γ ▹ t [ σ₀ ] ≡ t
    identity (var x)   = base x
    identity (op ∙ ts) = app λ i → identity (ts i)

    identity′ : (t : Tm Γ s) → E ⊢ Γ ▹ (⦅_⦆ {M = M Γ} t .apply σ₀) ≡ t
    identity′ (var x)   = base x
    identity′ (op ∙ ts) = app λ i → identity′ (ts i)

    -- This property has problems because the TmSetoid is defined for a fixed Γ
    -- -- evaluation : (t : Tm Δ s) (σ : Sub Γ Δ) → E ⊢ Γ ▹ (⦅ t ⦆ .apply σ) ≡ (t [ σ ])
    -- evaluation : (t : Tm Δ s) (σ : Sub Γ Δ) → E ⊢ Γ ▹ (⦅_⦆ {M = M Δ} t .apply σ) ≡ (t [ σ ])
    -- evaluation (var x)   σ = refl (σ x)
    -- evaluation (op ∙ ts) σ = app (λ i → evaluation (ts i) σ)


  -- If

  module Completeness {I : Set ℓ} (E : I → Eq) {Γ s} {t t' : Tm Γ s} where
    open TermModel E

    completeness : E ⊃ (t ≐ t') → E ⊢ Γ ▹ t ≡ t'
    completeness V = begin
      t                ≈˘⟨ identity′ t ⟩
      ⦅ t  ⦆ .apply σ₀  ≈⟨  V (M Γ) (λ i → {!hyp i!}) σ₀   ⟩
      ⦅ t' ⦆ .apply σ₀  ≈⟨ identity′ t' ⟩
      t' ∎
      where open SetoidReasoning (TmSetoid Γ s)

    -- completeness : Valid (ℓs ⊔ ℓc ⊔ ℓr) ((ℓs ⊔ suc ℓc ⊔ ℓr ⊔ ℓ)) (t ≐ t') → E ⊢ Γ ▹ t ≡ t'
    -- completeness V = begin
    --   t              ≈˘⟨ identity t ⟩
    --   t  [ σ₀ ]       ≈⟨ {! V (M Γ) σ₀ !} ⟩
    --   ⦅ t  ⦆ .apply σ₀ ≈⟨  V (M Γ) σ₀  ⟩
    --   ⦅ t' ⦆ .apply σ₀ ≈⟨ {! V (M Γ) σ₀ !} ⟩
    --   t' [ σ₀ ]       ≈⟨ identity t' ⟩
    --   t' ∎
    --   where open SetoidReasoning (TmSetoid Γ s)

-- -}
-- -}
-- -}
-- -}
-- -}
