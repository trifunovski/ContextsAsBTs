open import Preliminaries
open Nat

module Definitions where

data Tp : Set where
  P : Tp
  Q : Tp

data Ctx : Set where
  · : Ctx
  sCtx : Tp → Ctx
  _,_ : Ctx → Ctx → Ctx

data _empty : Ctx → Set where
  sinE : · empty
  mulE : ∀ {Γ₁ Γ₂} → Γ₁ empty → Γ₂ empty → (Γ₁ , Γ₂) empty

data _decTo_and_ : Ctx → Ctx → Ctx → Set where
  SD : ∀{A Γ} → Γ empty → sCtx A decTo sCtx A and Γ
  MD1 : ∀ {A Γ₁' Γ₁ Γ₂} → Γ₁ decTo sCtx A and Γ₁' → (Γ₁ , Γ₂) decTo sCtx A and (Γ₁' , Γ₂)
  MD2 : ∀ {A Γ₂' Γ₁ Γ₂} → Γ₂ decTo sCtx A and Γ₂' → (Γ₁ , Γ₂) decTo sCtx A and (Γ₁ , Γ₂')

data _≡_ : Ctx → Ctx → Set where
  emp : ∀{Γ₁ Γ₂} → Γ₁ empty → Γ₂ empty → Γ₁ ≡ Γ₂
  decom : ∀{Γ Γ' Δ Δ' A} → Γ decTo sCtx A and Γ' → Δ decTo sCtx A and Δ' → Γ' ≡ Δ' → Γ ≡ Δ

data _⊢s_ : Ctx → Ctx → Set where
  emptySub : · ⊢s ·
  var : ∀ {A} → (sCtx A) ⊢s (sCtx A)
  comma : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Γ₁ ⊢s Δ₁ → Γ₂ ⊢s Δ₂ → (Γ₁ , Γ₂) ⊢s (Δ₁ , Δ₂)
  equiv : ∀ {Γ Γ' Δ Δ'} → Γ ≡ Γ' → Γ' ⊢s Δ' → Δ' ≡ Δ → Γ ⊢s Δ

data _size_ : Ctx → Nat → Set where
  s0 : {Γ : Ctx} → Γ empty → Γ size 0
  s1 : {A : Tp} → sCtx A size 1
  sm : {Γ Δ : Ctx}{A : Tp}{n : Nat} → Γ decTo sCtx A and Δ → Δ size n → Γ size (S n)
