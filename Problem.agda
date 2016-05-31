open import Preliminaries
open import Definitions
open import Lemmas
open Nat

module Problem where

  emptyEquiv : ∀ {Γ₁ Γ₂} → · ≡ (Γ₁ , Γ₂) → · ≡ Γ₁ × · ≡ Γ₂
  emptyEquiv (emp x (mulE x₁ x₂)) = emp x x₁ , emp x x₂
  emptyEquiv (decom () x₁ pf)

  emptySubLemma : ∀ {Γ Δ} → Γ ⊢s Δ → Δ empty → Γ empty
  emptySubLemma emptySub empt = empt
  emptySubLemma var ()
  emptySubLemma (comma sub sub₁) (mulE empt empt₁) = mulE (emptySubLemma sub empt) (emptySubLemma sub₁ empt₁)
  emptySubLemma (equiv x sub x₁) empt = lemma (emptySubLemma sub (lemma empt (sym x₁))) (sym x)

  lemmaSingleEmpty : ∀ {Γ A Δ} → Γ decTo sCtx A and Δ → · ≡ Δ → Γ ≡ sCtx A
  lemmaSingleEmpty (SD x) empteq = decom (SD x) (SD x) (emp x x)
  lemmaSingleEmpty (MD1 decpf) empteq = decom (MD1 decpf) (SD sinE) (sym empteq)
  lemmaSingleEmpty (MD2 decpf) empteq = decom (MD2 decpf) (SD sinE) (sym empteq)

  emptyLemma : ∀ {Γ} → Γ empty → · ≡ Γ
  emptyLemma sinE = emp sinE sinE
  emptyLemma (mulE pf pf₁) = emp sinE (mulE pf pf₁)

  reflSub : ∀ {Γ} → Γ ⊢s Γ
  reflSub {·} = emptySub
  reflSub {sCtx x} = var
  reflSub {Γ₁ , Γ₂} = comma reflSub reflSub

  equivSubs : ∀ {Γ Δ} → Γ ≡ Δ → Γ ⊢s Δ
  equivSubs eqpf = equiv eqpf reflSub (refl (snd (findSize _)))

  commSub : ∀ {Γ₁ Γ₂} → (Γ₁ , Γ₂) ⊢s (Γ₂ , Γ₁)
  commSub = equiv (comm (snd (findSize _))) reflSub (refl (snd (findSize _)))

  assocSub : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₁ , (Γ₂ , Γ₃)) ⊢s ((Γ₁ , Γ₂) , Γ₃)
  assocSub = equiv (assoc (snd (findSize _))) reflSub (refl (snd (findSize _)))

  symSub : ∀ {Γ Δ} → Γ ⊢s Δ → Δ ⊢s Γ
  symSub emptySub = emptySub
  symSub var = var
  symSub (comma sub sub₁) = comma (symSub sub) (symSub sub₁)
  symSub (equiv x sub x₁) = equiv (sym x₁) (symSub sub) (sym x)

  transSub : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ⊢s Γ₂ → Γ₂ ⊢s Γ₃ → Γ₁ ⊢s Γ₃
  transSub sub1 sub2 = {! !}

  congSub : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Γ₁ ⊢s Δ₁ → Γ₂ ⊢s Δ₂ → (Γ₁ , Γ₂) ⊢s (Δ₁ , Δ₂)
  congSub sub1 sub2 = comma sub1 sub2

  unitLsub : ∀ {Γ} → (· , Γ) ⊢s Γ
  unitLsub = equiv unitL reflSub (refl (snd (findSize _)))

  unitRsub : ∀ {Γ} → (Γ , ·) ⊢s Γ
  unitRsub = equiv unitR reflSub (refl (snd (findSize _)))

  subLemma : ∀ {Γ Γ' Δ' A} → Γ decTo sCtx A and Γ'
                           → Δ' ⊢s Γ'
                           → Σ[ Δ ∈ Ctx ] (Δ decTo sCtx A and Δ' × Δ ⊢s Γ)
  subLemma (SD x) emptySub = _ , ((SD x) , var)
  subLemma (SD ()) var
  subLemma (SD (mulE x x₁)) (comma sub sub₁) = _ , ((SD (mulE (emptySubLemma sub x) (emptySubLemma sub₁ x₁))) , var)
  subLemma (MD1 dec) (comma sub sub₁) with subLemma dec sub
  ... | Δ , dec2 , sub2 = _ , ((MD1 dec2) , comma sub2 sub₁)
  subLemma (MD2 dec) (comma sub sub₁) with subLemma dec sub₁
  ... | Δ , dec2 , sub2 = _ , (MD2 dec2 , comma sub sub2)
  subLemma dec (equiv x₁ sub x₂) = {! !}

  dan : (Γ Γ' Γ₁' Γ₂' : Ctx) → Γ ⊢s Γ' → Γ' ≡ (Γ₁' , Γ₂') → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] ((Γ₁ , Γ₂) ≡ Γ × Γ₁ ⊢s Γ₁' × Γ₂ ⊢s Γ₂')
  dan .· .· Γ₁' Γ₂' emptySub (emp x (mulE x₁ x₂)) = · , · , emp (mulE x x) x , equiv (emp x x) emptySub (emp x x₁) , equiv (emp x x) emptySub (emp x x₂)
  dan .· .· Γ₁' Γ₂' emptySub (decom () x₁ pf)
  dan ._ ._ Γ₁' Γ₂' var (emp () x₁)
  dan ._ ._ Γ₁' Γ₂' (var {A}) (decom (SD em) (MD1 x₁) eq) = sCtx A , · , decom (MD1 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE) , equiv (refl s1) var (sym (lemmaSingleEmpty x₁ (fst (emptyEquiv (trans (emptyLemma em) eq (s0 sinE) (s0 em) (s0 (lemma em eq))))))) , equiv (emp sinE sinE) emptySub (snd (emptyEquiv (trans (emptyLemma em) eq (s0 sinE) (s0 em) (s0 (lemma em eq)))))
  dan ._ ._ Γ₁' Γ₂' (var {A}) (decom (SD em) (MD2 x₁) eq) = · , sCtx A , decom (MD2 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE) , equiv (emp sinE sinE) emptySub (fst (emptyEquiv (trans (emptyLemma em) eq (s0 sinE) (s0 em) (s0 (lemma em eq))))) , equiv (refl s1) var (sym (lemmaSingleEmpty x₁ (snd (emptyEquiv (trans (emptyLemma em) eq (s0 sinE) (s0 em) (s0 (lemma em eq)))))))
  dan Γ Γ' Γ₁' Γ₂' (equiv {Γ' = Γ''}{Δ' = Δ'} x sub x₁) pf with findSize Δ'
  ... | n , size1 with equivSameSize (sym x₁) size1
  ... | size2 with dan _ _ _ _ sub (trans x₁ pf size1 size2 (equivSameSize (sym pf) size2))
  ... | Γ1 , Γ2 , split , sub1 , sub2 with findSize Γ''
  ... | m , size3 = Γ1 , Γ2 , trans split (sym x) (equivSameSize split size3) size3 (equivSameSize x size3) , sub1 , sub2
  dan ._ ._ Γ₁' Γ₂' (comma sub sub₁) (emp (mulE x x₁) (mulE x₂ x₃)) = · , · , emp (mulE sinE sinE) (mulE (emptySubLemma sub x) (emptySubLemma sub₁ x₁)) , equiv (emp sinE sinE) emptySub (emp sinE x₂) , equiv (emp sinE sinE) emptySub (emp sinE x₃)
  dan .(Γ₁ , Γ₂) .(Δ₁ , Δ₂) Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (decom (MD1 {A}{Δ1} dec1) (MD1 {.A}{Γ1} dec2) pf) = {! !}
  dan _ _ Γ₁ Γ₂' (comma sub1 sub2) (decom (MD1 dec1) (MD2 dec2) pf) = {! !}
  dan _ _ Γ₁' Γ₂ (comma sub1 sub2) (decom (MD2 dec1) (MD1 dec2) pf) = {! !}
  dan _ _ Γ₁ Γ₂' (comma sub1 sub2) (decom (MD2 dec1) (MD2 dec2) pf) = {! !}
