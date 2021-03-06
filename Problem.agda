open import Preliminaries
open import Definitions
open import Lemmas
open Nat

module Problem where

  dan : {n : Nat} → (Γ Γ' Γ₁' Γ₂' : Ctx) → Γ ⊢s Γ' → Γ' ≡ (Γ₁' , Γ₂') → Γ size n → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] ((Γ₁ , Γ₂) ≡ Γ × Γ₁ ⊢s Γ₁' × Γ₂ ⊢s Γ₂')
  dan {Z} Γ Γ' Γ₁' Γ₂' sub eq (s0 x) with lemma (emptySubLemma (symSub sub) x) eq
  dan {Z} Γ Γ' Γ₁' Γ₂' sub eq (s0 x) | mulE res res₁ = · , · , emp (mulE sinE sinE) x , equiv (emp sinE sinE) emptySub (emp sinE res) , equiv (emp sinE sinE) emptySub (emp sinE res₁)
  dan {S n} Γ Γ' Γ₁' Γ₂' sub (emp x (mulE x₁ x₂)) size = · , · , emp (mulE sinE sinE) (emptySubLemma sub x) , equiv (emp sinE sinE) emptySub (emp sinE x₁) , equiv (emp sinE sinE) emptySub (emp sinE x₂)
  dan .· .· Γ₁' Γ₂' emptySub (decom () x₁ pf)
  dan _ _ _ Γ₂' var (decom (SD x) SD1 pf) size = _ , · , unitR size , var , equiv (emp sinE sinE) emptySub (trans (emptyLemma x) pf (s0 sinE) (s0 x) (s0 (emptyEquivLemma x pf)))
  dan _ _ Δ' _ var (decom (SD x) SD2 pf) size = · , _ , unitL size , equiv (emp sinE sinE) emptySub (trans (emptyLemma x) pf (s0 sinE) (s0 x) (s0 (emptyEquivLemma x pf))) , var
  dan ._ ._ Γ₁' Γ₂' (var {A}) (decom (SD em) (MD1 x₁) eq) size = sCtx A , · , decom (MD1 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE) , equiv (refl s1) var (sym (lemmaSingleEmpty x₁ (fst (emptyEquiv (trans (emptyLemma em) eq (s0 sinE) (s0 em) (s0 (lemma em eq))))))) , equiv (emp sinE sinE) emptySub (snd (emptyEquiv (trans (emptyLemma em) eq (s0 sinE) (s0 em) (s0 (lemma em eq)))))
  dan ._ ._ Γ₁' Γ₂' (var {A}) (decom (SD em) (MD2 x₁) eq) size = · , sCtx A , decom (MD2 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE) , equiv (emp sinE sinE) emptySub (fst (emptyEquiv (trans (emptyLemma em) eq (s0 sinE) (s0 em) (s0 (lemma em eq))))) , equiv (refl s1) var (sym (lemmaSingleEmpty x₁ (snd (emptyEquiv (trans (emptyLemma em) eq (s0 sinE) (s0 em) (s0 (lemma em eq)))))))
  dan Γ Γ' Γ₁' Γ₂' (equiv {Γ' = Γ''}{Δ' = Δ'} x sub x₁) pf size with findSize Δ'
  ... | n , size1 with equivSameSize (sym x₁) size1
  ... | size2 with dan _ _ _ _ sub (trans x₁ pf size1 size2 (equivSameSize (sym pf) size2)) (equivSameSize (sym x) size)
  ... | Γ1 , Γ2 , split , sub1 , sub2 with findSize Γ''
  ... | m , size3 = Γ1 , Γ2 , trans split (sym x) (equivSameSize split size3) size3 (equivSameSize x size3) , sub1 , sub2
  dan .(Γ₁ , Γ₂) _ _ Γ₂' (comma {Γ₁}{Γ₂} sub1 sub2) (decom SD1 SD1 pf) size = _ , _ , refl size , sub1 , equiv (refl (snd (findSize _))) sub2 pf
  dan _ _ Γ₁' _ (comma sub sub₁) (decom SD1 SD2 pf) size = _ , _ , comm (snd (findSize _)) , equiv (refl (snd (findSize _))) sub₁ pf , sub
  dan _ _ _ Δ' (comma sub sub₁) (decom SD2 SD1 pf) size = _ , _ , comm (snd (findSize _)) , sub₁ , equiv (refl (snd (findSize _))) sub pf
  dan _ _ Γ₁' _ (comma sub sub₁) (decom SD2 SD2 pf) size = _ , _ , refl size , equiv (refl (snd (findSize _))) sub pf , sub₁
  dan {S n} .(Γ₁ , Γ₂) .(Δ₁ , Δ₂) Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (decom (MD1 {A}{Δ1} dec1) (MD1 {.A}{Γ1} dec2) pf) size with subLemma2 sub1 dec1
  ... | (Γ'' , dec3 , sub3) with dan _ _ _ _ (comma sub3 sub2) pf (decdSize (MD1 dec3) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma dec2 sub4
  ... | (Γ5 , dec4 , sub6) = Γ5 , Γ4 , decom (MD1 dec4) (MD1 dec3) eqpf , sub6 , sub5
  dan {S n} .(Γ₁ , Γ₂) .(Δ₁ , Δ₂) Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (decom (MD1 {A}{Δ1} dec1) (MD2 {.A}{Γ2} dec2) pf) size with subLemma2 sub1 dec1
  ... | (Γ'' , dec3 , sub3) with dan _ _ _ _ (comma sub3 sub2) pf (decdSize (MD1 dec3) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma dec2 sub5
  ... | (Γ5 , dec4 , sub6) = Γ3 , Γ5 , decom (MD2 dec4) (MD1 dec3) eqpf , sub4 , sub6
  dan {S n} .(Γ₁ , Γ₂) .(Δ₁ , Δ₂) Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (decom (MD2 {A}{Δ2} dec1) (MD1 {.A}{Γ1} dec2) pf) size with subLemma2 sub2 dec1
  ... | (Γ'' , dec3 , sub3) with dan _ _ _ _ (comma sub1 sub3) pf (decdSize (MD2 dec3) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma dec2 sub4
  ... | (Γ5 , dec4 , sub6) = Γ5 , Γ4 , decom (MD1 dec4) (MD2 dec3) eqpf , sub6 , sub5
  dan {S n} .(Γ₁ , Γ₂) .(Δ₁ , Δ₂) Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (decom (MD2 {A}{Δ2} dec1) (MD2 {.A}{Γ2} dec2) pf) size with subLemma2 sub2 dec1
  ... | (Γ'' , dec3 , sub3) with dan _ _ _ _ (comma sub1 sub3) pf (decdSize (MD2 dec3) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma dec2 sub5
  ... | (Γ5 , dec4 , sub6) = Γ3 , Γ5 , decom (MD2 dec4) (MD2 dec3) eqpf , sub4 , sub6
  dan {S n} _ _ Γ₁' Γ₂ (comma sub sub₁) (decom SD1 (MD1 x₁) pf) size with subLemma2 sub (SD sinE) | findSize _
  ... | (Γ'' , dec3 , sub3) | p , size1 with dan _ _ _ _ (comma sub3 sub₁) (trans (unitL size1) pf (equivSameSize (unitL size1) size1) size1 (equivSameSize (sym pf) size1)) (decdSize (MD1 dec3) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma x₁ sub4
  ... | (Γ5 , dec4 , sub6) = Γ5 , Γ4 , decom (MD1 dec4) (MD1 dec3) eqpf , sub6 , sub5
  dan {S n} _ _ Γ₁' Γ₂' (comma sub sub₁) (decom SD1 (MD2 x₁) pf) size with subLemma2 sub (SD sinE) | findSize _
  ... | (Γ'' , dec3 , sub3) | p , size1 with dan _ _ _ _ (comma sub3 sub₁) (trans (unitL size1) pf (equivSameSize (unitL size1) size1) size1 (equivSameSize (sym pf) size1)) (decdSize (MD1 dec3) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma x₁ sub5
  ... | (Γ5 , dec4 , sub6) = Γ3 , Γ5 , decom (MD2 dec4) (MD1 dec3) eqpf , sub4 , sub6
  dan {S n} _ _ Γ₁' Γ₂ (comma sub sub₁) (decom SD2 (MD1 x₁) pf) size with subLemma2 sub₁ (SD sinE) | findSize _
  ... | (Γ'' , dec3 , sub3) | p , size1 with dan _ _ _ _ (comma sub sub3) (trans (unitR size1) pf (equivSameSize (unitR size1) size1) size1 (equivSameSize (sym pf) size1)) (decdSize (MD2 dec3) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma x₁ sub4
  ... | (Γ5 , dec4 , sub6) = Γ5 , Γ4 , decom (MD1 dec4) (MD2 dec3) eqpf , sub6 , sub5
  dan {S n} _ _ Γ₁' Γ₂' (comma sub sub₁) (decom SD2 (MD2 x₁) pf) size with subLemma2 sub₁ (SD sinE) | findSize _
  ... | (Γ'' , dec3 , sub3) | p , size1 with dan _ _ _ _ (comma sub sub3) (trans (unitR size1) pf (equivSameSize (unitR size1) size1) size1 (equivSameSize (sym pf) size1)) (decdSize (MD2 dec3) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma x₁ sub5
  ... | (Γ5 , dec4 , sub6) = Γ3 , Γ5 , decom (MD2 dec4) (MD2 dec3) eqpf , sub4 , sub6
  dan {S n} _ _ _ Δ' (comma sub sub₁) (decom (MD1 x) SD1 pf) size with subLemma2 sub x | findSize _
  ... | (Γ'' , dec , sub3) | p , size1 with dan _ _ _ _ (comma sub3 sub₁) (trans pf (sym (unitL size1)) (equivSameSize pf size1) size1 (equivSameSize (unitL size1) size1)) (decdSize (MD1 dec) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma (SD sinE) sub4
  ... | (Γ5 , dec4 , sub6) = Γ5 , Γ4 , decom (MD1 dec4) (MD1 dec) eqpf , sub6 , sub5
  dan {S n} _ _ Δ' _ (comma sub sub₁) (decom (MD1 x) SD2 pf) size with subLemma2 sub x | findSize _
  ... | (Γ'' , dec , sub3) | p , size1 with dan _ _ _ _ (comma sub3 sub₁) (trans pf (sym (unitR size1)) (equivSameSize pf size1) size1 (equivSameSize (unitR size1) size1)) (decdSize (MD1 dec) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma (SD sinE) sub5
  ... | (Γ5 , dec4 , sub6) = Γ3 , Γ5 , decom (MD2 dec4) (MD1 dec) eqpf , sub4 , sub6
  dan {S n} _ _ _ Δ' (comma sub sub₁) (decom (MD2 x) SD1 pf) size with subLemma2 sub₁ x | findSize _
  ... | (Γ'' , dec , sub3) | p , size1 with dan _ _ _ _ (comma sub sub3) (trans pf (sym (unitL size1)) (equivSameSize pf size1) size1 (equivSameSize (unitL size1) size1)) (decdSize (MD2 dec) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma (SD sinE) sub4
  ... | (Γ5 , dec4 , sub6) = Γ5 , Γ4 , decom (MD1 dec4) (MD2 dec) eqpf , sub6 , sub5
  dan {S n} _ _ Δ' _ (comma sub sub₁) (decom (MD2 x) SD2 pf) size with subLemma2 sub₁ x | findSize _
  ... | (Γ'' , dec , sub3) | p , size1 with dan _ _ _ _ (comma sub sub3) (trans pf (sym (unitR size1)) (equivSameSize pf size1) size1 (equivSameSize (unitR size1) size1)) (decdSize (MD2 dec) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma (SD sinE) sub5
  ... | (Γ5 , dec4 , sub6) = Γ3 , Γ5 , decom (MD2 dec4) (MD2 dec) eqpf , sub4 , sub6
