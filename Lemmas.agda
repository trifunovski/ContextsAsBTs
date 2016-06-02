open import Preliminaries
open import Definitions
open Nat

module Lemmas where

  lemmaEmptyDecom : ∀{Γ A Δ} → Γ empty → Γ decTo sCtx A and Δ → Void
  lemmaEmptyDecom sinE ()
  lemmaEmptyDecom (mulE empt empt₁) (MD1 decpf) = lemmaEmptyDecom empt decpf
  lemmaEmptyDecom (mulE empt empt₁) (MD2 decpf) = lemmaEmptyDecom empt₁ decpf
  lemmaEmptyDecom (mulE () empt₁) SD1
  lemmaEmptyDecom (mulE empt ()) SD2

  lemma : ∀{Γ Δ} → Γ empty → Γ ≡ Δ → Δ empty
  lemma sinE (emp x x₁) = x₁
  lemma sinE (decom x x₁ pf) = abort (lemmaEmptyDecom sinE x)
  lemma (mulE empt empt₁) (emp x x₁) = x₁
  lemma (mulE {Γ₁}{Γ₂} empt empt₁) (decom x x₁ pf) = abort (lemmaEmptyDecom (mulE empt empt₁) x)

  addEmptyCtx : ∀ {Γ Δ X} → Γ ≡ Δ → X empty → (Γ , X) ≡ Δ × (X , Γ) ≡ Δ × Γ ≡ (X , Δ) × Γ ≡ (Δ , X)
  addEmptyCtx (emp x x₁) empt = emp (mulE x empt) x₁ , emp (mulE empt x) x₁ , emp x (mulE empt x₁) , emp x (mulE x₁ empt)
  addEmptyCtx (decom x x₁ eqpf) empt with addEmptyCtx eqpf empt
  ... | res1 , res2 , res3 , res4 = decom (MD1 x) x₁ res1 , decom (MD2 x) x₁ res2 , decom x (MD2 x₁) res3 , decom x (MD1 x₁) res4

  emptyCtxSizeLemma : ∀ {Γ Δ n} → Γ empty → Δ size n → (Γ , Δ) size n
  emptyCtxSizeLemma empt (s0 x) = s0 (mulE empt x)
  emptyCtxSizeLemma empt s1 = sm (MD2 (SD empt)) (s0 (mulE empt empt))
  emptyCtxSizeLemma empt (sm x size) = sm (MD2 x) (emptyCtxSizeLemma empt size)

  addSizesLemma : ∀{Γ Δ n m} → Γ size n → Δ size m → (Γ , Δ) size (n + m)
  addSizesLemma {·} (s0 x) (s0 x₁) = s0 (mulE x x₁)
  addSizesLemma {·} (s0 x) s1 = sm (MD2 (SD x)) (s0 (mulE x x))
  addSizesLemma {·} (s0 x) (sm x₁ size2) = sm (MD2 x₁) (addSizesLemma (s0 x) size2)
  addSizesLemma {·} (sm () size1) size2
  addSizesLemma {sCtx x} (s0 ()) size2
  addSizesLemma {sCtx x} s1 (s0 x₁) = sm (MD1 (SD x₁)) (s0 (mulE x₁ x₁))
  addSizesLemma {sCtx x} s1 s1 = sm (MD2 (SD sinE)) (sm (MD1 (SD sinE)) (s0 (mulE sinE sinE)))
  addSizesLemma {sCtx x} s1 (sm x₁ size2) = sm (MD2 x₁) (addSizesLemma s1 size2)
  addSizesLemma {sCtx A} (sm (SD x) (s0 x₁)) (s0 x₂) = addSizesLemma s1 (s0 x₂)
  addSizesLemma {sCtx A₁} (sm (SD x) (s0 x₁)) s1 = addSizesLemma s1 s1
  addSizesLemma {sCtx A} (sm (SD x) (s0 x₁)) (sm x₂ size2) = sm (MD2 x₂) (addSizesLemma s1 size2)
  addSizesLemma {sCtx A₁} (sm (SD ()) s1) size2
  addSizesLemma {sCtx A} (sm (SD x) (sm x₁ size1)) size2 = abort (lemmaEmptyDecom x x₁)
  addSizesLemma {Γ₁ , Γ₂} (s0 (mulE x x₁)) (s0 x₂) = s0 (mulE (mulE x x₁) x₂)
  addSizesLemma {Γ₁ , Γ₂} (s0 (mulE x x₁)) s1 = sm (MD2 (SD x₁)) (s0 (mulE (mulE x x₁) x₁))
  addSizesLemma {Γ₁ , Γ₂} (s0 (mulE x x₁)) (sm x₂ size2) = sm (MD2 x₂) (emptyCtxSizeLemma (mulE x x₁) size2)
  addSizesLemma {Γ₁ , Γ₂} (sm x size1) (s0 x₁) = sm (MD1 x) (addSizesLemma size1 (s0 x₁))
  addSizesLemma {Γ₁ , Γ₂} (sm x size1) s1 = sm (MD1 x) (addSizesLemma size1 s1)
  addSizesLemma {Γ₁ , Γ₂} (sm x size1) (sm x₁ size2) = sm (MD1 x) (addSizesLemma size1 (sm x₁ size2))

  findSize : (Γ : Ctx) → Σ[ n ∈ Nat ] (Γ size n)
  findSize · = Z , s0 sinE
  findSize (sCtx x) = S Z , s1
  findSize (Γ₁ , Γ₂) with findSize Γ₁ | findSize Γ₂
  ... | (n1 , size1) | (n2 , size2) = (n1 + n2) , addSizesLemma size1 size2

  refl : ∀{Γ n} → Γ size n → Γ ≡ Γ
  refl (s0 x) = emp x x
  refl s1 = decom (SD sinE) (SD sinE) (emp sinE sinE)
  refl (sm x size) = decom x x (refl size)

  comm : ∀{Γ₁ Γ₂ n} → (Γ₁ , Γ₂) size n → (Γ₁ , Γ₂) ≡ (Γ₂ , Γ₁)
  comm (s0 (mulE x x₁)) = emp (mulE x x₁) (mulE x₁ x)
  comm (sm (MD1 x) size) = decom (MD1 x) (MD2 x) (comm size)
  comm (sm (MD2 x) size) = decom (MD2 x) (MD1 x) (comm size)
  comm (sm SD1 size) = decom SD1 SD2 (refl size)
  comm (sm SD2 size) = decom SD2 SD1 (refl size)


  sym : ∀{Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₁
  sym (emp x x₁) = emp x₁ x
  sym (decom x x₁ pf) = decom x₁ x (sym pf)

  cong : ∀{Γ Γ' Δ Δ'} → Γ ≡ Δ → Γ' ≡ Δ' → (Γ , Γ') ≡ (Δ , Δ')
  cong (emp x x₁) (emp x₂ x₃) = emp (mulE x x₂) (mulE x₁ x₃)
  cong (emp x x₁) (decom x₂ x₃ pf2) = decom (MD2 x₂) (MD2 x₃) (cong (emp x x₁) pf2)
  cong (decom x x₁ pf1) (emp x₂ x₃) = decom (MD1 x) (MD1 x₁) (cong pf1 (emp x₂ x₃))
  cong (decom x x₁ pf1) (decom x₂ x₃ pf2) = decom (MD1 x) (MD1 x₁) (cong pf1 (decom x₂ x₃ pf2))

  transHelper : ∀{Γ A B Γ₁ Γ₂} → Γ decTo sCtx A and Γ₁ → Γ decTo sCtx B and Γ₂ → Either (sCtx A ≡ sCtx B × Γ₁ ≡ Γ₂) (Σ[ Δ₁ ∈ Ctx ] Σ[ Δ₂ ∈ Ctx ] (Γ₁ decTo sCtx B and Δ₁ × Γ₂ decTo sCtx A and Δ₂ × Δ₁ ≡ Δ₂))
  transHelper {·} () dec2
  transHelper {sCtx A} (SD x) (SD x₁) = Inl ((decom (SD x₁) (SD x₁) (emp x₁ x₁)) , (emp x x₁))
  transHelper {_ , Γ₂} SD1 SD1 = Inl ((decom (SD sinE) (SD sinE) (emp sinE sinE)) , (refl (snd (findSize _))))
  transHelper {_ , _} SD1 SD2 = Inr (· , · , SD sinE , SD sinE , emp sinE sinE)
  transHelper {_ , _} SD2 SD1 = Inr (· , · , SD sinE , SD sinE , emp sinE sinE)
  transHelper {Γ₂ , _} SD2 SD2 = Inl ((decom (SD sinE) (SD sinE) (emp sinE sinE)) , (refl (snd (findSize _))))
  transHelper {_ , Γ₂} SD1 (MD1 (SD x)) with addEmptyCtx (refl (snd (findSize _))) x
  ... | res1 , res2 , res3 , res4 = Inl ((decom (SD x) (SD x) (emp x x)) , res3)
  transHelper {_ , Γ₁} SD1 (MD2 dec2) = Inr (_ , _ , dec2 , SD1 , refl (snd (findSize _)))
  transHelper {Γ₁ , _} SD2 (MD1 dec2) = Inr (_ , _ , dec2 , SD2 , refl (snd (findSize _)))
  transHelper {Γ₁ , _} SD2 (MD2 (SD x)) with addEmptyCtx (refl (snd (findSize _))) x
  ... | res1 , res2 , res3 , res4 = Inl ((decom (SD x) (SD x) (emp x x)) , res4)
  transHelper {_ , Γ₂} (MD1 (SD x)) SD1 with addEmptyCtx (refl (snd (findSize _))) x
  ... | res1 , res2 , res3 , res4 = Inl ((decom (SD x) (SD x) (emp x x)) , res2)
  transHelper {Γ , _} (MD1 dec1) SD2 = Inr (_ , _ , SD2 , dec1 , refl (snd (findSize _)))
  transHelper {_ , Γ₂} (MD2 dec1) SD1 = Inr (_ , _ , SD1 , dec1 , refl (snd (findSize _)))
  transHelper {Γ₂ , _} (MD2 (SD x)) SD2 with addEmptyCtx (refl (snd (findSize _))) x
  ... | res1 , res2 , res3 , res4 = Inl ((decom (SD x) (SD x) (emp x x)) , res1)
  transHelper {Γ₁ , Γ₂} (MD1 dec1) (MD1 dec2) with transHelper dec1 dec2
  transHelper {Γ₁ , Γ₂} (MD1 dec1) (MD1 dec2) | Inl (emp () x₁ , ctxeq)
  transHelper {Γ₁ , Γ₂} (MD1 dec1) (MD1 dec2) | Inl (decom (SD x) (SD x₁) seq , ctxeq) = Inl ((decom (SD x) (SD x₁) seq) , (cong ctxeq (refl (snd (findSize Γ₂)))))
  transHelper {Γ₁ , Γ₂} (MD1 dec1) (MD1 dec2) | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq) = Inr ((Δ₁ , Γ₂) , (Δ₂ , Γ₂) , MD1 dec3 , MD1 dec4 , cong eq (refl (snd (findSize Γ₂))))
  transHelper {Γ₁ , Γ₂} (MD1 dec1) (MD2 dec2) = Inr (_ , _ , MD2 dec2 , MD1 dec1 , refl (snd (findSize _)))
  transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD1 dec2) = Inr (_ , _ , MD1 dec2 , MD2 dec1 , refl (snd (findSize _)))
  transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD2 dec2) with transHelper dec1 dec2
  transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD2 dec2) | Inl (emp () x₁ , ctxeq)
  transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD2 dec2) | Inl (decom (SD x) (SD x₁) seq , ctxeq) = Inl ((decom (SD x) (SD x₁) seq) , (cong (refl (snd (findSize Γ₁))) ctxeq))
  transHelper {Γ₁ , Γ₂} (MD2 dec1) (MD2 dec2) | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq) = Inr ((Γ₁ , Δ₁) , (Γ₁ , Δ₂) , MD2 dec3 , MD2 dec4 , cong (refl (snd (findSize Γ₁))) eq)


  transNewHelper : ∀{Γ A B Γ₁ Γ₂} → Γ decTo sCtx A and Γ₁ → Γ₁ decTo sCtx B and Γ₂ → Σ[ Γ₃ ∈ Ctx ] (Γ decTo sCtx B and Γ₃ × Γ₃ decTo sCtx A and Γ₂)
  transNewHelper (SD ()) (SD x₁)
  transNewHelper (SD (mulE () x₁)) SD1
  transNewHelper (SD (mulE x ())) SD2
  transNewHelper (SD (mulE x x₁)) (MD1 dec2) = abort (lemmaEmptyDecom x dec2)
  transNewHelper (SD (mulE x x₁)) (MD2 dec2) = abort (lemmaEmptyDecom x₁ dec2)
  transNewHelper SD1 (SD x) = _ , SD2 , SD x
  transNewHelper SD1 SD1 = _ , MD2 SD1 , SD1
  transNewHelper SD1 SD2 = _ , MD2 SD2 , SD1
  transNewHelper SD2 (SD x) = _ , SD1 , SD x
  transNewHelper SD2 SD1 = _ , MD1 SD1 , SD2
  transNewHelper SD2 SD2 = _ , MD1 SD2 , SD2
  transNewHelper SD1 (MD1 dec2) = _ , MD2 (MD1 dec2) , SD1
  transNewHelper SD1 (MD2 dec2) = (_ , _) , MD2 (MD2 dec2) , SD1
  transNewHelper SD2 (MD1 dec2) = ((_ , _) , _) , MD1 (MD1 dec2) , SD2
  transNewHelper SD2 (MD2 dec2) = ((_ , _) , _) , MD1 (MD2 dec2) , SD2
  transNewHelper (MD1 (SD ())) SD1
  transNewHelper (MD1 SD1) SD1 = (_ , _) , MD1 SD2 , SD1
  transNewHelper (MD1 SD2) SD1 = (_ , _) , MD1 SD1 , SD1
  transNewHelper (MD1 dec1) SD2 = _ , SD2 , dec1
  transNewHelper (MD2 dec1) SD1 = _ , SD1 , dec1
  transNewHelper (MD2 (SD ())) SD2
  transNewHelper (MD2 SD1) SD2 = (_ , _) , MD2 SD2 , SD2
  transNewHelper (MD2 SD2) SD2 = (_ , _) , MD2 SD1 , SD2
  transNewHelper (MD1 dec1) (MD1 dec2) with transNewHelper dec1 dec2
  transNewHelper (MD1 dec1) (MD1 dec2) | Γ₃ , dec3 , dec4 = (Γ₃ , _) , MD1 dec3 , MD1 dec4
  transNewHelper {Γ = (Γ₁ , Γ₂)} (MD1 dec1) (MD2 {Γ₂' = Γ₂'} dec2) = (Γ₁ , Γ₂') , MD2 dec2 , MD1 dec1
  transNewHelper {Γ = (Γ₁ , Γ₂)} (MD2 dec1) (MD1 {Γ₁' = Γ₁'} dec2) = (Γ₁' , Γ₂) , MD1 dec2 , MD2 dec1
  transNewHelper (MD2 dec1) (MD2 dec2) with transNewHelper dec1 dec2
  transNewHelper (MD2 dec1) (MD2 dec2) | Γ₃ , dec3 , dec4 = (_ , Γ₃) , MD2 dec3 , MD2 dec4

  mutual
    decdSize : ∀{Γ Δ A n} → Γ decTo sCtx A and Δ → Γ size (S n) → Δ size n
    decdSize (SD x) s1 = s0 x
    decdSize dec (sm x size) with transHelper dec x
    decdSize dec (sm x size) | Inl (emp () x₂ , eq2)
    decdSize dec (sm x size) | Inl (decom (SD x₁) (SD x₂) eq1 , eq2) = equivSameSize eq2 size
    decdSize {Γ} {Δ₁} {A} {Z} dec (sm x (s0 x₁)) | Inr (Δ₂ , Δ₃ , dec3 , dec4 , eq) = abort (lemmaEmptyDecom x₁ dec4)
    decdSize {Γ} {Δ} {A} {S n} dec (sm x size) | Inr (Δ₂ , Δ₃ , dec3 , dec4 , eq) with decdSize dec4 size
    decdSize {Γ} {Δ₁} {A} {S Z} dec (sm x₁ size) | Inr (Δ₂ , Δ₃ , dec3 , dec4 , eq) | s0 x = sm dec3 (s0 (lemma x (sym eq)))
    decdSize {Γ} {Δ₁} {A} {S (S n)} dec (sm x size) | Inr (Δ₂ , Δ₃ , dec3 , dec4 , eq) | size2 = sm dec3 (equivSameSize eq size2)

    equivSameSize : ∀{Γ Δ n} → Γ ≡ Δ → Δ size n → Γ size n
    equivSameSize (emp x x₁) (s0 x₂) = s0 x
    equivSameSize (emp x ()) s1
    equivSameSize (emp x x₁) (sm x₂ size) = abort (lemmaEmptyDecom x₁ x₂)
    equivSameSize (decom x x₁ eqpf) (s0 x₂) = abort (lemmaEmptyDecom x₂ x₁)
    equivSameSize (decom x (SD x₁) eqpf) s1 = sm x (equivSameSize eqpf (s0 x₁))
    equivSameSize (decom x x₁ eqpf) (sm x₂ size) with transHelper x₁ x₂
    equivSameSize (decom x₄ x₁ eqpf) (sm x₂ size) | Inl (emp () x₃ , eq2)
    equivSameSize (decom x₄ x₁ eqpf) (sm x₂ size) | Inl (decom (SD x) (SD x₃) eq1 , eq2) with (decdSize x₁ (sm x₂ size))
    ... | size2 with equivSameSize eqpf size2
    ... | size3 = sm x₄ size3
    equivSameSize (decom x₃ x₁ eqpf) (sm {_} {Δ} {A₁} {Z} x₂ (s0 x)) | Inr (Δ₂ , Δ₃ , dec3 , dec4 , eq2) = abort (lemmaEmptyDecom x dec4)
    equivSameSize (decom x₃ x₁ eqpf) (sm {_} {Δ₁} {A₁} {S n} x₂ size) | Inr (Δ₂ , Δ₃ , dec3 , dec4 , eq2) with decdSize dec4 size | decdSize x₁ (sm x₂ size)
    ... | size2 | size3 = sm x₃ (equivSameSize eqpf size3)

    decProp : ∀{Γ Γ' A Δ n} → Γ decTo sCtx A and Δ
                        → Γ ≡ Γ'
                        → Γ size n
                        → Σ[ Δ' ∈ Ctx ] (Γ' decTo sCtx A and Δ' × Δ ≡ Δ')
    decProp dec (emp x x₁) size = abort (lemmaEmptyDecom x dec)
    decProp decpf (decom x x₁ eqpf) size with transHelper decpf x
    decProp decpf (decom x x₃ eqpf) size | Inl (emp () x₂ , eq2)
    decProp {Γ} {Γ'''} {A} {Δ} {Z} decpf (decom x x₃ eqpf) (s0 x₄) | Inl (decom (SD x₁) (SD x₂) eq1 , eq2) = abort (lemmaEmptyDecom x₄ x)
    decProp {Γ} {Γ'''} {A} {Δ} {S n} decpf (decom x x₃ eqpf) size | Inl (decom (SD x₁) (SD x₂) eq1 , eq2) with (decdSize decpf size)
    ... | size2 with equivSameSize (sym eq2) size2
    ... | size3 = _ , (x₃ , trans eq2 eqpf size2 size3 (equivSameSize (sym eqpf) size3))
    decProp {Γ} {Γ''} {A} {Δ} {Z} decpf (decom x x₂ eqpf) (s0 x₁) | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq2) = abort (lemmaEmptyDecom x₁ x)
    decProp {Γ} {Γ''} {A} {Δ} {S n} decpf (decom x x₂ eqpf) size | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq2) with (decdSize x size)
    ... | size2 with decProp dec4 eqpf size2
    ... | Δ₃ , dec5 , eq3 with transNewHelper x₂ dec5
    decProp {Γ₁} {Γ'} {A} {Δ} {S Z} decpf (decom x₁ x₂ eqpf) size | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq2) | s0 x | Δ₃ , dec5 , eq3 | Δ₄ , dec6 , dec7 = abort (lemmaEmptyDecom x dec4)
    decProp {Γ} {Γ'} {A} {Δ} {S (S n)} decpf (decom x x₂ eqpf) size | Inr (Δ₁ , Δ₂ , dec3 , dec4 , eq2) | size2 | Δ₃ , dec5 , eq3 | Δ₄ , dec6 , dec7 = Δ₄ , (dec6 , (decom dec3 dec7 (trans eq2 eq3 (decdSize dec3 (decdSize decpf size)) (decdSize dec4 size2) (decdSize dec5 (equivSameSize (sym eqpf) size2)))))

    trans : ∀{Γ₁ Γ₂ Γ₃ n} → Γ₁ ≡ Γ₂ → Γ₂ ≡ Γ₃ → Γ₁ size n → Γ₂ size n → Γ₃ size n → Γ₁ ≡ Γ₃
    trans (emp x x₁) (emp x₂ x₃) (s0 x₄) size2 size3 = emp x₄ x₃
    trans (emp x x₁) (decom x₂ x₃ eq2) (s0 x₄) size2 size3 = abort (lemmaEmptyDecom x₁ x₂)
    trans (decom x x₁ eq1) eq2 (s0 x₂) size2 size3 = abort (lemmaEmptyDecom x₂ x)
    trans (emp () x₁) eq2 s1 size2 size3
    trans (decom (SD x) x₁ eq1) (emp x₂ x₃) s1 size2 size3 = abort (lemmaEmptyDecom x₂ x₁)
    trans (decom (SD x) x₁ eq1) (decom x₂ x₃ eq2) s1 size2 size3 with transHelper x₁ x₂ | decdSize x₁ size2 | decdSize x₂ size2 | decdSize x₃ size3
    trans (decom (SD x) x₁ eq1) (decom x₂ x₃ eq2) s1 size2 size3 | Inl (emp () x₅ , snd) | size5 | size6 | size7
    trans (decom (SD x₅) x₁ eq1) (decom x₂ x₃ eq2) s1 size2 size3 | Inl (decom (SD x) (SD x₄) fst , snd) | size5 | size6 | size7 = decom (SD x₅) x₃ (trans eq1 (trans snd eq2 size5 size6 size7) (s0 x₅) size5 size7)
    trans (decom (SD x) x₁ eq1) (decom x₂ x₃ eq2) s1 size2 size3 | Inr (Δ₁ , Δ₂ , dec1 , dec2 , eq) | size5 | size6 | size7 = abort (lemmaEmptyDecom (lemma x eq1) dec1)
    trans (emp x x₁) (emp x₂ x₃) (sm x₄ size) size2 size3 = emp x x₃
    trans (emp x x₁) (decom x₂ x₃ eq2) (sm x₄ size) size2 size3 = abort (lemmaEmptyDecom x₁ x₂)
    trans (decom x x₁ eq1) (emp x₂ x₃) (sm x₄ size) size2 size3 = abort (lemmaEmptyDecom x₂ x₁)
    trans (decom x x₁ eq1) (decom x₂ x₃ eq2) (sm x₄ size) size2 size3 with transHelper x₁ x₂ | decdSize x (sm x₄ size) | decdSize x₁ size2 | decdSize x₃ size3 | decdSize x₂ size2
    trans (decom x₄ x₁ eq1) (decom x₂ x₅ eq2) (sm x₆ size) size2 size3 | Inl (emp () x₃ , eq4) | _ | _ | _ | _
    trans (decom x₄ x₁ eq1) (decom x₂ x₅ eq2) (sm x₆ size) size2 size3 | Inl (decom (SD x) (SD x₃) eq3 , eq4) | size4 | size5 | size6 | size7 = decom x₄ x₅ (trans eq1 (trans eq4 eq2 size5 size7 size6) size4 size5 size6)
    trans (decom x₃ x₁ eq1) (decom x₂ x₄ eq2) (sm x₅ size) size2 size3 | Inr (Δ₁ , Δ₂ , dec1 , dec2 , eq) | size4 | size5 | size6 | size7 with decProp dec1 (sym eq1) size5 | decProp dec2 eq2 size7
    ... | Δ₃ , dec3 , eq3 | Δ₄ , dec4 , eq4 with transNewHelper x₄ dec4
    trans (decom x₃ x₁ eq1) (decom x₂ x₄ eq2) (sm {_} {Δ} {A₂} {Z} x₅ size) size2 size3 | Inr (Δ₁ , Δ₂ , dec1 , dec2 , eq) | s0 x | size5 | size6 | size7 | Δ₃ , dec3 , eq3 | Δ₄ , dec4 , eq4 | Γ₄ , dec5 , dec6 = abort (lemmaEmptyDecom x dec3)
    trans (decom x₃ x₁ eq1) (decom x₂ x₄ eq2) (sm {_} {Δ} {A₂} {S n} x₅ size) size2 size3 | Inr (Δ₁ , Δ₂ , dec1 , dec2 , eq) | size4 | size5 | size6 | size7 | Δ₃ , dec3 , eq3 | Δ₄ , dec4 , eq4 | Γ₄ , dec5 , dec6 = decom x₃ dec5 (decom dec3 dec6 (trans (sym eq3) (trans eq eq4 (decdSize dec1 size5) (decdSize dec2 size7) (decdSize dec4 size6)) (decdSize dec3 size4) (decdSize dec1 size5) (decdSize dec4 size6)))

  mutual
    size+1 : ∀{Γ A n} → Γ size n → (sCtx A , Γ) size S n × (Γ , sCtx A) size S n
    size+1 (s0 x) = sm SD1 (s0 x) , sm SD2 (s0 x)
    size+1 s1 = sm SD2 s1 , sm SD1 s1
    size+1 (sm x size) = sm SD1 (sm x size) , sm (MD1 x) (snd (size+1 size))
  
    sizeHelper : ∀ {Γ₁ Γ₂ n} → (Γ₁ , Γ₂) size n → (Γ₁ , (Γ₂ , ·)) size n
    sizeHelper (s0 (mulE x x₁)) = s0 (mulE x (mulE x₁ sinE))
    sizeHelper (sm SD1 size) = equivSameSize (decom SD1 SD1 (unitR size)) (fst (size+1 size))
    sizeHelper (sm SD2 size) = equivSameSize (cong (refl size) (decom SD1 (SD sinE) (emp sinE sinE))) (snd (size+1 size))
    sizeHelper (sm (MD1 x) size) = sm (MD1 x) (sizeHelper size)
    sizeHelper (sm (MD2 x) size) = sm (MD2 (MD1 x)) (sizeHelper size)
    
    assoc : ∀{Γ₁ Γ₂ Γ₃ n} → (Γ₁ , (Γ₂ , Γ₃)) size n → (Γ₁ , (Γ₂ , Γ₃)) ≡ ((Γ₁ , Γ₂) , Γ₃)
    assoc (s0 (mulE x (mulE x₁ x₂))) = emp (mulE x (mulE x₁ x₂)) (mulE (mulE x x₁) x₂)
    assoc (sm (MD1 x) size) = decom (MD1 x) (MD1 (MD1 x)) (assoc size)
    assoc (sm (MD2 (MD1 x)) size) = decom (MD2 (MD1 x)) (MD1 (MD2 x)) (assoc size)
    assoc (sm (MD2 (MD2 x)) size) = decom (MD2 (MD2 x)) (MD2 x) (assoc size)
    assoc (sm {n = Z} (MD2 SD1) (s0 (mulE x x₁))) = decom (MD2 (MD1 (SD x₁))) (MD1 (MD2 (SD x₁))) (emp (mulE x (mulE x₁ x₁)) (mulE (mulE x x₁) x₁))
    assoc (sm {n = S n} (MD2 SD1) size) = decom (MD2 (MD1 (SD sinE))) (MD1 (MD2 (SD sinE))) (cong (sym (unitR (snd (findSize _)))) (unitL (snd (findSize _))))
    assoc (sm {n = Z} (MD2 SD2) (s0 (mulE x x₁))) = decom (MD2 (MD2 (SD x₁))) (MD2 (SD x₁)) (emp (mulE x (mulE x₁ x₁)) (mulE (mulE x x₁) x₁))
    assoc (sm {n = S n} (MD2 SD2) size) = decom (MD2 (MD2 (SD sinE))) (MD2 (SD sinE)) (assoc (sizeHelper size))
    assoc (sm SD1 size) = decom (MD1 (SD sinE)) (MD1 SD1) (unitL size)

    unitL : ∀ {Γ n} → Γ size n → (· , Γ) ≡ Γ
    unitL (s0 x) = emp (mulE sinE x) x
    unitL s1 = decom SD2 (SD sinE) (emp sinE sinE)
    unitL (sm x size)= decom (MD2 x) x (unitL size)

    unitR : ∀ {Γ n} → Γ size n → (Γ , ·) ≡ Γ
    unitR (s0 x) = emp (mulE x sinE) x
    unitR s1 = decom (MD1 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE)
    unitR (sm {n = Z} x (s0 x₁)) = decom (MD1 x) x (unitR (s0 x₁))
    unitR (sm {n = S n} x size) with unitR size
    ... | res = decom (MD1 x) x res


    emptyEquiv : ∀ {Γ₁ Γ₂} → · ≡ (Γ₁ , Γ₂) → · ≡ Γ₁ × · ≡ Γ₂
    emptyEquiv (emp x (mulE x₁ x₂)) = emp x x₁ , emp x x₂
    emptyEquiv (decom () x₁ pf)

    emptySubLemma : ∀ {Γ Δ} → Γ ⊢s Δ → Δ empty → Γ empty
    emptySubLemma emptySub empt = empt
    emptySubLemma var ()
    emptySubLemma (comma sub sub₁) (mulE empt empt₁) = mulE (emptySubLemma sub empt) (emptySubLemma sub₁ empt₁)
    emptySubLemma (equiv x sub x₁) empt = lemma (emptySubLemma sub (lemma empt (sym x₁))) (sym x)

    emptyLemma : ∀ {Γ} → Γ empty → · ≡ Γ
    emptyLemma sinE = emp sinE sinE
    emptyLemma (mulE pf pf₁) = emp sinE (mulE pf pf₁)

    emptyLemmaV2 : ∀ {Γ} → · ≡ Γ → Γ empty
    emptyLemmaV2 (emp x x₁) = x₁
    emptyLemmaV2 (decom () x₁ eq)

    lemmaSingleEmpty : ∀ {Γ A Δ} → Γ decTo sCtx A and Δ → · ≡ Δ → Γ ≡ sCtx A
    lemmaSingleEmpty (SD x) empteq = decom (SD x) (SD x) (emp x x)
    lemmaSingleEmpty (MD1 decpf) empteq = decom (MD1 decpf) (SD sinE) (sym empteq)
    lemmaSingleEmpty (MD2 decpf) empteq = decom (MD2 decpf) (SD sinE) (sym empteq)
    lemmaSingleEmpty SD1 empteq = decom SD1 (SD (emptyLemmaV2 empteq)) (refl (snd (findSize _)))
    lemmaSingleEmpty SD2 empteq = decom SD2 (SD (emptyLemmaV2 empteq)) (refl (snd (findSize _)))

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
  
    nat-suc : ∀ {n m} → n == m → S n == S m
    nat-suc Refl = Refl

    nat-dec : ∀ {n m} → S n == S m → n == m
    nat-dec Refl = Refl

    transNat : (n m p : Nat) → n == m → m == p → n == p
    transNat Z Z Z x x₁ = Refl
    transNat Z Z (S p) x ()
    transNat Z (S m) Z () x₁
    transNat Z (S m) (S p) () x₁
    transNat (S n) Z Z () x₁
    transNat (S n) Z (S p) () x₁
    transNat (S n) (S m) Z x ()
    transNat (S n) (S .n) (S .n) Refl Refl = Refl

    plus-rh-Z : (n : Nat) → n == (n + Z)
    plus-rh-Z Z = Refl
    plus-rh-Z (S n) = nat-suc (plus-rh-Z n)
  
    plus-rh-S : (n m : Nat) → S (n + m) == n + (S m)
    plus-rh-S Z m = Refl
    plus-rh-S (S n) m = nat-suc (plus-rh-S n m)

    plus-comm : (n m : Nat) → n + m == m + n
    plus-comm Z m = plus-rh-Z m
    plus-comm (S n) m with plus-comm n m | plus-rh-S (S m) n
    ... | eq1 | eq2 = transNat ((S n) + m) (S (m + n)) (m + (S n)) (nat-suc eq1) (nat-dec eq2)

    commaSizeLemma : {Γ₁ Γ₂ : Ctx} {n : Nat} → (Γ₁ , Γ₂) size n → Σ[ k ∈ Nat ] Σ[ p ∈ Nat ] (Γ₁ size k × Γ₂ size p × (n == (k + p)))
    commaSizeLemma (s0 (mulE x x₁)) = 0 , 0 , s0 x , s0 x₁ , Refl
    commaSizeLemma (sm (MD1 x) size) with commaSizeLemma size
    commaSizeLemma (sm (MD1 x) size) | k , p , size1 , size2 , Refl = S k , p , sm x size1 , size2 , Refl
    commaSizeLemma (sm (MD2 x) size)  with commaSizeLemma size
    commaSizeLemma (sm (MD2 x) size) | k , p , size1 , size2 , Refl = k , S p , size1 , sm x size2 , plus-rh-S k p 
    commaSizeLemma (sm SD1 size) = 1 , _ , s1 , size , Refl
    commaSizeLemma (sm SD2 size) = _ , 1 , size , s1 , plus-comm 1 _

    subSameSize : ∀ {Γ Δ n} → Γ ⊢s Δ → Γ size n → Δ size n
    subSameSize emptySub size = size
    subSameSize var size = size
    subSameSize (comma sub sub₁) size with commaSizeLemma size
    subSameSize (comma sub sub₁) size | k , p , size1 , size2 , Refl = addSizesLemma (subSameSize sub size1) (subSameSize sub₁ size2)
    subSameSize (equiv x sub x₁) size1 = equivSameSize (sym x₁) (subSameSize sub (equivSameSize (sym x) size1))

    singleCtxSize : ∀{Γ A} → Γ ≡ sCtx A → Γ size 1
    singleCtxSize (emp x ())
    singleCtxSize (decom x (SD x₁) eq) = sm x (s0 (lemma x₁ (sym eq)))
  
    wrongSize : ∀{Γ n} → Γ ≡ · → Γ size S n → Void
    wrongSize (emp () x₁) s1
    wrongSize (decom x () eqpf) s1
    wrongSize eqpf (sm x size) = abort (lemmaEmptyDecom (emptyLemmaV2 (sym eqpf)) x)

  -- switchLemma : ∀ {Γ₁ Γ₂ Δ} → (Γ₁ , Γ₂) ≡ Δ → (Γ₂ , Γ₁) ≡ Δ
  -- switchLemma (emp (mulE x x₁) x₂) = emp (mulE x₁ x) x₂
  -- switchLemma (decom (MD1 x) x₁ eqpf) = decom (MD2 x) x₁ (switchLemma eqpf)
  -- switchLemma (decom (MD2 x) x₁ eqpf) = decom (MD1 x) x₁ (switchLemma eqpf)

  -- singleDecLemma : ∀{Γ Δ A} → Γ decTo sCtx A and Δ → Δ empty → Γ ≡ sCtx A
  -- singleDecLemma (SD x) empt = decom (SD empt) (SD empt) (emp empt empt)
  -- singleDecLemma (MD1 decpf) (mulE empt empt₁) = addEmptyCtx (singleDecLemma decpf empt) empt₁
  -- singleDecLemma (MD2 decpf) (mulE empt empt₁) = switchLemma (addEmptyCtx (singleDecLemma decpf empt₁) empt)
