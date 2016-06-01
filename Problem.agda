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

  emptyLemmaV2 : ∀ {Γ} → · ≡ Γ → Γ empty
  emptyLemmaV2 (emp x x₁) = x₁
  emptyLemmaV2 (decom () x₁ eq)

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

  1+Lemma : ∀ {k p} → S (k + p) == (k + S p)
  1+Lemma {Z} = λ {p} → Refl
  1+Lemma {S k}{p} with 1+Lemma {k}{p}
  ... | eq = nat-suc eq

  commaSizeLemma : {Γ₁ Γ₂ : Ctx} {n : Nat} → (Γ₁ , Γ₂) size n → Σ[ k ∈ Nat ] Σ[ p ∈ Nat ] (Γ₁ size k × Γ₂ size p × (n == (k + p)))
  commaSizeLemma (s0 (mulE x x₁)) = 0 , 0 , s0 x , s0 x₁ , Refl
  commaSizeLemma (sm (MD1 x) size) with commaSizeLemma size
  commaSizeLemma (sm (MD1 x) size) | k , p , size1 , size2 , Refl = S k , p , sm x size1 , size2 , Refl
  commaSizeLemma (sm (MD2 x) size)  with commaSizeLemma size
  commaSizeLemma (sm (MD2 x) size) | k , p , size1 , size2 , Refl = k , S p , size1 , sm x size2 , 1+Lemma {k} {p}

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

  transSub : ∀ {Γ₁ Γ₂ Γ₃ n} → Γ₁ ⊢s Γ₂ → Γ₂ ⊢s Γ₃ → Γ₁ size n → Γ₂ size n → Γ₃ size n → Γ₁ ⊢s Γ₃
  transSub emptySub emptySub _ _ _ = emptySub
  transSub emptySub (equiv x sub2 x₁) _ _ _ = equiv x sub2 x₁
  transSub var var _ _ _ = var
  transSub var (equiv x sub2 x₁) _ _ _ = equiv x sub2 x₁
  transSub (comma {Δ₁ = Δ₁} {Δ₂ = Δ₂} sub1 sub2) (comma sub3 sub4) size1 size2 size3 with findSize Δ₁ | findSize Δ₂
  ... | n , size4 | m , size5 = comma (transSub sub1 sub3 (subSameSize (symSub sub1) size4) size4 (subSameSize sub3 size4)) (transSub sub2 sub4 (subSameSize (symSub sub2) size5) size5 (subSameSize sub4 size5))
  transSub (comma sub1 sub2) (equiv x sub3 x₁) size1 size2 size3 = {!!} -- transSub (comma sub1 sub2) (transSub (transSub (equivSubs x) sub3 ? ? ?) (equivSubs x₁) ? ? ?) ? ? ?
  transSub {n = Z} (equiv x emptySub x₁) sub2 (s0 x₂) (s0 x₃) (s0 x₄) = equiv x emptySub (emp sinE x₄)
  transSub {n = S n} (equiv x emptySub x₁) sub2 x₂ x₃ x₄ = abort (wrongSize x x₂)
  transSub (equiv x var x₁) sub2 x₂ x₃ x₄ = equiv (trans x x₁ (singleCtxSize x) s1 (singleCtxSize (sym x₁))) sub2 (refl x₄)
  transSub (equiv x (comma sub1 sub2) x₁) sub3 size1 size2 size3 = {!!} -- transSub {!!} (equiv x₁ sub3 (refl x₄)) x₂ (equivSameSize x₁ x₃) x₄
  transSub (equiv x (equiv x₁ sub1 x₂) x₃) sub2 x₄ x₅ x₆ with equivSameSize x₃ x₅ | equivSameSize (sym x) x₄
  ... | size1 | size2 = equiv (trans x x₁ x₄ size2 (equivSameSize (sym x₁) size2)) (transSub sub1 (equiv (trans x₂ x₃ (equivSameSize x₂ size1) size1 x₅) sub2 (refl x₆)) ((equivSameSize (sym x₁) size2)) ((equivSameSize x₂ size1)) x₆) (refl x₆)

  congSub : ∀ {Γ₁ Γ₂ Δ₁ Δ₂} → Γ₁ ⊢s Δ₁ → Γ₂ ⊢s Δ₂ → (Γ₁ , Γ₂) ⊢s (Δ₁ , Δ₂)
  congSub sub1 sub2 = comma sub1 sub2

  unitLsub : ∀ {Γ} → (· , Γ) ⊢s Γ
  unitLsub = equiv unitL reflSub (refl (snd (findSize _)))

  unitRsub : ∀ {Γ} → (Γ , ·) ⊢s Γ
  unitRsub = equiv unitR reflSub (refl (snd (findSize _)))



  constructLemma : ∀{A Δ} → Σ[ Γ ∈ Ctx ] (Γ decTo sCtx A and Δ)
  constructLemma {Δ = ·} = _ , (SD sinE)
  constructLemma {A = A}{Δ = sCtx x} = (sCtx A , sCtx x) , {!MD1 (SD {A} sinE)!}
  constructLemma {A = A}{Δ = Δ₁ , Δ₂} with constructLemma {A} {Δ₁}
  ... | Γ₁ , dec = (Γ₁ , Δ₂) , MD1 dec

  decProp2 : ∀{Γ A Δ Δ' n} → Γ decTo sCtx A and Δ
                           → Δ ≡ Δ'
                           → Γ size n
                           → Σ[ Γ' ∈ Ctx ] (Γ' decTo sCtx A and Δ' × Γ ≡ Γ')
  decProp2 {A = A} {Δ' = Δ'} dec eq size with constructLemma {A} {Δ'}
  ... | Γ' , dec2 = Γ' , dec2 , decom dec dec2 eq

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
  subLemma dec (equiv x₁ sub x₂) with decProp2 dec (sym x₂) (snd (findSize _))
  ... | Γ' , dec2 , eq2 with subLemma dec2 sub
  ... | Δ , dec3 , sub2 with decProp2 dec3 (sym x₁) (snd (findSize _))
  ... | Γ'' , dec4 , eq3 = Γ'' , dec4 , transSub (equivSubs (sym eq3)) (transSub sub2 (equivSubs (sym eq2)) {!!} {!!} {!!}) {!!} {!!} {!!}

  subLemma2 : ∀ {Γ Δ Δ' A} → Γ ⊢s Δ → Δ decTo sCtx A and Δ' → Σ[ Γ' ∈ Ctx ] (Γ decTo sCtx A and Γ' × Γ' ⊢s Δ')
  subLemma2 emptySub ()
  subLemma2 var (SD x) = · , SD sinE , equiv (emp sinE sinE) emptySub (emp sinE x)
  subLemma2 (comma sub sub₁) (MD1 decpf) with subLemma2 sub decpf
  ... | Γ' , dec1 , sub2 = (Γ' , _) , MD1 dec1 , comma sub2 sub₁
  subLemma2 (comma sub sub₁) (MD2 decpf) with subLemma2 sub₁ decpf
  ... | Γ' , dec1 , sub2 = (_ , Γ') , MD2 dec1 , comma sub sub2
  subLemma2 (equiv x sub x₁) dec with decProp dec (sym x₁) (snd (findSize _))
  ... | Δ' , dec2 , eq2 with subLemma2 sub dec2
  ... | Γ' , dec3 , sub2 with decProp dec3 (sym x) (snd (findSize _)) | findSize Δ' | findSize Γ'
  ... | Δ'' , dec4 , eq3 | n , size1 | m , size2 = Δ'' , dec4 , transSub (equivSubs (sym eq3)) (transSub sub2 (equivSubs (sym eq2)) (subSameSize (symSub sub2) size1) size1 (equivSameSize eq2 size1)) (equivSameSize (sym eq3) size2) size2 (equivSameSize eq2 (subSameSize sub2 size2))

  

  dan : {n : Nat} → (Γ Γ' Γ₁' Γ₂' : Ctx) → Γ ⊢s Γ' → Γ' ≡ (Γ₁' , Γ₂') → Γ size n → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] ((Γ₁ , Γ₂) ≡ Γ × Γ₁ ⊢s Γ₁' × Γ₂ ⊢s Γ₂')
  dan .· .· Γ₁' Γ₂' emptySub (emp x (mulE x₁ x₂)) size = · , · , emp (mulE x x) x , equiv (emp x x) emptySub (emp x x₁) , equiv (emp x x) emptySub (emp x x₂)
  dan .· .· Γ₁' Γ₂' emptySub (decom () x₁ pf)
  dan ._ ._ Γ₁' Γ₂' var (emp () x₁)
  dan ._ ._ Γ₁' Γ₂' (var {A}) (decom (SD em) (MD1 x₁) eq) size = sCtx A , · , decom (MD1 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE) , equiv (refl s1) var (sym (lemmaSingleEmpty x₁ (fst (emptyEquiv (trans (emptyLemma em) eq (s0 sinE) (s0 em) (s0 (lemma em eq))))))) , equiv (emp sinE sinE) emptySub (snd (emptyEquiv (trans (emptyLemma em) eq (s0 sinE) (s0 em) (s0 (lemma em eq)))))
  dan ._ ._ Γ₁' Γ₂' (var {A}) (decom (SD em) (MD2 x₁) eq) size = · , sCtx A , decom (MD2 (SD sinE)) (SD sinE) (emp (mulE sinE sinE) sinE) , equiv (emp sinE sinE) emptySub (fst (emptyEquiv (trans (emptyLemma em) eq (s0 sinE) (s0 em) (s0 (lemma em eq))))) , equiv (refl s1) var (sym (lemmaSingleEmpty x₁ (snd (emptyEquiv (trans (emptyLemma em) eq (s0 sinE) (s0 em) (s0 (lemma em eq)))))))
  dan Γ Γ' Γ₁' Γ₂' (equiv {Γ' = Γ''}{Δ' = Δ'} x sub x₁) pf size with findSize Δ'
  ... | n , size1 with equivSameSize (sym x₁) size1
  ... | size2 with dan _ _ _ _ sub (trans x₁ pf size1 size2 (equivSameSize (sym pf) size2)) (equivSameSize (sym x) size)
  ... | Γ1 , Γ2 , split , sub1 , sub2 with findSize Γ''
  ... | m , size3 = Γ1 , Γ2 , trans split (sym x) (equivSameSize split size3) size3 (equivSameSize x size3) , sub1 , sub2
  dan ._ ._ Γ₁' Γ₂' (comma sub sub₁) (emp (mulE x x₁) (mulE x₂ x₃)) size = · , · , emp (mulE sinE sinE) (mulE (emptySubLemma sub x) (emptySubLemma sub₁ x₁)) , equiv (emp sinE sinE) emptySub (emp sinE x₂) , equiv (emp sinE sinE) emptySub (emp sinE x₃)
  dan {Z} _ _ Γ₁' Γ₂' (comma sub1 sub2) (decom (MD1 dec1) (MD1 dec2) pf) (s0 (mulE x x₁)) with subLemma2 sub1 dec1
  ... | (_ , dec , _) = abort (lemmaEmptyDecom x dec)
  dan {S n} .(Γ₁ , Γ₂) .(Δ₁ , Δ₂) Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (decom (MD1 {A}{Δ1} dec1) (MD1 {.A}{Γ1} dec2) pf) size with subLemma2 sub1 dec1
  ... | (Γ'' , dec3 , sub3) with dan _ _ _ _ (comma sub3 sub2) pf (decdSize (MD1 dec3) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma dec2 sub4
  ... | (Γ5 , dec4 , sub6) = Γ5 , Γ4 , decom (MD1 dec4) (MD1 dec3) eqpf , sub6 , sub5
  dan {Z} _ _ Γ₁ Γ₂' (comma sub1 sub2) (decom (MD1 dec1) (MD2 dec2) pf) (s0 (mulE x x₁)) with subLemma2 sub1 dec1
  ... | (_ , dec , _) = abort (lemmaEmptyDecom x dec)
  dan {S n} .(Γ₁ , Γ₂) .(Δ₁ , Δ₂) Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (decom (MD1 {A}{Δ1} dec1) (MD2 {.A}{Γ2} dec2) pf) size with subLemma2 sub1 dec1
  ... | (Γ'' , dec3 , sub3) with dan _ _ _ _ (comma sub3 sub2) pf (decdSize (MD1 dec3) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma dec2 sub5
  ... | (Γ5 , dec4 , sub6) = Γ3 , Γ5 , decom (MD2 dec4) (MD1 dec3) eqpf , sub4 , sub6
  dan {Z} _ _ Γ₁' Γ₂ (comma sub1 sub2) (decom (MD2 dec1) (MD1 dec2) pf) (s0 (mulE x x₁)) with subLemma2 sub2 dec1
  ... | (_ , dec , _) = abort (lemmaEmptyDecom x₁ dec)
  dan {S n} .(Γ₁ , Γ₂) .(Δ₁ , Δ₂) Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (decom (MD2 {A}{Δ2} dec1) (MD1 {.A}{Γ1} dec2) pf) size with subLemma2 sub2 dec1
  ... | (Γ'' , dec3 , sub3) with dan _ _ _ _ (comma sub1 sub3) pf (decdSize (MD2 dec3) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma dec2 sub4
  ... | (Γ5 , dec4 , sub6) = Γ5 , Γ4 , decom (MD1 dec4) (MD2 dec3) eqpf , sub6 , sub5
  dan {Z} _ _ Γ₁ Γ₂' (comma sub1 sub2) (decom (MD2 dec1) (MD2 dec2) pf) (s0 (mulE x x₁)) with subLemma2 sub2 dec1
  ... | (_ , dec , _) = abort (lemmaEmptyDecom x₁ dec)
  dan {S n} .(Γ₁ , Γ₂) .(Δ₁ , Δ₂) Γ₁' Γ₂' (comma {Γ₁}{Γ₂}{Δ₁}{Δ₂} sub1 sub2) (decom (MD2 {A}{Δ2} dec1) (MD2 {.A}{Γ2} dec2) pf) size with subLemma2 sub2 dec1
  ... | (Γ'' , dec3 , sub3) with dan _ _ _ _ (comma sub1 sub3) pf (decdSize (MD2 dec3) size)
  ... | (Γ3 , Γ4 , eqpf , sub4 , sub5) with subLemma dec2 sub5
  ... | (Γ5 , dec4 , sub6) = Γ3 , Γ5 , decom (MD2 dec4) (MD2 dec3) eqpf , sub4 , sub6
