{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import HLevels
open import Equivalence hiding (isPropIsEquiv ; equivEq)
open import FunExtPostulate

private variable
  ℓ ℓ' ℓ'' : Level

isHAE : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isHAE {A = A} {B} f = Σ (B → A) (λ g → Σ (g ∘ f ~ id) λ η → Σ (f ∘ g ~ id) λ ϵ → (x : A) → cong f (η x) ≡ ϵ (f x))

~natural : {A : Type ℓ} {B : Type ℓ'} {f g : A → B} (α : f ~ g) {x y : A} (p : x ≡ y) → α x ∙ cong g p ≡ cong f p ∙ α y
~natural {f = f} {g = g} α {x = x} {y = y} refl = α x ∙ cong g refl ≡⟨ cong (λ { y → _ ∙ y }) refl ⟩
 α x ∙ refl ≡⟨ sym (rUnit _) ⟩
 α x ≡⟨ lUnit _ ⟩
 refl ∙ α x  ≡⟨ cong (λ { y → y ∙ _ }) refl ⟩
 cong f refl ∙ α x ∎

~natural' : {A : Type ℓ} {f : A → A} (α : f ~ id) (x : A) → α (f x) ≡ cong f (α x)
~natural' {f = f} α x = α (f x) ≡⟨ rUnit _ ⟩
 α (f x) ∙ refl ≡⟨ cong (λ { p → _ ∙ p }) (sym (rCancel _)) ⟩
 α (f x) ∙ α x ∙ sym (α x) ≡⟨ assoc _ _ _ ⟩
 (α (f x) ∙ α x) ∙ sym (α x) ≡⟨ cong (λ { p → p ∙ _ }) commute ⟩
 (cong f (α x) ∙ α x) ∙ sym (α x) ≡⟨ sym (assoc _ _ _) ⟩
 cong f (α x) ∙ α x ∙ sym (α x) ≡⟨ cong (λ { p → _ ∙ p }) (rCancel _) ⟩
 cong f (α x) ∙ refl ≡⟨ sym (rUnit _) ⟩
 cong f (α x) ∎
 where
 commute : α (f x) ∙ α x ≡ cong f (α x) ∙ α x
 commute = α (f x) ∙ α x ≡⟨ cong (λ { p → _ ∙ p }) (sym (congId _)) ⟩
  α (f x) ∙ cong id (α x) ≡⟨ ~natural _ _ ⟩
  cong f (α x) ∙ α x ∎

hasQInv→isHAE : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → hasQInv f → isHAE f
hasQInv→isHAE {A = A} f (g , η , ε) = g , η , ε' , τ
 where
 ε' : f ∘ g ~ id
 ε' x = sym (ε (f (g x))) ∙ cong f (η (g x)) ∙ ε x

 τ : (a : A) → cong f (η a) ≡ ε' (f a)
 τ a = sym (sym (ε (f (g (f a)))) ∙ cong f (η (g (f a))) ∙ ε (f a) ≡⟨ cong (λ { x → _ ∙ x }) compute ⟩
  sym (ε (f (g (f a)))) ∙ ε (f (g (f a))) ∙ cong f (η a) ≡⟨ assoc _ _ _ ⟩
  (sym (ε (f (g (f a)))) ∙ ε (f (g (f a)))) ∙ cong f (η a) ≡⟨ cong (λ { x → x ∙ _ }) (lCancel _) ⟩
  refl ∙ cong f (η a) ≡⟨ sym (lUnit _) ⟩
  cong f (η a) ∎)
  where
  commηgf : η (g (f a)) ≡ cong (g ∘ f) (η a)
  commηgf = ~natural' η a

  compute : cong f (η (g (f a))) ∙ ε (f a) ≡ ε (f (g (f a))) ∙ cong f (η a)
  compute = cong f (η (g (f a))) ∙ ε (f a) ≡⟨ cong (λ { p → cong f p ∙ _ }) commηgf ⟩
   cong f (cong (g ∘ f) (η a)) ∙ ε (f a) ≡⟨ cong (λ { x → cong f x ∙ _ }) (cong∘ f g (η a)) ⟩
   cong f (cong g (cong f (η a))) ∙ ε (f a) ≡⟨ cong (λ { x → _ ∙ x }) commεffη ⟩
   cong f (cong g (cong f (η a))) ∙ cong f (η a) ≡⟨ {! !} ⟩
   ε (f (g (f a))) ∙ cong f (η a) ∎
    where
    commεffη : ε (f a) ≡ cong f (η a)
    commεffη = ε (f a) ≡⟨ rUnit _ ⟩
     ε (f a) ∙ refl ≡⟨ cong (λ { x → _ ∙ x }) (sym (congConst _)) ⟩
     ε (f a) ∙ cong (λ _ → f a) (η a) ≡⟨ {! ~natural _ _ !} ⟩
     cong f (η a) ∙ refl ≡⟨ sym (rUnit _) ⟩
     cong f (η a) ∎
