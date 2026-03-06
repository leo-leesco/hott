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
~natural {f = f} {g = g} α {x = x} {y = y} refl = α x ∙ cong g refl ≡⟨ cong (λ { y → α x ∙ y }) refl ⟩
 α x ∙ refl ≡⟨ sym (rUnit (α x)) ⟩
 α x ≡⟨ lUnit (α x) ⟩
 refl ∙ α x  ≡⟨ cong (λ { y → y ∙ α x }) refl ⟩
 cong f refl ∙ α x ∎

~natural' : {A : Type ℓ} {f : A → A} (α : f ~ id) (x : A) → α (f x) ≡ cong f (α x)
~natural' {f = f} α x = α (f x) ≡⟨ rUnit (α (f x)) ⟩
 α (f x) ∙ refl ≡⟨ cong _ refl ⟩
 α (f x) ∙ α x ∙ sym (α x) ≡⟨ assoc (α (f x)) (α x) (sym (α x)) ⟩
 (α (f x) ∙ α x) ∙ sym (α x) ≡⟨ cong (λ { p → p ∙ sym (α x) }) commute ⟩
 (cong f (α x) ∙ α x) ∙ sym (α x) ≡⟨ sym (assoc (cong f (α x)) (α x) (sym (α x))) ⟩
 cong f (α x) ∙ α x ∙ sym (α x) ≡⟨ cong _ refl ⟩
 cong f (α x) ∙ refl ≡⟨ sym (rUnit (cong f (α x))) ⟩
 cong f (α x) ∎
 where
 commute : α (f x) ∙ α x ≡ cong f (α x) ∙ α x
 commute = α (f x) ∙ α x ≡⟨ cong (λ { p → α (f x) ∙ p }) (sym (congId (α x))) ⟩
  α (f x) ∙ cong id (α x) ≡⟨ ~natural {g = id} α {x = f x} (α x) ⟩
  cong f (α x) ∙ α x ∎
