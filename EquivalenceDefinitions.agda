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
~natural' {f = f} α x = α (f x) ≡⟨ {! !} ⟩
 α (f x) ∙ f x ∙ sym (f x) ≡⟨ ? ⟩
 cong f (α x) ∎
