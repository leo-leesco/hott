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
~natural α p = {! !}
