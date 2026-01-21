{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import HLevels

private variable
  ℓ ℓ' ℓ'' : Level

_∼_ : {A : Type ℓ} {B : A → Type ℓ'} (f g : (x : A) → B x) → Type (ℓ-max ℓ ℓ')
f ∼ g = (x : _) → f x ≡ g x
infixr 4 _∼_

∼refl : {A : Type ℓ} {B : A → Type ℓ'} {f : (x : A) → B x} → f ∼ f
∼refl x = refl

∼sym : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} → f ∼ g → g ∼ f
∼sym p x = sym (p x)

∼trans : {A : Type ℓ} {B : A → Type ℓ'} {f g h : (x : A) → B x} → f ∼ g → g ∼ h → f ∼ h
∼trans p q x = trans (p x) (q x)

∼LWhisk : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : A → B) {g g' : B → C} → g ∼ g' → (g ∘ f) ∼ (g' ∘ f)
∼LWhisk f p x = p (f x)

∼RWhisk : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f f' : A → B} → f ∼ f' → (g : B → C) → (g ∘ f) ∼ (g ∘ f')
∼RWhisk p g x = cong g (p x)

module _ {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
  hasLInv : Type (ℓ-max ℓ ℓ')
  hasLInv = Σ (B → A) (λ g → g ∘ f ∼ id)

  hasRInv : Type (ℓ-max ℓ ℓ')
  hasRInv = Σ (B → A) (λ g → f ∘ g ∼ id)

  hasQInv : Type (ℓ-max ℓ ℓ')
  hasQInv = Σ (B → A) (λ g → (g ∘ f ∼ id) × (f ∘ g ∼ id))

  isEquiv : Type (ℓ-max ℓ ℓ')
  isEquiv = hasLInv × hasRInv

  hasQInv→isEquiv : hasQInv → isEquiv
  hasQInv→isEquiv = {! !}
