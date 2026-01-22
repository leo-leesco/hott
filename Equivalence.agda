{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import HLevels

private variable
  ℓ ℓ' ℓ'' : Level

_~_ : {A : Type ℓ} {B : A → Type ℓ'} (f g : (x : A) → B x) → Type (ℓ-max ℓ ℓ')
f ~ g = (x : _) → f x ≡ g x
infixr 4 _~_

~refl : {A : Type ℓ} {B : A → Type ℓ'} {f : (x : A) → B x} → f ~ f
~refl x = refl

~sym : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} → f ~ g → g ~ f
~sym p x = sym (p x)

~trans : {A : Type ℓ} {B : A → Type ℓ'} {f g h : (x : A) → B x} → f ~ g → g ~ h → f ~ h
~trans p q x = trans (p x) (q x)

~LWhisk : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : A → B) {g g' : B → C} → g ~ g' → (g ∘ f) ~ (g' ∘ f)
~LWhisk f p x = p (f x)

~RWhisk : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f f' : A → B} → f ~ f' → (g : B → C) → (g ∘ f) ~ (g ∘ f')
~RWhisk p g x = cong g (p x)

module _ {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
  hasLInv : Type (ℓ-max ℓ ℓ')
  hasLInv = Σ (B → A) (λ g → g ∘ f ~ id)

  hasRInv : Type (ℓ-max ℓ ℓ')
  hasRInv = Σ (B → A) (λ g → f ∘ g ~ id)

  hasQInv : Type (ℓ-max ℓ ℓ')
  hasQInv = Σ (B → A) (λ g → (g ∘ f ~ id) × (f ∘ g ~ id))

  isEquiv : Type (ℓ-max ℓ ℓ')
  isEquiv = hasLInv × hasRInv

  hasQInv→isEquiv : hasQInv → isEquiv
  hasQInv→isEquiv (g , left , right) = (g , left) , g , right

  isEquiv→hasQInv : isEquiv → hasQInv
  isEquiv→hasQInv ((g , left) , h , right) = g , left , λ { x → f (g x) ≡⟨ cong f (unicity x) ⟩
   f (h x) ≡⟨ right x ⟩
   id x ∎}
   where
   unicity : g ~ h
   unicity x = g x ≡⟨ cong g (sym (right x)) ⟩
    g (f (h x)) ≡⟨ left (h x) ⟩
    h x ∎

  postulate
   isPropIsEquiv : isProp isEquiv

Iso : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
Iso A B = Σ (A → B) hasQInv

_≃_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B = Σ (A → B) isEquiv
infix 4 _≃_

module _ {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) where
  equivFun : A → B
  equivFun = fst e

  invEq : B → A
  invEq = isEquiv→hasQInv equivFun (snd e) .fst

  retEq : invEq ∘ equivFun ~ id
  retEq = isEquiv→hasQInv equivFun (snd e) .snd .fst

  secEq : equivFun ∘ invEq ~ id
  secEq = isEquiv→hasQInv equivFun (snd e) .snd .snd

isoToEquiv : {A : Type ℓ} {B : Type ℓ'} → Iso A B → A ≃ B
isoToEquiv (f , g , left , right) = f , hasQInv→isEquiv f (g , left , right)

idEquiv : {A : Type ℓ} → A ≃ A
idEquiv = id , (id , λ x → refl) , id , λ x → refl

invEquiv : {A : Type ℓ} {B : Type ℓ'} → A ≃ B → B ≃ A
invEquiv (f , L , R) with isEquiv→hasQInv f (L , R)
... | g , left , right = g , (f , right) , f , left

compEquiv : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → A ≃ B → B ≃ C → A ≃ C
compEquiv (f , fL , fR) (g , gL , gR) with isEquiv→hasQInv f (fL , fR) | isEquiv→hasQInv g (gL , gR)
... | f' , fleft , fright | g' , gleft , gright = g ∘ f , (f' ∘ g' , λ { x → f' (g' (g (f x))) ≡⟨ cong f' (gleft (f x)) ⟩
 f' (f x) ≡⟨ fleft x ⟩
 x ∎}) , f' ∘ g'  , λ { x → g (f (f' (g' x))) ≡⟨ cong g (fright (g' x)) ⟩
 g (g' x) ≡⟨ gright x ⟩
 x ∎}

_≃⟨_⟩_ : (A : Type ℓ) {B : Type ℓ'} {C : Type ℓ''} → (A ≃ B) → (B ≃ C) → (A ≃ C)
_ ≃⟨ f ⟩ g = compEquiv f g

_■ : (A : Type ℓ) → (A ≃ A)
_■ A = idEquiv

infixr  0 _≃⟨_⟩_
infix   1 _■

equivEq : {A : Type ℓ} {B : Type ℓ'} {e e' : A ≃ B} → equivFun e ≡ equivFun e' → e ≡ e'
equivEq {ℓ} {ℓ'} {A} {B} {f , fL , fR} {g , gL , gR} refl with isEquiv→hasQInv f (fL , fR) | isEquiv→hasQInv g (gL , gR)
... | f' , fleft , fright | g' , gleft , gright = Σ≡ refl (Σ≡ {! !} {! !})


