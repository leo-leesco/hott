{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import FunExtPostulate

private variable
  ℓ ℓ' : Level

isContr : Type ℓ → Type ℓ
isContr A = Σ A (λ x → (y : A) → x ≡ y)

isContr⊤ : isContr ⊤
isContr⊤ = tt , λ y → refl

¬isContrBool : ¬ (isContr Bool)
¬isContrBool (false , f) = true≢false (sym (f true))
¬isContrBool (true , f) = true≢false (f false)

isContr× : {A : Type ℓ} {B : Type ℓ'} → isContr A → isContr B → isContr (A × B)
isContr× (x , f) (y , g) = (x , y) , λ { (x' , y') → ×pack (f x') (g y') }

isContr→isContrPath : {A : Type ℓ} → isContr A → (x y : A) → isContr (x ≡ y)
isContr→isContrPath (x , f) y z = trans (sym (f y)) (f z) , λ { refl → lCancel (f y) }

singl : {A : Type ℓ} → A → Type ℓ
singl {A = A} a = Σ A λ x → a ≡ x

isContrSingl : {A : Type ℓ} (a : A) → isContr (singl a)
isContrSingl a = (a , refl) , λ { (a' , refl) → refl }

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

isProp⊥ : isProp ⊥
isProp⊥ ()

isProp⊤ : isProp ⊤
isProp⊤ x y = refl

¬isPropBool : ¬ (isProp Bool)
¬isPropBool f = true≢false (f true false)

isContr→isProp : {A : Type ℓ} → isContr A → isProp A
isContr→isProp (x , f) y z = trans (sym (f y)) (f z)

isProp→isContr : {A : Type ℓ} → isProp A → A → isContr A
isProp→isContr f x = x , λ { y → f x y }

isContr→isProp' : {A : Type ℓ} → (A → isContr A) → isProp A
isContr→isProp' f x y with f x
... | z , g = trans (sym (g x)) (g y)

isProp→isContrPath : {A : Type ℓ} → isProp A → (x y : A) → isContr (x ≡ y)
isProp→isContrPath f x y = isContr→isContrPath (isProp→isContr f x) x y

isProp' : Type ℓ → Type ℓ
isProp' A = (x y : A) → isContr (x ≡ y)

isProp'→isProp : {A : Type ℓ} → isProp' A → isProp A
isProp'→isProp f x y with f x y
... | e , _ = e

isProp→isProp' : {A : Type ℓ} → isProp A → isProp' A
isProp→isProp' f x y = isProp→isContr (isContr→isProp' λ { refl → isContr→isContrPath (x , f x) x x }) (f x y)

×packDep : {A : Type ℓ} {B : Type ℓ'} {x y : A} {f g : A → B}  → (p : x ≡ y) → (q : f ≡ g) → (x , f) ≡ (y , g)
×packDep {ℓ} {ℓ'} {A} {B} {x} {y} {f} {g} p q = ×pack p q

isPropIsContr : {A : Type ℓ} → isProp (isContr A)
isPropIsContr {A = A} (x , p) (y , q) = Σ≡ (p y) (funExt λ { z → isContr→isProp (isContr→isContrPath (x , p) y z) (subst (λ x₁ → (y₁ : A) → x₁ ≡ y₁) (p y) p z) (q z) })

isPropIsProp : {A : Type ℓ} → isProp (isProp A)
isPropIsProp p q = funExt λ { x → funExt λ { y → isContr→isProp (isContr→isContrPath (isProp→isContr p x) x y) (p x y) (q x y) } }

isProp× : {A : Type ℓ} {B : Type ℓ'} → isProp A → isProp B → isProp (A × B)
isProp× p q (x , y) (x' , y') = ×pack (p x x') (q y y')

isProp⊎ : {A : Type ℓ} {B : Type ℓ'} → isProp A → isProp B → (A → B → ⊥) → isProp (A ⊎ B)
isProp⊎ p q f (inl x) (inl y) = cong inl (p x y)
isProp⊎ p q f (inl x) (inr y) with f x y
... | ()
isProp⊎ p q f (inr x) (inl y) with f y x
... | ()
isProp⊎ p q f (inr x) (inr y) = cong inr (q x y)

isProp→ : {A : Type ℓ} {B : Type ℓ'} → isProp B → isProp (A → B)
isProp→ p f g = funExt λ { a → p (f a) (g a) }

isPropΠ : {A : Type ℓ} (B : A → Type ℓ') → ((x : A) → isProp (B x)) → isProp ((x : A) → B x)
isPropΠ B p f g = funExt λ { x → isContr→isProp (f x , p x (f x)) (f x) (g x) }

isProp¬ : {A : Type ℓ} → isProp (¬ A)
isProp¬ = isProp→ isProp⊥

isPropΣ : {A : Type ℓ} (B : A → Type ℓ') → isProp A → ((x : A) → isProp (B x)) → isProp (Σ A B)
isPropΣ B p q (x , y) (x' , y') = Σ≡ (p x x') (isContr→isProp (y' , q x' y') (subst B (p x x') y) y')

Dec : Type ℓ → Type ℓ
Dec A = A ⊎ ¬ A

isPropDec : {A : Type ℓ} → isProp A → isProp (Dec A)
isPropDec p (inl x) (inl y) = cong inl (p x y)
isPropDec p (inl x) (inr y) with y x
... | ()
isPropDec p (inr x) (inl y) with x y
... | ()
isPropDec p (inr x) (inr y) = cong inr (isContr→isProp (isProp→isContr isProp¬ x) x y)

hProp : (ℓ : Level) → Type (ℓ-suc ℓ)
hProp ℓ = Σ (Type ℓ) isProp

_∧_ : hProp ℓ → hProp ℓ → hProp ℓ
(x , p) ∧ (y , q) = x × y , λ { (x₁ , y₁) (x₂ , y₂) → ×pack (p x₁ x₂) (q y₁ y₂) }

sub : {A : Type ℓ} (P : A → hProp ℓ) → Type ℓ
sub {A = A} P = Σ A (fst ∘ P)

subInj : {A : Type ℓ} (P : A → hProp ℓ) {x y : sub P} → fst x ≡ fst y → x ≡ y
subInj {ℓ} {A} P {x , π} {y , ρ} p = Σ≡ p (isContr→isProp (ρ , λ { σ → unif P ρ σ }) (subst (λ x₁ → fst (P x₁)) p π) ρ)
 where
 unif : {A : Type ℓ} (P : A → hProp ℓ) {y : A} -> (x₁ y₁ : P y .fst) → x₁ ≡ y₁
 unif P x₁ y₁ = P _ .snd x₁ y₁
