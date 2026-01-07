{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import FunExtPostulate

private variable
  ℓ ℓ' : Level

isContr : Type ℓ → Type ℓ
isContr A = Σ A (λ x → (y : A) → x ≡ y)

isContr⊤ : isContr ⊤
isContr⊤ .fst = tt
isContr⊤ .snd y = refl

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
isProp'→isProp f x y = {! !}

isProp→isProp' : {A : Type ℓ} → isProp A → isProp' A
isProp→isProp' f x y = {! !}

