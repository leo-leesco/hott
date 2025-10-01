{-# OPTIONS --without-K #-}
open import Prelude

private variable
  ℓ ℓ' ℓ'' : Level

sym : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

J : {A : Type ℓ} {x : A} (P : (y : A) → x ≡ y → Type ℓ') → P x refl → {y : A} (p : x ≡ y) → P y p
J P x refl = x

sym' : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym' x = {! !}
