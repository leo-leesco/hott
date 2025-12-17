{-# OPTIONS --without-K #-}
open import Prelude

private variable
  ℓ ℓ' ℓ'' : Level

sym : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

J : {A : Type ℓ} {x : A} (P : (y : A) → x ≡ y → Type ℓ') → P x refl → {y : A} (p : x ≡ y) → P y p
J P x refl = x

sym' : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym' {ℓ} {A} {x} {y} e = J (λ { y₁ p → y₁ ≡ x }) refl e

trans : {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

infixr 30 _∙_
_∙_ = trans

lUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ refl ∙ p
lUnit refl = refl

rUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ p ∙ refl
rUnit refl = refl

lCancel : {A : Type ℓ} {x y : A} (p : x ≡ y) → sym p ∙ p ≡ refl
lCancel refl = refl

rCancel : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
rCancel refl = refl

assoc : {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
assoc refl refl refl = refl

symInvo : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ sym (sym p)
symInvo refl = refl

cong : {A : Type ℓ} {B : Type ℓ'} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
cong f refl = refl

≡× : {A : Type ℓ} {B : Type ℓ'} {x x' : A} {y y' : B} → (x , y) ≡ (x' , y') → (x ≡ x') × (y ≡ y')
≡× xy≡x'y' = cong fst xy≡x'y' , cong snd xy≡x'y'

congConst : {A : Type ℓ} {B : Type ℓ'} {x' : B} {x y : A} (p : x ≡ y) → cong (λ _ → x') p ≡ refl
congConst refl = refl

congComposite : {A : Type ℓ} {B : Type ℓ'} {x y z : A} (f : A -> B) (p : x ≡ y) (q : y ≡ z) → cong f (p ∙ q) ≡ (cong f p) ∙ (cong f q)
congComposite f refl refl = refl

congSym : {A : Type ℓ} {B : Type ℓ'} {x y z : A} (f : A -> B) (p : x ≡ y) → cong f (sym p) ≡ sym (cong f p)
congSym f refl = refl

congId : {A : Type ℓ} {x y : A} (p : x ≡ y) → cong id p ≡ p
congId refl = refl

cong∘ : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {x y : A} (f : A -> B) (g : B -> C) (p : x ≡ y) -> cong (g ∘ f) p ≡ cong g (cong f p)
cong∘ f g refl = refl

-- cong₂ : {A A' : Type ℓ} {B : Type ℓ'} {x y x' y' : A} (f : A × A' -> B) (p : x ≡ y) (q : x' ≡ y') -> cong f (p , q)

rotate∙≡ : {A : Type ℓ} {x y y' : A} (p : x ≡ y) (q : y ≡ y') (p' : x ≡ y') → p ∙ q ≡ p' → sym p ∙ p' ≡ q
rotate∙≡ p q p' α = sym p ∙ p' ≡⟨ cong (λ { x → sym p ∙ x }) (sym α) ⟩
  sym p ∙ (p ∙ q) ≡⟨ assoc (sym p) p q ⟩
  (sym p ∙ p) ∙ q ≡⟨ cong (λ { x → x ∙ q }) (lCancel p) ⟩
  refl ∙ q ≡⟨ sym (lUnit q) ⟩
  q ∎

subst : {A : Type ℓ} (B : A → Type ℓ') {x y : A} (p : x ≡ y) → B x → B y
subst B refl Bx = Bx
