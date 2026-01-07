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

true≢false : ¬ true ≡ false
true≢false tf = subst (λ { false → ⊥
                         ; true → true ≡ false }) tf tf

transport : {A B : Type ℓ} → A ≡ B → A → B
transport e a = subst (λ z → z) e a

subst' : {A : Type ℓ} (B : A → Type ℓ') {x y : A} (p : x ≡ y) → B x → B y
subst' B p x = transport (cong B p) x

substComposite : {A : Type ℓ} (B : A → Type ℓ) {x y z : A} (p : x ≡ y) (q : y ≡ z) (x' : B x) → subst B (p ∙ q) x' ≡ subst B q (subst B p x')
substComposite B refl refl x' = refl

substConst : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} {x y : A} (p : x ≡ y) (x' : B) → subst (λ _ → B) p x' ≡ x'
substConst refl x' = refl

substInPathsL : {A : Type ℓ} {x y y' : A} (p : x ≡ y) (q : y ≡ y') → subst (λ y → x ≡ y) q p ≡ p ∙ q
substInPathsL refl refl = refl

substInPathsR : {A : Type ℓ} {x x' y : A} (p : x ≡ x') (q : x ≡ y) → subst (λ x → x ≡ y) p q ≡ sym p ∙ q
substInPathsR refl refl = refl

substInPaths : {A : Type ℓ} {B : Type ℓ'}  {x y : A} (f g : A → B) (p : x ≡ y) (q : f x ≡ g x) → subst (λ x → f x ≡ g x) p q ≡ sym (cong f p) ∙ q ∙ cong g p
substInPaths f g refl q = subst (λ x₁ → f x₁ ≡ g x₁) refl q ≡⟨ refl ⟩
 q ≡⟨ rUnit q ⟩
 q ∙ refl ≡⟨ lUnit (trans q refl) ⟩
 refl ∙ q ∙ refl ≡⟨ refl ⟩
 sym (cong f refl) ∙ q ∙ cong g refl ∎

substInPathsL' : {A : Type ℓ} {B : Type ℓ'}  {x x' : A} (f : A → B) {y : B} (p : x ≡ x') (q : f x ≡ y) → subst (λ x → f x ≡ y) p q ≡ sym (cong f p) ∙ q
substInPathsL' {ℓ} {ℓ'} {A} {B} {x} {x'} f {y} refl q = subst (λ x₁ → f x₁ ≡ y) refl q ≡⟨ refl ⟩
 q  ≡⟨ lUnit q ⟩
 refl ∙ q  ≡⟨ refl ⟩
 sym (cong f refl) ∙ q ∎
