open import Prelude

comm× : {A B : Type} → A × B → B × A
comm× (a , b) = b , a

comm×-involutive : {A B : Type} (a : A) (b : B) → comm× (comm× (a , b)) ≡ (a , b)
comm×-involutive a b = refl

assoc× : {A B C : Type} → (A × B) × C → A × (B × C)
assoc× ((fst₁ , snd₂) , snd₁) = fst₁ , snd₂ , snd₁

comm⊎ : {A B : Type} → A ⊎ B → B ⊎ A
comm⊎ (inl x) = inr x
comm⊎ (inr x) = inl x

comm⊎-involutive : {A B : Type} (ab : A ⊎ B) → comm⊎ (comm⊎ ab) ≡ ab
comm⊎-involutive (inl x) = refl
comm⊎-involutive (inr x) = refl

dist⊎ : {A B C : Type} → A × (B ⊎ C) → (A × B) ⊎ (A × C)
dist⊎ (a , inl x) = inl (a , x)
dist⊎ (a , inr x) = inr (a , x)

currying : {A B C : Type} → (A × B → C) ↔ (A → B → C)
currying .fst x x₁ x₂ = x (x₁ , x₂)
currying .snd x (fst₁ , snd₁) = x fst₁ snd₁

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

pred : ℕ → ℕ
pred zero = zero
pred (suc x) = x

cong : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

unitr+ : (n : ℕ) → n + zero ≡ n
unitr+ zero = refl
unitr+ (suc n) = suc (n + zero) ≡⟨ cong suc (unitr+ n) ⟩
 suc n ∎

assoc+ : (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
assoc+ zero n o = refl
assoc+ (suc m) n o = ((suc m + n) + o) ≡⟨ refl ⟩
 suc (m + n) + o ≡⟨ refl ⟩
 suc((m + n) + o) ≡⟨ cong suc (assoc+ m n o) ⟩
 suc(m + (n + o)) ≡⟨ refl ⟩
 suc m + (n + o) ∎

sym : {A : Type} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

+suc : (m n : ℕ) → m + (suc n) ≡ suc (m + n)
+suc zero n = refl
+suc (suc m) n = (suc m + suc n) ≡⟨ refl ⟩
 suc (m + suc n) ≡⟨ cong suc (+suc m n) ⟩
 suc (suc (m + n)) ≡⟨ refl ⟩
 suc (suc m + n) ∎

comm+ : (m n : ℕ) → m + n ≡ n + m
comm+ zero n = sym (unitr+ n)
comm+ (suc m) n = (suc m + n) ≡⟨ refl ⟩
 suc (m + n) ≡⟨ cong suc (comm+ m n) ⟩
 suc (n + m) ≡⟨ sym (+suc n m) ⟩
 (n + suc m) ∎

pred-suc : (n : ℕ) → pred (suc n) ≡ n
pred-suc zero = refl
pred-suc (suc n) = refl

suc-pred : (n : ℕ) → ¬ (n ≡ zero) → suc (pred n) ≡ n
suc-pred zero x = ⊥-rec (x refl)
suc-pred (suc n) x = refl

zero-suc : (n : ℕ) → ¬ (zero ≡ suc n)
zero-suc n ()

suc-inj : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

nat-eq-dec : (m n : ℕ) → (m ≡ n) ⊎ ¬ (m ≡ n)
nat-eq-dec zero zero = inl refl
nat-eq-dec zero (suc n) = inr λ ()
nat-eq-dec (suc m) zero = inr λ ()
nat-eq-dec (suc m) (suc n) with nat-eq-dec m n
... | inl eq = inl (cong suc eq)
... | inr neq = inr λ { x → neq (suc-inj x) }

div2 : (n : ℕ) → Σ ℕ (λ q → q + q ≡ n ⊎ suc (q + q) ≡ n)
div2 zero = 0 , inl refl
div2 (suc zero) = 0 , inr refl
div2 (suc (suc n)) with div2 n
... | m , inl x = suc m , inl ( suc (m + suc m) ≡⟨ cong suc (+suc m m) ⟩
 suc (suc (m + m)) ≡⟨ cong (λ { x₁ → suc (suc x₁) }) x ⟩
 suc (suc n) ∎)
... | m , inr x = suc m , inr ( suc (suc m + suc m) ≡⟨ cong (λ { x₁ → suc (suc x₁) }) (+suc m m) ⟩
 suc(suc (suc (m + m))) ≡⟨ cong (λ { x₁ → suc (suc x₁) }) x ⟩
 suc (suc n) ∎)

subst : {A : Type} (P : A → Type) {x y : A} → x ≡ y → P x → P y
subst P refl x₁ = x₁

data Even : ℕ → Type where
  evenZero : Even zero
  evenSuc  : {n : ℕ} → Even n → Even (suc (suc n))

double-even : (n : ℕ) → Even (n + n)
double-even zero = evenZero
double-even (suc n) = subst Even (
 suc (suc (n + n)) ≡⟨ cong suc (sym (+suc n n)) ⟩
 suc (n + suc n) ∎
 ) (evenSuc (double-even n))

rec⊎ : {A B C : Type} → (A → C) → (B → C) → A ⊎ B → C
rec⊎ f g (inl x) = f x
rec⊎ f g (inr x) = g x

elim⊎ : {A B : Type} (C : A ⊎ B → Type) → ((x : A) → C (inl x)) → ((x : B) → C (inr x)) → (x : A ⊎ B) → C x
elim⊎ C f g (inl x) = f x
elim⊎ C f g (inr x) = g x

comp⊎l : {A B : Type} (C : A ⊎ B → Type) (f : (x : A) → C (inl x)) (g : (x : B) → C (inr x)) (x : A) → elim⊎ C f g (inl x) ≡ f x
comp⊎l C f g x = refl

uniq⊎ : {A B : Type} (x : A ⊎ B) → elim⊎ (λ _ → A ⊎ B) inl inr x ≡ x
uniq⊎ (inl x) = refl
uniq⊎ (inr x) = refl

rec× : {A B C : Type} → (A → B → C) → A × B → C
rec× = snd currying

elim× : {A B : Type} (C : A × B → Type) → ((x : A) → (y : B) → C (x , y)) → (x : A × B) → C x
elim× C f (x , y) = f x y

-- comp× : {A B : Type} (C : A × B → Type) (f : (x : A) → (y : B) → C (x , y)) ((x , y) : A × B) → elim× C f g (x , y) ≡ (f x , g y)
-- comp× = ?

-- uniq× : {A B : Type} (x : A × B) → elim× (λ _ → A × B) inl inr x ≡ x
-- uniq× (inl x) = refl
-- uniq× (inr x) = refl
