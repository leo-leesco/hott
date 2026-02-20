{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import HLevels
open import Equivalence

private variable
  ℓ ℓ' : Level

pathToEquiv : {A B : Type ℓ} → A ≡ B → A ≃ B
pathToEquiv {A = A} {B = B} e = transport e , eq e
 where
 eq : (p : A ≡ B) -> isEquiv(transport p)
 eq refl = (id , λ x → refl) , (id , λ x → refl)

pathToEquivTest : {A B : Type ℓ} (p : A ≡ B) → equivFun (pathToEquiv p) ≡ transport p
pathToEquivTest p = refl

postulate
  -- Univalence!
  isEquivPathToEquiv : {A B : Type ℓ} → isEquiv (pathToEquiv {A = A} {B = B})

univalence : {A B : Type ℓ} → (A ≡ B) ≃ (A ≃ B)
univalence = pathToEquiv , isEquivPathToEquiv

ua : {A B : Type ℓ} → A ≃ B → A ≡ B
ua {A = A} {B = B} = invEq univalence

uaβ : {A B : Type ℓ} (e : A ≃ B) → transport (ua e) ≡ equivFun e
uaβ {A = A} {B = B} e = cong fst (secEq univalence e)

uaη : {A B : Type ℓ} (p : A ≡ B) → ua (pathToEquiv p) ≡ p
uaη p = retEq univalence p

uaIdEquiv : {A : Type ℓ} → ua (idEquiv {A = A}) ≡ refl
uaIdEquiv = uaη refl

isContr≃≡⊤ : {A : Type} → isContr A ≃ (A ≡ ⊤)
isContr≃≡⊤ {A = A} = isoToEquiv (f , g , gf , fg)
 where
 f : isContr A → A ≡ ⊤
 f = ua ∘ isContr→≃⊤

 g : A ≡ ⊤ → isContr A
 g = ≃⊤→isContr ∘ pathToEquiv

 gf : (x : isContr A) → g (f x) ≡ x
 gf x = ((≃⊤→isContr ∘ pathToEquiv) ∘ (ua ∘ isContr→≃⊤)) x ≡⟨ refl ⟩
  (≃⊤→isContr ∘ (pathToEquiv ∘ ua) ∘ isContr→≃⊤) x ≡⟨ cong ≃⊤→isContr (secEq univalence (isContr→≃⊤ x)) ⟩
  (≃⊤→isContr ∘ id ∘ isContr→≃⊤) x ≡⟨ refl ⟩
  (≃⊤→isContr ∘ isContr→≃⊤) x ≡⟨ isContrInv x ⟩
  x ∎
  where
  isContrInv : (≃⊤→isContr ∘ isContr→≃⊤) ~ id
  isContrInv x = refl

 fg : (x : A ≡ ⊤) → f (g x) ≡ id x
 fg refl = uaIdEquiv

is¬≃≡⊥ : {A : Type} → (¬ A) ≃ (A ≡ ⊥)
is¬≃≡⊥ {A = A} = ¬ A ≃⟨ isoToEquiv (f , g , gf , fg) ⟩
 A ≃ ⊥ ≃⟨ invEquiv univalence ⟩
 A ≡ ⊥ ■
 where
 f : ¬ A → A ≃ ⊥
 f x = isoToEquiv (x , (λ ()) , (λ { y → ⊥-rec (x y) }) , λ { y → ⊥-rec y })

 g : (A ≃ ⊥) → (¬ A)
 g (f , _) x = f x

 gf : (x : ¬ A) → g (f x) ≡ x
 gf x = refl

 fg : (x : A ≃ ⊥) → f (g x) ≡ x
 fg x = equivEq refl

≃ind : (P : {A B : Type ℓ} → (A ≃ B) → Type ℓ') → ({A : Type ℓ} → P (idEquiv {A = A})) → {A B : Type ℓ} (e : A ≃ B) → P e
≃ind {ℓ} {ℓ'} P x {A} {B} e = subst P (secEq univalence e) Pp
 where
 p : A ≡ B
 p = ua e

 Pp : P (pathToEquiv p)
 Pp = pathInduction p
  where
  pathInduction : (eq : A ≡ B) → P (pathToEquiv eq)
  pathInduction refl = x

¬isSetType : ¬ (isSet Type)
¬isSetType setType = let isPropBool = setType Bool Bool in
 let p = ua not≃ in
 let reflNot = isPropBool p refl in
 true≢false ( true ≡⟨ sym (happly (uaβ not≃) false) ⟩
  transport p false ≡⟨ cong (λ { q → transport q false }) reflNot ⟩
  transport refl false ≡⟨ refl ⟩
  false ∎)

¬NNE : ¬ ((A : Type) → ¬ ¬ A → A)
¬NNE nne =
 let
  f = nne Bool
  p = ua not≃
  g = subst (λ { X → ¬ (¬ X) → X }) p f

  q : g ≡ f
  q = congP (λ { X → ¬ (¬ X) → X }) nne p

  x : ¬ ¬ Bool
  x nb = nb true

  x' : ¬ ¬ Bool
  x' = subst (λ { X → ¬ (¬ X) }) p x

  fx'≡notfx' : f x' ≡ not (f x')
  fx'≡notfx' = f x' ≡⟨ sym (happly q x') ⟩
   g x' ≡⟨ happly (funTypeTransp (λ X → ¬ (¬ X)) (λ X → X) p f) x' ⟩
   subst (λ X → X) p (f (subst (λ X → ¬ (¬ X)) (sym p) x')) ≡⟨ happly (uaβ not≃) (f (subst (λ X → ¬ (¬ X)) (sym p) x')) ⟩
   not (f (subst (λ X → ¬ (¬ X)) (sym p) x')) ≡⟨ cong (λ { x'' → not (f x'') }) (isProp¬ (subst (λ X → ¬ (¬ X)) (sym p) x') x') ⟩
   not (f x') ∎
 in
 absurd (f x') fx'≡notfx'
 where
  absurd : (b : Bool) → ¬ (b ≡ not b)
  absurd false x = true≢false (sym x)
  absurd true x = true≢false x

postulate
 ¬LEM : ¬ ((A : Type) → A ⊎ ¬ A)

 decProp : Σ Type (λ A → isProp A × Dec A) ≃ Bool
