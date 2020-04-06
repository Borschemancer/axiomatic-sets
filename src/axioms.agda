{-# OPTIONS --prop --rewriting --confluence-check #-} 

module axioms where

--------------------------------------------------

open import Agda.Builtin.Coinduction 
open import core
open import logic

--------------------------------------------------

postulate
  _≝_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ

{-# BUILTIN REWRITE _≝_ #-}

--------------------------------------------------

postulate
  ∅ : Ens
  ω : Ens
  ∐ : Ens → Ens
  𝒫 : Ens → Ens
  _·_ : Ens → Ens → Ens
  comp : Ens → (Ens → Prop) → Ens
  repl : (Ens → Ens) → Ens → Ens

infixr 3 _·_
syntax comp y (λ x → body) = ⟨ x ∈ y ∣ body ⟩
syntax repl (λ x → body) y = ⟨ x ∈ y ↦ body ⟩

--------------------------------------------------

postulate
  ext : ∀ {x y} → (∀ z → (z ∈ x) ↔ (z ∈ y)) → x ≡ y
  adj : ∀ x y z → (z ∈ (x · y)) ≝ ((z ≡ x) ∨ (z ∈ y))
  uni : ∀ x z → (z ∈ (∐ x)) ≝ (∃ λ w → (w ∈ x) ∧ (z ∈ w))
  pow : ∀ x z → (z ∈ (𝒫 x)) ≝ (∀ a → a ∈ z → a ∈ x)
  emp : ∀ y → (y ∈ ∅) ≝ ⊥
  cmp : (φ : Ens → Prop) → ∀ z x → (x ∈ (comp z φ)) ≝ ((♯ (x ∈ z)) & (♯ (φ x)))
  rpl : ∀ x y φ → (y ∈ repl φ x) ≝ (∃ λ v → (v ∈ x) ∧ (y ≡ φ v))
  omg : ∀ x → (x ∈ ω) ≝ ((x ≡ ∅) ∨ ∃ λ y → (♯ (y ∈ ω)) & (♯ (x ≡ (y · y))))

{-# REWRITE adj uni pow emp cmp rpl omg #-}

--------------------------------------------------


