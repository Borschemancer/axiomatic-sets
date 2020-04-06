{-# OPTIONS --prop #-}

module logic where

--------------------------------------------------

open import Agda.Builtin.Coinduction
open import core

--------------------------------------------------

data ⊤ : Prop where
  ★ : ⊤

data ⊥ : Prop where

--------------------------------------------------

¬ : Prop → Prop
¬ A = A → ⊥

exfalso : {P : Prop} → ⊥ → P
exfalso ()

--------------------------------------------------

infixr 3 _∧_
infixr 3 _*_
infixr 2 _∨_

data _∨_ (A B : Prop) : Prop where
  inl : A → A ∨ B
  inr : B → A ∨ B

record _&_ (A B : ∞ Prop) : Prop where
  constructor _*_
  field
    fst : ♭ A
    snd : ♭ B

open _&_

_₁ = fst
_₂ = snd

_∧_ : Prop → Prop → Prop
_∧_ A B = (♯ A) & (♯ B)

--------------------------------------------------

_↔_ : Prop → Prop → Prop
_↔_ A B = (A → B) ∧ (B → A)

eq-iff
 : ∀ {p}
 → p ↔ p
eq-iff
 = (λ x → x)
 * (λ x → x)

--------------------------------------------------

|> : {P Q T : Prop} → (P → T) → (Q → T) → (P ∨ Q) → T
|> f g (inl x) = f x
|> f g (inr x) = g x

*> : {P Q : ∞ Prop} {T : Prop} → (♭ P → ♭ Q → T) → (P & Q) → T
*> f (p * q) = f p q

triv : {P : Prop} → P → P
triv p = p

const : {P Q : Prop} → P → Q → P
const p q = p

infixr 9 _∙_
_∙_ : {P Q R : Prop} → (Q → R) → (P → Q) → (P → R)
_∙_ f g = λ z → f (g z)

infixr 0 _$_
_$_ : {P Q : Prop} → (P → Q) → P → Q
_$_ f p = f p

exf-imp
 : ∀ {P Q}
 → P
 → ¬ P
 → Q
exf-imp p np
 = exfalso (np p)

exf-iff
 : ∀ {P}
 → ¬ (P ↔ (¬ P))
exf-iff
 = *> λ f g
 → f (g λ x → f x x) (g (f (g λ x → f x x)))

--------------------------------------------------

postulate
  lem : ∀ P {T : Prop} → (P → T) → (¬ P → T) → T

syntax lem P f g = P ⁇ f ∷ g -- à la ternary if-then-else

--------------------------------------------------

not-not
 : ∀ {P}
 → ¬ (¬ P) ↔ P
not-not {P}
 = P
 ⁇ const
 ∷ exf-imp
 * λ p np → np p

cont-imp
 : ∀ {P Q}
 → ((¬ Q) → (¬ P)) ↔ (P → Q)
cont-imp {P} {Q}
 = Q
 ⁇ (const ∙ const)
 ∷ (λ nq f p → exfalso (f nq p))
 * (λ f nq p → nq (f p))

--------------------------------------------------

data _≡_ (x : Ens) : Ens → Prop where
  equal : x ≡ x

_≠_ : Ens → Ens → Prop
_≠_ x y = ¬ (x ≡ y)

e>
 : ∀ {x y}
 → x ≡ y
 → (∀ z → z ∈ x → z ∈ y)
e> equal
 = λ z → triv

ê>
 : ∀ {x y}
 → x ≡ y
 → (∀ z → x ∈ z → y ∈ z)
ê> equal
 = λ z → triv

sym
 : ∀ {x y}
 → x ≡ y
 → y ≡ x
sym equal
 = equal 

--------------------------------------------------

infixr 3 _#_

data ∃ (p : Ens → Prop) : Prop where
 _#_ : (x : Ens) → p x → ∃ p

#>
 : ∀ {p} {r : Prop}
 → ((x : Ens) → p x → r)
 → (∃ p → r)
#> f (x # px)
 = f x px

--------------------------------------------------

uniq : (Ens → Prop) → Prop
uniq p = ∀ x y → p x → p y → x ≡ y

∃! : (Ens → Prop) → Prop 
∃! p = ∃ λ x → (p x) ∧ (uniq p)

#!>
 : ∀ {p} {r : Prop}
 → ((x : Ens) → p x → (∀ y → p y → y ≡ x) → r)
 → (∃! p → r)
#!> f
 = #> λ x
 → *> λ px up
 → f x px λ y py
 → up y x py px

--------------------------------------------------

_from_ : Prop → Prop → Prop₁
_from_ P Q = {T : Prop} → (P → T) → (Q → T)

