{-# OPTIONS --prop --rewriting #-}

module ensembles where

--------------------------------------------------

open import core
open import logic
open import axioms

--------------------------------------------------

_∉_ : Ens → Ens → Prop
_∉_ x y = ¬ (x ∈ y)

--------------------------------------------------

_⊆_ : Ens → Ens → Prop
_⊆_ x y = ∀ a → a ∈ x → a ∈ y

sub-empty
 : ∀ x
 → ∅ ⊆ x
sub-empty x
 = λ z → exfalso

sub-self
 : ∀ x
 → x ⊆ x
sub-self x 
 = λ z
 → triv

--------------------------------------------------

ext′
 : ∀ {x y}
 → x ⊆ y
 → y ⊆ x
 → x ≡ y
ext′ xy yx
 = ext λ z
 → xy z
 * yx z

--------------------------------------------------

⟨_⟩ : Ens → Ens
⟨_⟩ x = x · ∅

singl-in
 : ∀ {a b}
 → a ∈ ⟨ b ⟩
 → a ≡ b
singl-in
 = |> triv exfalso

singl-inj
 : ∀ {a b}
 → ⟨ a ⟩ ≡ ⟨ b ⟩
 → a ≡ b
singl-inj {a} e
 = |> triv exfalso
 $ e> e a (inl equal)

singl-union
 : ∀ {a}
 → ∐ ⟨ a ⟩ ≡ a
singl-union {a}
 = ext λ z
 → #> (λ x → *> (|> (λ { equal → triv }) exfalso))
 * λ za → a # inl equal * za

--------------------------------------------------

⟨_,_⟩ : Ens → Ens → Ens
⟨_,_⟩ x y = x · y · ∅

--------------------------------------------------

_∪_ : Ens → Ens → Ens
_∪_ x y = ∐ ⟨ x , y ⟩

∪>
 : ∀ {x y z}
 → ((z ∈ x) ∨ (z ∈ y)) from (z ∈ (x ∪ y))
∪> f = #> λ u
     → *> (|> (λ { equal zx → f (inl zx) })
          (|> (λ { equal zy → f (inr zy) }) exfalso))

∪[]
 : ∀ {x y z}
 → ((z ∈ x) ∨ (z ∈ y))
 → (z ∈ (x ∪ y))
∪[] {x} {y}
  = |> (λ zx → x # inl equal * zx)
       (λ zy → y # inr (inl equal) * zy)

union-comm
 : ∀ {x y}
 → (x ∪ y) ≡ (y ∪ x)
union-comm
 = ext λ z
 → ∪> (|> (∪[] ∙ inr) (∪[] ∙ inl))
 * ∪> (|> (∪[] ∙ inr) (∪[] ∙ inl))

union-self
 : ∀ {x}
 → (x ∪ x) ≡ x
union-self
 = ext λ z
 → ∪> (|> triv triv)
 * ∪[] ∙ inl

--------------------------------------------------

∏ : Ens → Ens
∏ x = ⟨ z ∈ (∐ x) ∣ (∀ v → v ∈ x → z ∈ v) ⟩

_∩_ : Ens → Ens → Ens
_∩_ x y = ⟨ u ∈ x ∣ u ∈ y ⟩

inter-comm
 : ∀ {x y}
 → (x ∩ y) ≡ (y ∩ x)
inter-comm
 = ext λ z
 → *> (λ zx zy → zy * zx)
 * *> (λ zy zx → zx * zy)

inter-sub
 : ∀ {x y}
 → (x ∩ y) ⊆ x
inter-sub
 = λ z
 → *> const

inter-self
 : ∀ {x}
 → (x ∩ x) ≡ x
inter-self
 = ext λ z
 → *> const
 * λ zx → zx * zx

inter-empty
 : ∀ {x}
 → (x ∩ ∅) ≡ ∅
inter-empty
 = ext λ z
 → *> (const triv)
 * exfalso

--------------------------------------------------

_-_ : Ens → Ens → Ens
_-_ x y = ⟨ v ∈ x ∣ v ∉ y ⟩

--------------------------------------------------

_▲_ : Ens → Ens → Ens
_▲_ x y = (x - y) ∪ (y - x)

--------------------------------------------------
