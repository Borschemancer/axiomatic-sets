{-# OPTIONS --prop --rewriting #-}

module ensembles where

--------------------------------------------------

open import core
open import logic
open import axioms

--------------------------------------------------

_∉_ : Ens → Ens → Prop
_∉_ x y = ¬ (x ∈ y)

empty
 : ∀ {x}
 → x ∉ ∅
empty
 = triv

is-empty : Ens → Prop
is-empty x = ∀ a → a ∉ x

empty-eq
 : ∀ {x}
 → is-empty x
 → x ≡ ∅
empty-eq emp
 = ext λ z
 → emp z
 * exfalso

--------------------------------------------------

_⊆_ : Ens → Ens → Prop
_⊆_ x y = ∀ a → a ∈ x → a ∈ y

empty-sub
 : ∀ x
 → ∅ ⊆ x
empty-sub x
 = λ z
 → exfalso

sub-self
 : ∀ x
 → x ⊆ x
sub-self x 
 = λ z
 → triv

sub-empty
 : ∀ {x}
 → x ⊆ ∅
 → x ≡ ∅
sub-empty xso
 = empty-eq xso

sub-trans
 : ∀ x y z
 → x ⊆ y
 → y ⊆ z
 → x ⊆ z
sub-trans x y z xsy ysz
 = λ u ux
 → ysz u (xsy u ux)

ext′
 : ∀ {x y}
 → x ⊆ y
 → y ⊆ x
 → x ≡ y
ext′ xsy ysx
 = ext λ z
 → xsy z
 * ysx z

_⊂_ : Ens → Ens → Prop
_⊂_ x y = (x ⊆ y) ∧ (x ≠ y)

not-psub-self
 : ∀ {x}
 → ¬ (x ⊂ x)
not-psub-self {x}
 = *> (const (exf-imp eq))

not-psub-sym
 : ∀ {x y}
 → x ⊂ y
 → ¬ (y ⊂ x)
not-psub-sym 
 = *> λ xsy _
 → *> λ ysx
 → exf-imp (ext′ ysx xsy)

{- TODO
psub-trans
 : ∀ x y z
 → x ⊂ y
 → y ⊂ z
 → x ⊂ z
psub-trans x y z
 = *> λ xsy xney
 → *> λ xsz ynez
 → sub-trans x y z xsy xsz
 * λ xez → {!!}
-}

psub-sub
 : ∀ {x y}
 → x ⊂ y
 → x ⊆ y
psub-sub
 = fst

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
 $ e> e a (inl eq)

singl-union
 : ∀ {a}
 → ∐ ⟨ a ⟩ ≡ a
singl-union {a}
 = ext λ z
 → #> (λ x → *> (|> (λ { eq → triv }) exfalso))
 * λ za → a # inl eq * za

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
     → *> (|> (λ { eq zx → f (inl zx) })
          (|> (λ { eq zy → f (inr zy) }) exfalso))

∪[]
 : ∀ {x y z}
 → ((z ∈ x) ∨ (z ∈ y)) to (z ∈ (x ∪ y))
∪[] {x} {y}
  = |> (λ zx → x # inl eq * zx)
       (λ zy → y # inr (inl eq) * zy)

union-comm
 : ∀ {x y}
 → (x ∪ y) ≡ (y ∪ x)
union-comm
 = ext λ z
 → ∪> (|> (∪[] ∙ inr) (∪[] ∙ inl))
 * ∪> (|> (∪[] ∙ inr) (∪[] ∙ inl))

union-assoc
 : ∀ {x y z}
 → (x ∪ (y ∪ z)) ≡ ((x ∪ y) ∪ z)
union-assoc
 = ext λ u
 → ∪> (|> (∪[] ∙ inl ∙ ∪[] ∙ inl)
          (∪> (|> (∪[] ∙ inl ∙ ∪[] ∙ inr)
                  (∪[] ∙ inr))))
 * ∪> (|> (∪> (|> (∪[] ∙ inl)
                  (∪[] ∙ inr ∙ ∪[] ∙ inl)))
          (∪[] ∙ inr ∙ ∪[] ∙ inr))

union-self
 : ∀ {x}
 → (x ∪ x) ≡ x
union-self
 = ext λ z
 → ∪> (|> triv triv)
 * ∪[] ∙ inl

union-empty
 : ∀ {x}
 → (x ∪ ∅) ≡ x
union-empty
 = ext λ z
 → ∪> (|> triv exfalso)
 * ∪[] ∙ inl

union-sub
 : ∀ {x y z}
 → x ⊆ z
 → y ⊆ z
 → (x ∪ y) ⊆ z
union-sub xsz ysz
 = λ u
 → ∪> (|> (xsz u) (ysz u))

--------------------------------------------------

∏ : Ens → Ens
∏ x = ⟨ z ∈ (∐ x) ∣ (∀ v → v ∈ x → z ∈ v) ⟩

_∩_ : Ens → Ens → Ens
_∩_ x y = ⟨ u ∈ x ∣ u ∈ y ⟩

∩>
 : ∀ {x y z}
 → (z ∈ (x ∩ y)) from (z ∈ ∏ ⟨ x , y ⟩)
∩> {x} {y} {z} f
 = *> (#> λ u
 → *> (|> (λ { eq zx g → f (zx * g y (inr (inl eq))) })
      (|> (λ { eq zy g → f (g x (inl eq) * zy) })
          exfalso)))

inter-comm
 : ∀ {x y}
 → (x ∩ y) ≡ (y ∩ x)
inter-comm
 = ext λ z
 → *> (λ zx zy → zy * zx)
 * *> (λ zy zx → zx * zy)

inter-assoc
 : ∀ {x y z}
 → (x ∩ (y ∩ z)) ≡ ((x ∩ y) ∩ z)
inter-assoc
 = ext λ u
 → *> (λ ux → *> λ uy uz → (ux * uy) * uz)
 * *> (*> λ ux uy uz → ux * uy * uz)

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

{- TODO
inter-sub-eq
 : ∀ {x y}
 → (x ⊆ y) ↔ ((x ∩ y) ≡ x)
inter-sub-eq
 = {!!}
 * {!!}
-}

distr-int-uni
 : ∀ {x y z}
 → ((x ∪ y) ∩ z) ≡ ((x ∩ z) ∪ (y ∩ z))
distr-int-uni
 = ext λ u
 → *> (∪> (|> (λ ux uz → ∪[] (inl (ux * uz)))
              (λ uy uz → ∪[] (inr (uy * uz)))))
 * ∪> (|> (*> λ ux uz → ∪[] (inl ux) * uz)
          (*> λ uy uz → ∪[] (inr uy) * uz))

distr-uni-int
 : ∀ {x y z}
 → ((x ∩ y) ∪ z) ≡ ((x ∪ z) ∩ (y ∪ z))
distr-uni-int
 = ext λ u
 → ∪> (|> (*> λ ux uy → ∪[] (inl ux) * ∪[] (inl uy))
          (λ uz → ∪[] (inr uz) * ∪[] (inr uz)))
 * *> (∪> (|> (λ ux → ∪> (|> (λ uy → ∪[] (inl (ux * uy)))
                             (λ uz → ∪[] (inr uz))))
              (λ uz → ∪> (|> (λ uy → ∪[] (inr uz))
                             (λ uz → ∪[] (inr uz))))))

--------------------------------------------------

_-_ : Ens → Ens → Ens
_-_ x y = ⟨ v ∈ x ∣ v ∉ y ⟩

dif-self
 : ∀ {x}
 → (x - x) ≡ ∅
dif-self
 = ext λ z
 → *> exf-imp
 * exfalso

dif-int
 : ∀ {x y}
 → (x - (x ∩ y)) ≡ (x - y)
dif-int
 = ext λ z
 → *> (λ zx f → zx * λ zy → f (zx * zy))
 * *> (λ zx f → zx * *> (const f))

int-dif-eq-dif
 : ∀ {x y}
 → (x ∩ (x - y)) ≡ (x - y)
int-dif-eq-dif
 = ext λ z
 → *> (λ zx → *> λ _ nzy → zx * nzy)
 * *> λ zx nzy → zx * zx * nzy

dif-int-sec
 : ∀ {x y}
 → ((x - y) ∩ y) ≡ ∅
dif-int-sec
 = ext λ z
 → *> (*> (const (flp exf-imp)))
 * exfalso

--------------------------------------------------

_▲_ : Ens → Ens → Ens
_▲_ x y = (x - y) ∪ (y - x)

--------------------------------------------------
