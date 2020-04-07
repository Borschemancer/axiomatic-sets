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
 = prj₁

--------------------------------------------------

⟨_,_⟩ : Ens → Ens → Ens
⟨_,_⟩ x y = x · y · ∅

pe>
 : ∀ {x y u v}
 → ((x ≡ u) ∧ (y ≡ v) ∨ (x ≡ v) ∧ (y ≡ u)) from (⟨ x , y ⟩ ≡ ⟨ u , v ⟩)
pe> {x} {y} {u} {v} {T} f e
 with
    (e> e x (inl eq))
  | (e> e y (inr (inl eq)))
… | inl eq | inl eq =
  let e′ = (e> (eq-sym e) v (inr (inl eq)))
      f′ vex = f (inl (eq * eq-sym vex)) in
      |> f′ (|> f′ exfalso) e′
… | inl xeu | inr (inl yev) = f (inl (xeu * yev))
… | inr (inl xev) | inl yeu = f (inr (xev * yeu))
… | inr (inl eq)  | inr (inl eq) =
  let e′ = e> (eq-sym e) u (inl eq)
      f′ uex = f (inr (eq * (eq-sym uex))) in
      |> f′ (|> f′ exfalso) e′

pair-eq
 : ∀ {x y u v}
 → x ≡ u
 → y ≡ v
 → ⟨ x , y ⟩ ≡ ⟨ u , v ⟩
pair-eq eq eq
 = eq

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

singl-self-pair-eq
 : ∀ {x}
 → ⟨ x ⟩ ≡ ⟨ x , x ⟩
singl-self-pair-eq
 = ext λ z
 → |> inl exfalso
 * |> inl (|> inl exfalso)

singl-pair-eq
 : ∀ {x y z}
 → ⟨ x ⟩ ≡ ⟨ y , z ⟩
 → (x ≡ y) ∧ (x ≡ z)
singl-pair-eq {x} e
 = pe> (|> triv (*> λ xez xey → xey * xez))
 $ eq-trans (eq-sym singl-self-pair-eq) e

--------------------------------------------------

_∪_ : Ens → Ens → Ens
_∪_ x y = ∐ ⟨ x , y ⟩

∪>
 : ∀ {x y z}
 → ((z ∈ x) ∨ (z ∈ y)) from (z ∈ (x ∪ y))
∪> f
 = #> λ u
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

sub-sub-uni
 : ∀ {x y z}
 → x ⊆ z
 → y ⊆ z
 → (x ∪ y) ⊆ z
sub-sub-uni xsz ysz
 = λ u → ∪> (|> (xsz u) (ysz u))

not-uni-not
 : ∀ {x y z}
 → (z ∉ (x ∪ y))
 → (z ∉ x) ∧ (z ∉ y)
not-uni-not nzxuy
 = (λ zx → exf-imp (∪[] (inl zx)) nzxuy)
 * (λ zy → exf-imp (∪[] (inr zy)) nzxuy)

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
 → prj₁

inter-self
 : ∀ {x}
 → (x ∩ x) ≡ x
inter-self
 = ext λ z
 → prj₁
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

not-int-comm-not
 : ∀ {x y z}
 → (z ∉ (x ∩ y))
 → (z ∉ (y ∩ x))
not-int-comm-not nzxiy
 = *> λ zy zx
 → exf-imp (zx * zy) nzxiy

not-int-not-imp
 : ∀ {x y z}
 → (z ∉ (x ∩ y))
 → (z ∈ y)
 → (z ∉ x)
not-int-not-imp nzxiy zy
 = λ zx → exf-imp (zx * zy) nzxiy

{- TODO
not-int-not
 : ∀ {x y z}
 → (z ∉ (x ∩ y))
 → (z ∉ x) ∧ (z ∉ y)
not-int-not {x} {y} {z} nzxiy
 = ?
-}

--------------------------------------------------

_-_ : Ens → Ens → Ens
_-_ x y = ⟨ v ∈ x ∣ v ∉ y ⟩

dif-self-empty
 : ∀ {x}
 → (x - x) ≡ ∅
dif-self-empty
 = ext λ z
 → *> exf-imp
 * exfalso

dif-int-dif
 : ∀ {x y}
 → (x - (x ∩ y)) ≡ (x - y)
dif-int-dif
 = ext λ z
 → *> (λ zx f → zx * λ zy → f (zx * zy))
 * *> (λ zx f → zx * *> (const f))

int-dif-dif
 : ∀ {x y}
 → (x ∩ (x - y)) ≡ (x - y)
int-dif-dif
 = ext λ z
 → *> (λ zx → *> λ _ nzy → zx * nzy)
 * *> λ zx nzy → zx * zx * nzy

uni-dif-uni
 : ∀ {x y}
 → ((x - y) ∪ y) ≡ (x ∪ y)
uni-dif-uni {x} {y}
 = ext λ z
 → ∪> (|> (*> (flp (const (∪[] ∙ inl))))
          (∪[] ∙ inr))
 * ∪> (|> (∪[] ∙ (z ∈ y) ⁇ flp (const inr) ∷ λ nzy zx → inl (zx * nzy))
          (∪[] ∙ inr))

uni-dif-dif
 : ∀ {x y}
 → ((x ∪ y) - y) ≡ (x - y)
uni-dif-dif
 = ext λ z
 → *> (∪> (|> (λ zx nzy → zx * nzy) exf-imp))
 * *> λ zx nzy → ∪[] (inl zx) * nzy

dif-int-empty
 : ∀ {x y}
 → ((x - y) ∩ y) ≡ ∅
dif-int-empty
 = ext λ z
 → *> (*> (const (flp exf-imp)))
 * exfalso

dif-uni-uni-dif
 : ∀ {x y z}
 → (x - (y ∪ z)) ≡ ((x - y) ∩ (x - z))
dif-uni-uni-dif
 = ext λ u
 → *> (λ ux nyuz → (ux * not-uni-not nyuz ₁) * ux * (not-uni-not nyuz ₂))
 * *> (*> λ uz nuy → *> λ ux nuz → ux * ∪> (|> nuy nuz))

{- TODO
dif-int-uni-dif
 : ∀ {x y z}
 → (x - (y ∩ z)) ≡ ((x - y) ∪ (x - z))
dif-int-uni-dif
 = ext λ z
 → *> (λ zx nyuz → ∪[] (inl (zx * {!!})))
 * {!!}
-}

--------------------------------------------------

_▲_ : Ens → Ens → Ens
_▲_ x y = (x - y) ∪ (y - x)

sdif-empty
 : ∀ {x}
 → (x ▲ ∅) ≡ x
sdif-empty
 = ext λ z
 → ∪> (|> prj₁ (*> exfalso))
 * λ zx → ∪[] (inl (zx * triv))

sdif-comm
 : ∀ {x y}
 → (x ▲ y) ≡ (y ▲ x)
sdif-comm
 = ext λ z
 → ∪> (|> (*> λ zx nzy → ∪[] (inr (zx * nzy)))
          (*> λ zy nzx → ∪[] (inl (zy * nzx))))
 * ∪> (|> (*> λ zy nzx → ∪[] (inr (zy * nzx)))
          (*> λ zx nzy → ∪[] (inl (zx * nzy))))

--------------------------------------------------

power-self-in
 : ∀ {x}
 → x ∈ (𝒫 x)
power-self-in
 = λ _ → triv

power-empty-in
 : ∀ {x}
 → ∅ ∈ (𝒫 x)
power-empty-in
 = λ _ → exfalso

power-empty-singl
 : (𝒫 ∅) ≡ ⟨ ∅ ⟩
power-empty-singl
 = ext λ z
 → (λ emp → inl (empty-eq emp))
 * |> (λ { eq _ → triv })
      exfalso

--------------------------------------------------

[_,_] : Ens → Ens → Ens
[_,_] x y = ⟨ ⟨ x ⟩ , ⟨ x , y ⟩ ⟩

ope>
 : ∀ {x y u v}
 → ((x ≡ u) ∧ (y ≡ v)) from ([ x , y ] ≡ [ u , v ])
ope> f = pe>
   (|> (*> ((λ { eq → pe>
            (|> f (*> λ { eq yx → f (eq * yx) })) })
               ∙ singl-inj))
       (*> (flp ((*> (λ { eq eq → f })
               ∙ singl-pair-eq)
               ∙ eq-sym)
               ∙ singl-pair-eq)))

opair-eq-singl-singl
 : ∀ {x y}
 → x ≡ y
 → [ x , y ] ≡ ⟨ ⟨ x ⟩ ⟩
opair-eq-singl-singl {x} eq
 = eq-sym
 $ begin
   ⟨ ⟨ x ⟩ ⟩
   ≡⟨ singl-self-pair-eq ⟩
   ⟨ ⟨ x ⟩ , ⟨ x ⟩ ⟩
   ≡⟨ pair-eq eq singl-self-pair-eq ⟩
   ⟨ ⟨ x ⟩ , ⟨ x , x ⟩ ⟩
   ∎

--------------------------------------------------

S : Ens → Ens
S x = x · x

succ-eq-uni-singl
 : ∀ {x}
 → (S x) ≡ (x ∪ ⟨ x ⟩)
succ-eq-uni-singl
 = ext λ z
 → |> (λ { eq → ∪[] (inr (inl eq)) })
      (λ zx → ∪[] (inl zx))
 * ∪> (|> inr (|> inl exfalso))


