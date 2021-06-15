{- # OPTIONS --sized-types #-}
{- # OPTIONS --show-implicit #-}

module Ty where

open import Data.List using (List; _∷_; [])
open import Size
open import Function using (id; _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst; cong₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

data Kind : Set where
  Mono : Kind
  _⇒*_ : Kind → Kind → Kind

infixl 5 _,*_

-- The context of a type is a context of kinds.
data Ctx* : Set where
  ∅ : Ctx*
  _,*_ : Ctx* → Kind → Ctx*

infix 4 _∋*_

data _∋*_ : Ctx* → Kind → Set where
  KZ : ∀ {Φ k} → Φ ,* k ∋* k
  KS : ∀ {Φ k k'} → Φ ∋* k → Φ ,* k' ∋* k

infix 4 _⊢*_

data _⊢*_ Φ : Kind → Set where
  *var : ∀ {k} → Φ ∋* k → Φ ⊢* k
  _⇒_ : Φ ⊢* Mono → Φ ⊢* Mono → Φ ⊢* Mono
  𝔹 : Φ ⊢* Mono
  *λ : ∀ {k j} → Φ ,* k ⊢* j → Φ ⊢* k ⇒* j
  _·*_ : ∀ {k j} → Φ ⊢* k ⇒* j → Φ ⊢* k → Φ ⊢* j
  *∀ : ∀ {k} → Φ ,* k ⊢* Mono → Φ ⊢* Mono

-- A renaming of type variables from one context to another.
Ren* : Ctx* → Ctx* → Set
Ren* Φ Ψ = ∀ {k} → Φ ∋* k → Ψ ∋* k

-- Lift a renaming over a newly introduced type variable.
lift* : ∀ {Φ Ψ} → Ren* Φ Ψ → ∀ {k} → Ren* (Φ ,* k) (Ψ ,* k)
lift* p KZ = KZ
lift* p (KS x) = KS (p x)

-- Now we can define renaming on types.
ren* : ∀ {Φ Ψ} → Ren* Φ Ψ → ∀ {k} → Φ ⊢* k → Ψ ⊢* k
ren* p (*var x) = *var (p x)
ren* p 𝔹 = 𝔹
ren* p (*λ B) = *λ (ren* (lift* p) B)
ren* p (A ·* B) = ren* p A ·* ren* p B
ren* p (A ⇒ B) = ren* p A ⇒ ren* p B
ren* p (*∀ B) = *∀ (ren* (lift* p) B)

-- Weakening is a special case of renaming.
weaken* : ∀ {Φ k j} → Φ ⊢* k → Φ ,* j ⊢* k
weaken* = ren* KS

-- Substitution is a function from type variables to types.
Sub* : Ctx* → Ctx* → Set
Sub* Φ Ψ = ∀ {k} → Φ ∋* k → Ψ ⊢* k

-- lift a substitution over a binder.
lifts* : ∀ {Φ Ψ} → Sub* Φ Ψ → ∀ {k} → Sub* (Φ ,* k) (Ψ ,* k)
lifts* σ KZ = *var KZ
lifts* σ (KS x) = weaken* (σ x)

-- substitution on types.
sub* : ∀ {Φ Ψ} → Sub* Φ Ψ → ∀ {k} → Φ ⊢* k → Ψ ⊢* k
sub* σ (*var x) = σ x
sub* _ 𝔹 = 𝔹
sub* σ (A ·* B) = sub* σ A ·* sub* σ B
sub* σ (A ⇒ B) = sub* σ A ⇒ sub* σ B
sub* σ (*λ body) = *λ (sub* (lifts* σ) body)
sub* σ (*∀ body) = *∀ (sub* (lifts* σ) body)

extend* : ∀ {Φ Ψ} → Sub* Φ Ψ → ∀ {j} (A : Ψ ⊢* j) → Sub* (Φ ,* j) Ψ
extend* σ A KZ = A
extend* σ _ (KS x) = σ x

_[_]* : ∀ {Φ k j} → Φ ,* k ⊢* j → Φ ⊢* k → Φ ⊢* j
B [ A ]* = sub* (extend* *var A) B

-- laws
lift*-id : ∀ {Φ j k} (a : Φ ,* k ∋* j) → lift* id a ≡ a
lift*-id {Φ} {j} {.j} (KZ {Φ = .Φ} {k = .j}) = refl
lift*-id {Φ} {j} {k} (KS {Φ = .Φ} {k = .j} {k' = .k} a) = refl

lift*-comp : ∀ {Φ Ψ Θ} {p : Ren* Φ Ψ} {p' : Ren* Ψ Θ} {j k} (a : Φ ,* k ∋* j)
  → lift* (p' ∘ p) a ≡ lift* p' (lift* p a)
lift*-comp {Φ} {Ψ} {Θ} {p} {p'} {j} {.j} (KZ {Φ = .Φ} {k = .j}) = refl
lift*-comp {Φ} {Ψ} {Θ} {p} {p'} {j} {k} (KS {Φ = .Φ} {k = .j} {k' = .k} a) = refl

-- lemma for ren*-cong
lift*-cong : ∀ {Φ Ψ}
  → {f g : Ren* Φ Ψ}
  → (∀ {J} (x : Φ ∋* J) → f x ≡ g x)
  → ∀ {J K} (x : Φ ,* J ∋* K)
  → lift* f x ≡ lift* g x
lift*-cong p KZ = refl
lift*-cong p (KS x) = cong KS (p x)

-- lemma for ren*-id
ren*-cong : ∀ {Φ Ψ}
  → {f g : Ren* Φ Ψ}
  → (∀ {J} (x : Φ ∋* J) → f x ≡ g x)
  → ∀ {J} (x : Φ ⊢* J)
  → ren* f x ≡ ren* g x
ren*-cong p {J} (*var {k = .J} x) = cong *var (p x)
ren*-cong p {.Mono} (a ⇒ b) = cong₂ _⇒_ (ren*-cong p a) (ren*-cong p b)
ren*-cong p {.Mono} 𝔹 = refl
ren*-cong p {.(k ⇒* j)} (*λ {k = k} {j = j} t) = cong *λ (ren*-cong (lift*-cong p) t)
ren*-cong p {J} (_·*_ {k = k} {j = .J} a b) = cong₂ _·*_ (ren*-cong p a) (ren*-cong p b)
ren*-cong p {J} (*∀ t) = cong *∀ (ren*-cong (lift*-cong p) t)

ren*-id : ∀ {Φ J} (a : Φ ⊢* J) → ren* id a ≡ a
ren*-id {Φ} {J} (*var {k = .J} x) = refl
ren*-id {Φ} {.Mono} (a ⇒ b) = cong₂ _⇒_ (ren*-id a) (ren*-id b)
ren*-id {Φ} {.Mono} 𝔹 = refl
ren*-id {Φ} {.(k ⇒* j)} (*λ {k = k} {j = j} t) = cong *λ (trans (ren*-cong lift*-id t) (ren*-id t))
ren*-id {Φ} {J} (_·*_ {k = k} {j = .J} a b) = cong₂ _·*_ (ren*-id a) (ren*-id b)
ren*-id {Φ} {J} (*∀ t) = cong *∀ (trans (ren*-cong lift*-id t) (ren*-id t))

ren*-comp : ∀ {Φ Ψ Θ} {p : Ren* Φ Ψ} {p' : Ren* Ψ Θ} {J} (a : Φ ⊢* J)
  → ren* (p' ∘ p) a ≡ ren* p' (ren* p a)
-- roughly, ren* p' (ren* p (*var x)) ≡ (*var (p' (p x)))
-- and ren* (p' ∘ p) (*var x) ≡ (*var (p' (p x)))
ren*-comp {Φ} {Ψ} {Θ} {p} {p'} {J} (*var {k = .J} x) = refl
ren*-comp {Φ} {Ψ} {Θ} {p} {p'} {.Mono} (t1 ⇒ t2)
  rewrite ren*-comp {Φ} {Ψ} {Θ} {p} {p'} t1
  | ren*-comp {Φ} {Ψ} {Θ} {p} {p'} t2 = refl
ren*-comp {Φ} {Ψ} {Θ} {p} {p'} {.Mono} 𝔹 = refl
-- we recurse with `ren*-comp t`, which gives us
-- ren* (lift* p' ∘ lift* p) t ≡ ren* (lift* p') (ren* (lift* p) t)
-- we then use `ren*-cong lift*-comp t` to get
-- ren* (lift* (p' ∘ p)) t ≡ ren* (lift* p' ∘ lift* p) t
-- which combined with trans gives us what we need after we wrap it in `*λ`
-- using `cong`.
ren*-comp {Φ} {Ψ} {Θ} {p} {p'} {.(k ⇒* j)} (*λ {k = k} {j = j} t) =
  cong *λ (trans (ren*-cong lift*-comp t) (ren*-comp t))
-- Same principle as for `⇒`.
ren*-comp {Φ} {Ψ} {Θ} {p} {p'} {J} (_·*_ {k = k} {j = .J} t1 t2)
  rewrite ren*-comp {Φ} {Ψ} {Θ} {p} {p'} t1
  | ren*-comp {Φ} {Ψ} {Θ} {p} {p'} t2 = refl
-- same principle as for `*λ`.
ren*-comp {Φ} {Ψ} {Θ} {p} {p'} {J} (*∀ t) =
  cong *∀ (trans (ren*-cong lift*-comp t) (ren*-comp t))

lifts*-id : ∀ {Φ j k} (a : Φ ,* k ∋* j) → lifts* *var a ≡ *var a
lifts*-id KZ = refl
lifts*-id (KS x) = refl

lifts*-cong : ∀ {Φ Ψ}
  → {f g : Sub* Φ Ψ}
  → (∀ {J} (x : Φ ∋* J) → f x ≡ g x)
  → ∀ {J K} (x : Φ ,* K ∋* J)
  → lifts* f x ≡ lifts* g x
lifts*-cong p KZ = refl
lifts*-cong p (KS x) = cong weaken* (p x)

sub*-cong : ∀ {Φ Ψ}
  → {f g : Sub* Φ Ψ}
  → (∀ {J} (x : Φ ∋* J) → f x ≡ g x)
  → ∀ {J} (t : Φ ⊢* J)
  → sub* f t ≡ sub* g t
sub*-cong p (*var x) = p x
sub*-cong p (t1 ⇒ t2) rewrite sub*-cong p t1 | sub*-cong p t2 = refl
sub*-cong p 𝔹 = refl
sub*-cong p (*λ t) = cong *λ (sub*-cong (lifts*-cong p) t)
sub*-cong p (t1 ·* t2) rewrite sub*-cong p t1 | sub*-cong p t2 = refl
sub*-cong p (*∀ t) = cong *∀ (sub*-cong (lifts*-cong p) t)

sub*-id : ∀ {Φ J} (a : Φ ⊢* J) → sub* *var a ≡ a
sub*-id (*var x) = refl
sub*-id (t1 ⇒ t2) rewrite sub*-id t1 | sub*-id t2 = refl
sub*-id 𝔹 = refl
sub*-id (*λ t) = cong *λ (trans (sub*-cong lifts*-id t) (sub*-id t))
sub*-id (t1 ·* t2) rewrite sub*-id t1 | sub*-id t2 = refl
sub*-id (*∀ t) = cong *∀ (trans (sub*-cong lifts*-id t) (sub*-id t))

sub*-var : ∀ {Φ Ψ} {s : Sub* Φ Ψ} {J} (a : Φ ∋* J) → sub* s (*var a) ≡ s a
sub*-var t = refl

-- same as: lifts* (s ∘ p) ≡ lifts* s ∘ lift* p
lifts*-lift* : ∀ {Φ Ψ Θ} {p : Ren* Φ Ψ} {s : Sub* Ψ Θ} {J K} (x : Φ ,* K ∋* J)
  → lifts* (s ∘ p) x ≡ lifts* s (lift* p x)
lifts*-lift* KZ = refl
lifts*-lift* (KS x) = refl

sub*-ren* : ∀ {Φ Ψ Θ} {p : Ren* Φ Ψ} {s : Sub* Ψ Θ} {J} (t : Φ ⊢* J)
  → sub* (s ∘ p) t ≡ sub* s (ren* p t)
sub*-ren* (*var x) = refl
sub*-ren* (t1 ⇒ t2) = cong₂ _⇒_ (sub*-ren* t1) (sub*-ren* t2)
sub*-ren* 𝔹 = refl
{-
Goal:
sub* (lifts* (s ∘ p)) t ≡ sub* (lifts* s) (ren* (lift* p) t)

Via recursion:
rec : sub* (lifts* s ∘ lift* p) t ≡ sub* (lifts* s) (ren* (lift* p) t)
rec = sub*-ren* {p = lift* p} {s = lifts* s} t

so I need
lifts* s ∘ lift* p ≡ lifts* (s ∘ p)
-}
sub*-ren* {p = p} {s = s} (*λ t) = cong *λ (trans
  (sub*-cong lifts*-lift* t)
  (sub*-ren* {p = lift* p} {s = lifts* s} t))
sub*-ren* (t1 ·* t2) = cong₂ _·*_ (sub*-ren* t1) (sub*-ren* t2)
sub*-ren* {p = p} {s = s} (*∀ t) = cong *∀ (trans
  (sub*-cong lifts*-lift* t)
  (sub*-ren* {p = lift* p} {s = lifts* s} t))

-- same as: lifts* (ren* p ∘ s) ≡ ren* (lift* p) ∘ lifts* s
ren*-lift*-lifts* : ∀ {Φ Ψ Θ} {s : Sub* Φ Ψ} {p : Ren* Ψ Θ} {J K} (x : Φ ,* K ∋* J)
  → lifts* (ren* p ∘ s) x ≡ ren* (lift* p) (lifts* s x)
ren*-lift*-lifts* KZ = refl
{-
Goal
weaken* ((ren* p ∘ s) x) ≡ ren* (lift* p) (weaken* (s x))

change to
weaken* (ren* p (s x)) ≡ ren* (lift* p) (weaken* (s x))

relevant
weaken* = ren* KS

So:
ren* KS (ren* p (s x)) ≡ ren* (lift* p) (ren* KS (s x))

Then we apply ren*-comp twice to get
ren* (KS ∘ p) (s x) ≡ ren* (lift* p ∘ KS) (s x)

which is obvious from the definition of lift*
-}
ren*-lift*-lifts* {s = s} {p = p} (KS x) = trans
  (sym (ren*-comp (s x))) (ren*-comp (s x))

ren*-sub* : ∀ {Φ Ψ Θ} {s : Sub* Φ Ψ} {p : Ren* Ψ Θ} {J} (t : Φ ⊢* J)
  → sub* (ren* p ∘ s) t ≡ ren* p (sub* s t)
ren*-sub* (*var x) = refl
ren*-sub* (t1 ⇒ t2) = cong₂ _⇒_ (ren*-sub* t1) (ren*-sub* t2)
ren*-sub* 𝔹 = refl
{-
Goal:
sub* (lifts* (ren* p ∘ s)) t ≡ ren* (lift* p) (sub* (lifts* s) t)

Via recursion:
rec : sub* (ren* (lift* p) ∘ lifts* s) t ≡ ren* (lift* p) (sub* (lifts* s) t)
rec = ren*-sub* {s = lifts* s} {p = lift* p} t

I need
lifts* (ren* p ∘ s) ≡ ren* (lift* p) ∘ lifts* s
-}
ren*-sub* {s = s} {p = p} (*λ t) = cong *λ (trans
  (sub*-cong ren*-lift*-lifts* t)
  (ren*-sub* {s = lifts* s} {p = lift* p} t))
ren*-sub* (t1 ·* t2) = cong₂ _·*_ (ren*-sub* t1) (ren*-sub* t2)
ren*-sub* {s = s} {p = p} (*∀ t) = cong *∀ (trans
  (sub*-cong ren*-lift*-lifts* t)
  (ren*-sub* {s = lifts* s} {p = lift* p} t))

lifts*-comp : ∀ {Φ Ψ Θ} {s : Sub* Φ Ψ} {s' : Sub* Ψ Θ} {J K} (x : Φ ,* K ∋* J)
  → lifts* (sub* s' ∘ s) x ≡ sub* (lifts* s') (lifts* s x)
lifts*-comp KZ = refl
-- TODO: study how the below works
lifts*-comp {s = s} (KS x) = trans (sym (ren*-sub* (s x))) (sub*-ren* (s x))

sub*-comp : ∀ {Φ Ψ Θ} {s : Sub* Φ Ψ} {s' : Sub* Ψ Θ} {J} (a : Φ ⊢* J)
  → sub* (sub* s' ∘ s) a ≡ sub* s' (sub* s a)
sub*-comp (*var x) = refl
sub*-comp {Φ} {Ψ} {Θ} {s} {s'} (t1 ⇒ t2) = cong₂ _⇒_ (sub*-comp t1) (sub*-comp t2)
sub*-comp 𝔹 = refl
-- (all of this is inside cong *λ)
-- I need sub* (lifts* (sub* s' ∘ s)) t ≡ sub* (lifts* s') (sub* (lifts* s) t).
--   liftrec = sub*-comp {Φ ,* k} {Ψ ,* k} {Θ ,* k} {lifts* s} {lifts* s'} t
--   liftrec : sub* (sub* (lifts* s') ∘ lifts* s) t ≡ sub* (lifts* s') (sub* (lifts* s) t)
-- so I need `trans ?a liftrec` where
--   a : sub* (lifts* (sub* s' ∘ s)) t ≡ sub* (sub* (lifts* s') ∘ lifts* s) t
-- I can apply sub*-cong
--   a = sub*-cong ?b
--   b : lifts* (sub* s' ∘ s) ≡ sub* (lifts* s') ∘ lifts* s
-- `b` will be a separate proof, `sub*-lifts*-comp`
sub*-comp {s = s} {s' = s'} (*λ {k} t) = cong *λ (trans
  (sub*-cong lifts*-comp t)
  (sub*-comp {s = lifts* s} {s' = lifts* s'} t))
sub*-comp {Φ} {Ψ} {Θ} {s} {s'} (t1 ·* t2) = cong₂ _·*_ (sub*-comp t1) (sub*-comp t2)
sub*-comp {s = s} {s' = s'} (*∀ t) = cong *∀ (trans
  (sub*-cong lifts*-comp t)
  (sub*-comp {s = lifts* s} {s' = lifts* s'} t))

-- type equality
-- https://github.com/input-output-hk/plutus-metatheory/blob/cb596a1eb697c083c4bdf2ade4d37bbd2c3cb0bc/Type/Equality.lagda#L34

infix 4 _≡β_

data _≡β_ {Φ} : ∀ {K} → Φ ⊢* K → Φ ⊢* K → Set where
  -- structural rules
  refl≡β : ∀ {K}
    → (A : Φ ⊢* K) → A ≡β A
  sym≡β : ∀ {K} {A B : Φ ⊢* K}
    → A ≡β B → B ≡β A
  trans≡β : ∀ {K} {A B C : Φ ⊢* K}
    → A ≡β B → B ≡β C → A ≡β C

  -- congruence rules
  ⇒≡β : {A A' B B' : Φ ⊢* Mono}
    → A ≡β A' → B ≡β B' → (A ⇒ B) ≡β (A' ⇒ B')
  ·*≡β : ∀ {K J} {A A' : Φ ⊢* K ⇒* J} {B B' : Φ ⊢* K}
    → A ≡β A' → B ≡β B' → (A ·* B) ≡β (A' ·* B')
  *λ≡β : ∀ {K J} {B B' : Φ ,* J ⊢* K}
    → B ≡β B' → *λ B ≡β *λ B'
  *∀≡β : ∀ {K} {B B' : Φ ,* K ⊢* Mono}
    → B ≡β B' → *∀ B ≡β *∀ B'

  -- computation rule
  β≡β : ∀ {K J} (B : Φ ,* J ⊢* K) (A : Φ ⊢* J) → (*λ B) ·* A ≡β B [ A ]*

-- term context
infixl 5 _,_

data Ctx : Ctx* → Set where
  ∅ : Ctx ∅
  _,*_ : ∀ {Φ} → Ctx Φ → ∀ j → Ctx (Φ ,* j)
  _,_ : ∀ {Φ} → Ctx Φ → Φ ⊢* Mono → Ctx Φ

infix 4 _∋_

data _∋_ : ∀ {Φ} → Ctx Φ → Φ ⊢* Mono → Set where
  IZ : ∀ {Φ Γ} {A : Φ ⊢* Mono} → Γ , A ∋ A
  IS : ∀ {Φ Γ} {A : Φ ⊢* Mono} {B : Φ ⊢* Mono} → Γ ∋ A → Γ , B ∋ A
  IT : ∀ {Φ Γ} {A : Φ ⊢* Mono} {K} → Γ ∋ A → Γ ,* K ∋ weaken* A

-- terms
infix 4 _⊢_

data _⊢_ {Φ} Γ : Φ ⊢* Mono → Set where
  -- term variable
  #var : ∀ {A} → Γ ∋ A → Γ ⊢ A
  -- term lambda
  #λ : ∀ {A B} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
  -- term app
  _·_ : ∀ {A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  -- type lambda
  Λ : ∀ {K B} → Γ ,* K ⊢ B → Γ ⊢ *∀ B
  -- type app
  _·*_ : ∀ {K B} → Γ ⊢ *∀ B → (A : Φ ⊢* K) → Γ ⊢ B [ A ]*
  -- type cast
  conv : ∀ {A B} → A ≡β B → Γ ⊢ A → Γ ⊢ B

-- normal form.
-- Here we define a normal form that precludes a type-level
-- beta-redux.
data _⊢Nf*_ (Φ : Ctx*) : Kind → Set

-- A neutral type, which is either a type variable
-- or a type application that is stuck on a type variable
-- in the function position.
infix 4 _⊢Ne*_
data _⊢Ne*_ Φ K : Set where
  *var : Φ ∋* K → Φ ⊢Ne* K
  _·*_ : ∀ {J} → Φ ⊢Ne* (J ⇒* K) → Φ ⊢Nf* J → Φ ⊢Ne* K

infix 4 _⊢Nf*_
data _⊢Nf*_ Φ where
  *λ : ∀ {K J} → Φ ,* K ⊢Nf* J → Φ ⊢Nf* (K ⇒* J)
  ne : ∀ {K} → Φ ⊢Ne* K → Φ ⊢Nf* K
  _⇒_ : Φ ⊢Nf* Mono → Φ ⊢Nf* Mono → Φ ⊢Nf* Mono

  𝔹 : Φ ⊢Nf* Mono

renNe* : ∀ {Φ Ψ} → Ren* Φ Ψ → ∀ {K} → Φ ⊢Ne* K → Ψ ⊢Ne* K
renNf* : ∀ {Φ Ψ} → Ren* Φ Ψ → ∀ {K} → Φ ⊢Nf* K → Ψ ⊢Nf* K

renNe* p (*var x) = *var (p x)
renNe* p (A ·* B) = renNe* p A ·* renNf* p B

renNf* p (*λ B) = *λ (renNf* (lift* p) B)
renNf* p (ne x) = ne (renNe* p x)
renNf* p (A ⇒ B) = renNf* p A ⇒ renNf* p B
renNf* p (*∀ B) = *∀ (renNf* (lift* p) B)
renNf* p 𝔹 = 𝔹

weakenNf* : ∀ {Φ J K} → Φ ⊢Nf* J → Φ ,* K ⊢Nf* J
weakenNf* = renNf* KS

renNf*-cong : ∀ {Φ Ψ} {f g : Ren* Φ Ψ}
  → (∀ {J} (x : Φ ∋* J) → f x ≡ g x)
  → ∀ {J} (t : Φ ⊢Nf* J)
  → renNf* f t ≡ renNf* g t
renNe*-cong : ∀ {Φ Ψ} {f g : Ren* Φ Ψ}
  → (∀ {J} (x : Φ ∋* J) → f x ≡ g x)
  → ∀ {J} (t : Φ ⊢Ne* J)
  → renNe* f t ≡ renNe* g t

renNf*-cong p (*λ t) = cong *λ (renNf*-cong (lift*-cong p) t)
renNf*-cong p (ne t) = cong ne (renNe*-cong p t)
renNf*-cong p (t1 ⇒ t2) = cong₂ _⇒_ (renNf*-cong p t1) (renNf*-cong p t2)
renNf*-cong p (*∀ t) = cong *∀ (renNf*-cong (lift*-cong p) t)
renNf*-cong p 𝔹 = refl

renNe*-cong p (*var x) = cong *var (p x)
renNe*-cong p (t ·* x) = cong₂ _·*_ (renNe*-cong p t) (renNf*-cong p x)

renNf*-id : ∀ {Φ J} (t : Φ ⊢Nf* J) → renNf* id t ≡ t
renNe*-id : ∀ {Φ J} (t : Φ ⊢Ne* J) → renNe* id t ≡ t

renNf*-id (*λ t) = cong *λ (trans (renNf*-cong lift*-id t) (renNf*-id t))
renNf*-id (ne t) = cong ne (renNe*-id t)
renNf*-id (t1 ⇒ t2) = cong₂ _⇒_ (renNf*-id t1) (renNf*-id t2)
renNf*-id (*∀ t) = cong *∀ (trans (renNf*-cong lift*-id t) (renNf*-id t))
renNf*-id 𝔹 = refl

renNe*-id (*var x) = refl
renNe*-id (t ·* x) = cong₂ _·*_ (renNe*-id t) (renNf*-id x)

renNf*-comp : ∀ {Φ Ψ Θ} {p : Ren* Φ Ψ} {p' : Ren* Ψ Θ} {J}
  (t : Φ ⊢Nf* J) → renNf* (p' ∘ p) t ≡ renNf* p' (renNf* p t)
renNe*-comp : ∀ {Φ Ψ Θ} {p : Ren* Φ Ψ} {p' : Ren* Ψ Θ} {J}
  (t : Φ ⊢Ne* J) → renNe* (p' ∘ p) t ≡ renNe* p' (renNe* p t)

renNf*-comp {p = p} {p' = p'} (*λ t) = cong *λ (trans
  (renNf*-cong lift*-comp t)
  (renNf*-comp t))
renNf*-comp (ne x) = cong ne (renNe*-comp x)
renNf*-comp (t1 ⇒ t2) = cong₂ _⇒_ (renNf*-comp t1) (renNf*-comp t2)
renNf*-comp {p = p} {p' = p'} (*∀ t) = cong *∀ (trans
  (renNf*-cong lift*-comp t)
  (renNf*-comp t))
renNf*-comp 𝔹 = refl

renNe*-comp (*var x) = refl
renNe*-comp (t ·* x) = cong₂ _·*_ (renNe*-comp t) (renNf*-comp x)

-- This is my own attempt; it could utterly fail
-- OHHHH
-- I get it. You really do need the semantic type (or something similar;
-- it may not need to be a function) in order to pattern match on the
-- kind and return it. That's my current problem. Well, now that I understand
-- that, I can go use that method.
{-
nf*-app : ∀ {Φ} J K → Φ ⊢* K ⇒* J → Φ ⊢* K → (Φ ⊢Ne* J) ⊎ (Φ ⊢Nf* J)
nf* : ∀ {Φ} J → Φ ⊢* J → Φ ⊢Nf* J

nf* J (*var x) = ne (*var x)
nf* Mono (t1 ⇒ t2) = nf* Mono t1 ⇒ nf* Mono t2
nf* .Mono 𝔹 = 𝔹
nf* (K ⇒* J) (*λ t) = *λ (nf* J t)
nf* {Φ} J (_·*_ {K} {.J} t1 t2) with nf*-app J K t1 t2
... | inj₁ x = ne x
... | inj₂ t = t
nf* {Φ} .(Mono) (*∀ t) = *∀ (nf* Mono t)

nf*-app J K (*var x) t2 = inj₁ (*var x ·* nf* K t2)
nf*-app J K (*λ t1) t2 = inj₂ (nf* J (t1 [ t2 ]*))
nf*-app J K (t1 ·* t3) t2 = {!!}
-}
