module RefTy where

open import Function using (id; _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst; cong₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_) renaming (_,_ to <_,_>)

-- I think that I may have to merge the type contexts
-- and term contexts for a reference to depend on a term
-- variable.


data Kind : Set where
  -- the kind of types that directly classify terms.
  Type* : Kind
  -- A lifetime
  Life* : Kind
  _⇒*_ : Kind → Kind → Kind

data Ctx : Set
data _⊢*_ (Γ : Ctx) : Kind → Set

infixl 5 _,*_
infixl 5 _,_
data Ctx where
  ∅ : Ctx
  _,*_ : Ctx → Kind → Ctx
  _,_ : ∀ (Γ : Ctx) → Γ ⊢* Type* → Ctx

data CtxIndexTag : Set where
  TypeVarTag : Kind → CtxIndexTag
  ErasedTermVarTag : CtxIndexTag

data InCtx : CtxIndexTag → Ctx → Set where
  KZ : ∀ {Γ K} → InCtx (TypeVarTag K) (Γ ,* K)
  EZ : ∀ {Γ} {A : Γ ⊢* Type*} → InCtx ErasedTermVarTag (Γ , A)
  SK : ∀ {P Γ K} → InCtx P Γ → InCtx P (Γ ,* K)
  ST : ∀ {P Γ} {A : Γ ⊢* Type*} → InCtx P Γ → InCtx P (Γ , A)

infix 4 _∋*_
_∋*_ : Ctx → Kind → Set
Γ ∋* K = InCtx (TypeVarTag K) Γ

TermVar : Ctx → Set
TermVar = InCtx ErasedTermVarTag

infixr 6 _⇒_
infixr 6 _r⇒_

infix 4 _⊢*_
data _⊢*_ Γ where
  𝔹 : Γ ⊢* Type*
  *var : ∀ {K} → Γ ∋* K → Γ ⊢* K
  -- lifetime of the given term variable
  *' : TermVar Γ → Γ ⊢* Life*
  -- intersection of two lifetimes (may not be necessary?)
  -- *∩ : Γ ⊢* Life* → Γ ⊢* Life* → Γ ⊢* Life*
  -- reference to a variable of the given type.
  -- We don't combine `*'` with it because we need *var to
  -- also work.
  *& : Γ ⊢* Life* → Γ ⊢* Type* → Γ ⊢* Type*
  -- The type of single use functions.
  _⇒_ : Γ ⊢* Type* → Γ ⊢* Type* → Γ ⊢* Type*
  -- The type of re-usable functions.
  _r⇒_ : Γ ⊢* Type* → Γ ⊢* Type* → Γ ⊢* Type*
  _·*_ : ∀ {J K} → Γ ⊢* K ⇒* J → Γ ⊢* K → Γ ⊢* J
  *λ : ∀ {J K} → Γ ,* K ⊢* J → Γ ⊢* K ⇒* J
  *∀ : ∀ {K} → Γ ,* K ⊢* Type* → Γ ⊢* Type*

-- A renaming of type variables from one context to another.
Ren* : Ctx → Ctx → Set
Ren* Φ Ψ = ∀ {P} → InCtx P Φ → InCtx P Ψ

-- Lift a renaming over a newly introduced type variable.
lift* : ∀ {Φ Ψ} → Ren* Φ Ψ → ∀ {K} → Ren* (Φ ,* K) (Ψ ,* K)
lift* p KZ = KZ
lift* p (SK i) = SK (p i)

-- Renaming of type variables in types.
ren* : ∀ {Φ Ψ} → Ren* Φ Ψ → ∀ {K} → Φ ⊢* K → Ψ ⊢* K
ren* p 𝔹 = 𝔹
ren* p (*var x) = *var (p x)
ren* p (*' x) = *' (p x)
ren* p (*& A1 A2) = *& (ren* p A1) (ren* p A2)
ren* p (A1 ⇒ A2) = ren* p A1 ⇒ ren* p A2
ren* p (A1 r⇒ A2) = ren* p A1 r⇒ ren* p A2
ren* p (A1 ·* A2) = ren* p A1 ·* ren* p A2
ren* p (*λ A) = *λ (ren* (lift* p) A)
ren* p (*∀ A) = *∀ (ren* (lift* p) A)

weaken* : ∀ {Γ J K} → Γ ⊢* J → Γ ,* K ⊢* J
weaken* = ren* SK

Sub* : Ctx → Ctx → Set
Sub* Φ Ψ = ∀ {P : CtxIndexTag} → f P
  where
  f : CtxIndexTag → Set
  f (TypeVarTag K) = Φ ∋* K → Ψ ⊢* K
  f ErasedTermVarTag = TermVar Φ → TermVar Ψ

idSub* : ∀ {Γ} → Sub* Γ Γ
idSub* {Γ} {TypeVarTag K} i = *var i
idSub* {Γ} {ErasedTermVarTag} i = i

lifts* : ∀ {Φ Ψ} → Sub* Φ Ψ → ∀ {K} → Sub* (Φ ,* K) (Ψ ,* K)
lifts* {Φ} {Ψ} s {K} {TypeVarTag .(K)} KZ = *var KZ
lifts* {Φ} {Ψ} s {K} {TypeVarTag J} (SK i) = weaken* (s {TypeVarTag J} i)
lifts* {Φ} {Ψ} s {K} {ErasedTermVarTag} (SK i) = SK (s {ErasedTermVarTag} i)

sub* : ∀ {Φ Ψ} → Sub* Φ Ψ → ∀ {K} → Φ ⊢* K → Ψ ⊢* K
sub* s 𝔹 = 𝔹
sub* s (*var i) = s {TypeVarTag _} i
sub* s (*' i) = *' (s {ErasedTermVarTag} i)
sub* s (*& A1 A2) = *& (sub* s A1) (sub* s A2)
sub* s (A1 ⇒ A2) = sub* s A1 ⇒ sub* s A2
sub* s (A1 r⇒ A2) = sub* s A1 r⇒ sub* s A2
sub* s (A1 ·* A2) = sub* s A1 ·* sub* s A2
sub* s (*λ A) = *λ (sub* (lifts* s) A)
sub* s (*∀ A) = *∀ (sub* (lifts* s) A)

extend* : ∀ {Φ Ψ} → Sub* Φ Ψ → ∀ {K} → Ψ ⊢* K → Sub* (Φ ,* K) Ψ
extend* s {.J} A {TypeVarTag J} KZ = A
extend* s {K} A {TypeVarTag J} (SK i) = s {TypeVarTag J} i
extend* s {K} A {ErasedTermVarTag} (SK i) = s {ErasedTermVarTag} i

_[_]* : ∀ {Γ J K} → Γ ,* K ⊢* J → Γ ⊢* K → Γ ⊢* J
A [ B ]* = sub* (extend* idSub* B) A

weakenT* : ∀ {Γ K} {A : Γ ⊢* Type*} → Γ ⊢* K → Γ , A ⊢* K
weakenT* = ren* ST

-- Term variables that are also indexed by the type.
infix 4 _∋_
data _∋_ : ∀ (Γ : Ctx) → Γ ⊢* Type* → Set where
  TZ : ∀ {Γ} {A : Γ ⊢* Type*} → Γ , A ∋ weakenT* A
  TK : ∀ {Γ K} {A : Γ ⊢* Type*} → Γ ∋ A → Γ ,* K ∋ weaken* A
  TT : ∀ {Γ} {A : Γ ⊢* Type*} {B : Γ ⊢* Type*} → Γ ∋ A → Γ , B ∋ weakenT* A

-- Erase a typed term variable to an untyped term variable.
eraseTV : ∀ {Γ} {A : Γ ⊢* Type*} → Γ ∋ A → TermVar Γ
eraseTV TZ = EZ
eraseTV (TK i) = SK (eraseTV i)
eraseTV (TT i) = ST (eraseTV i)

-- type equality
-- https://github.com/input-output-hk/plutus-metatheory/blob/cb596a1eb697c083c4bdf2ade4d37bbd2c3cb0bc/Type/Equality.lagda#L34
infix 4 _≡β_

data _≡β_ {Γ} : ∀ {K} → Γ ⊢* K → Γ ⊢* K → Set where
  -- structural rules
  refl≡β : ∀ {K}
    → (A : Γ ⊢* K) → A ≡β A
  sym≡β : ∀ {K} {A B : Γ ⊢* K}
    → A ≡β B → B ≡β A
  trans≡β : ∀ {K} {A B C : Γ ⊢* K}
    → A ≡β B → B ≡β C → A ≡β C

  -- congruence rules
  *&≡β : {L L' : Γ ⊢* Life*} {A A' : Γ ⊢* Type*}
    → L ≡β L' → A ≡β A' → (*& L A) ≡β (*& L' A')
  ⇒≡β : {A A' B B' : Γ ⊢* Type*}
    → A ≡β A' → B ≡β B' → (A ⇒ B) ≡β (A' ⇒ B')
  r⇒≡β : {A A' B B' : Γ ⊢* Type*}
    → A ≡β A' → B ≡β B' → (A r⇒ B) ≡β (A' r⇒ B')
  ·*≡β : ∀ {K J} {A A' : Γ ⊢* K ⇒* J} {B B' : Γ ⊢* K}
    → A ≡β A' → B ≡β B' → (A ·* B) ≡β (A' ·* B')
  *λ≡β : ∀ {K J} {B B' : Γ ,* J ⊢* K}
    → B ≡β B' → *λ B ≡β *λ B'
  *∀≡β : ∀ {K} {B B' : Γ ,* K ⊢* Type*}
    → B ≡β B' → *∀ B ≡β *∀ B'

  -- computation rule
  β≡β : ∀ {K J} (B : Γ ,* J ⊢* K) (A : Γ ⊢* J) → (*λ B) ·* A ≡β B [ A ]*

-- Proof that one context is the superset (or the same as) of another.
infix 4 _⊇_
data _⊇_ : Ctx → Ctx → Set

-- A proof that the given type is still valid in `Ψ`.
data RestrictType : ∀ {Φ Ψ K} → Φ ⊇ Ψ → Φ ⊢* K → Ψ ⊢* K → Set

-- A proof that the variable is still present in `Ψ`.
data RestrictVar : ∀ {Φ Ψ tag} → Φ ⊇ Ψ → InCtx tag Φ → InCtx tag Ψ → Set

data _⊇_ where
  refl⊇ : ∀ {Γ} → Γ ⊇ Γ
  keepK⊇ : ∀ {Φ Ψ K} → Φ ⊇ Ψ → Φ ,* K ⊇ Ψ ,* K
  skipT⊇ : ∀ {Φ Ψ A} → Φ ⊇ Ψ → Φ , A ⊇ Ψ
  keepT⊇ : ∀ {Φ Ψ A A'} → (ss : Φ ⊇ Ψ) → RestrictType ss A A'
    → Φ , A ⊇ Ψ , A'

data RestrictType where
  drop-𝔹 : ∀ {Φ Ψ} {ss : Φ ⊇ Ψ} → RestrictType ss 𝔹 𝔹
  drop-*var : ∀ {Φ Ψ K} {ss : Φ ⊇ Ψ} {i i'} → RestrictVar ss i i'
    → RestrictType {Φ} {Ψ} {K} ss (*var i) (*var i')
  drop-*' : ∀ {Φ Ψ} {ss : Φ ⊇ Ψ} {i i'} → RestrictVar ss i i'
    → RestrictType ss (*' i) (*' i')
  drop-*& : ∀ {Φ Ψ} {ss : Φ ⊇ Ψ} {L L' A A'} → RestrictType ss L L'
    → RestrictType ss A A' → RestrictType ss (*& L A) (*& L' A')
  drop-⇒ : ∀ {Φ Ψ} {ss : Φ ⊇ Ψ} {A A' B B'} → RestrictType ss A A'
    → RestrictType ss B B' → RestrictType ss (A ⇒ B) (A' ⇒ B')
  drop-r⇒ : ∀ {Φ Ψ} {ss : Φ ⊇ Ψ} {A A' B B'} → RestrictType ss A A'
    → RestrictType ss B B' → RestrictType ss (A r⇒ B) (A' r⇒ B')
  drop-·* : ∀ {Φ Ψ J K} {ss : Φ ⊇ Ψ} {A : Φ ⊢* K ⇒* J} {A' : Ψ ⊢* K ⇒* J}
    {B : Φ ⊢* K} {B' : Ψ ⊢* K} → RestrictType ss A A'
    → RestrictType ss B B' → RestrictType ss (A ·* B) (A' ·* B')
  drop-*λ : ∀ {Φ Ψ K J} {ss : Φ ⊇ Ψ} {A A'} → RestrictType {K = J} (keepK⊇ {K = K} ss) A A'
    → RestrictType ss (*λ A) (*λ A')
  drop-*∀ : ∀ {Φ Ψ K} {ss : Φ ⊇ Ψ} {A A'} → RestrictType (keepK⊇ {K = K} ss) A A'
    → RestrictType ss (*∀ A) (*∀ A')

data RestrictVar where
  drop-KZ : ∀ {Φ Ψ K} {ss : Φ ⊇ Ψ} → RestrictVar (keepK⊇ {K = K} ss) KZ KZ
  drop-EZ : ∀ {Φ Ψ B B'} {ss : Φ ⊇ Ψ} (rt : RestrictType ss B B')
    → RestrictVar (keepT⊇ ss rt) EZ EZ
  drop-refl : ∀ {Γ tag} {i : InCtx tag Γ} → RestrictVar refl⊇ i i
  drop-keepK : ∀ {Φ Ψ tag K} {ss : Φ ⊇ Ψ} {i i'} → RestrictVar {tag = tag} ss i i'
    → RestrictVar (keepK⊇ {K = K} ss) (SK i) (SK i')
  drop-keepT : ∀ {Φ Ψ tag A A'} {ss : Φ ⊇ Ψ} {i i'} → RestrictVar {tag = tag} ss i i'
    → (rt : RestrictType ss A A') → RestrictVar (keepT⊇ ss rt) (ST {A = A} i) (ST {A = A'} i')

comp⊇ : ∀ {Φ Ψ Θ} → Φ ⊇ Ψ → Ψ ⊇ Θ → Φ ⊇ Θ
compT⊇ : ∀ {Φ Ψ Θ K A B C} {ss1 : Φ ⊇ Ψ} {ss2 : Ψ ⊇ Θ} → RestrictType {K = K} ss1 A B
  → RestrictType {K = K} ss2 B C → RestrictType {K = K} (comp⊇ ss1 ss2) A C
compV⊇ : ∀ {Φ Ψ Θ tag g h i} {ss1 : Φ ⊇ Ψ} {ss2 : Ψ ⊇ Θ}
  → RestrictVar {tag = tag} ss1 g h → RestrictVar ss2 h i
  → RestrictVar (comp⊇ ss1 ss2) g i

comp⊇ refl⊇ ss2 = ss2
comp⊇ (keepK⊇ ss1) refl⊇ = keepK⊇ ss1
comp⊇ (keepK⊇ ss1) (keepK⊇ ss2) = keepK⊇ (comp⊇ ss1 ss2)
comp⊇ (keepT⊇ ss1 x) (skipT⊇ ss2) = skipT⊇ (comp⊇ ss1 ss2)
comp⊇ {Φ , A} {Ψ , B} {Θ , C} (keepT⊇ ss1 rt1) (keepT⊇ ss2 rt2) =
  keepT⊇ (comp⊇ ss1 ss2) (compT⊇ rt1 rt2)
comp⊇ (keepT⊇ ss rt) refl⊇ = keepT⊇ ss rt
comp⊇ (skipT⊇ ss1) ss2 = skipT⊇ (comp⊇ ss1 ss2)

compT⊇ drop-𝔹 drop-𝔹 = drop-𝔹
compT⊇ (drop-*var rv1) (drop-*var rv2) = drop-*var (compV⊇ rv1 rv2)
compT⊇ (drop-*' rv1) (drop-*' rv2) = drop-*' (compV⊇ rv1 rv2)
compT⊇ {Φ} {Ψ} {Θ} (drop-*& rt1 rt3) (drop-*& rt2 rt4) =
  drop-*& (compT⊇ rt1 rt2) (compT⊇ rt3 rt4)
compT⊇ (drop-⇒ rt1 rt3) (drop-⇒ rt2 rt4) =
  drop-⇒ (compT⊇ rt1 rt2) (compT⊇ rt3 rt4)
compT⊇ (drop-r⇒ rt1 rt3) (drop-r⇒ rt2 rt4) =
  drop-r⇒ (compT⊇ rt1 rt2) (compT⊇ rt3 rt4)
compT⊇ (drop-·* rt1 rt3) (drop-·* rt2 rt4) =
  drop-·* (compT⊇ rt1 rt2) (compT⊇ rt3 rt4)
compT⊇ (drop-*λ rt1) (drop-*λ rt2) = drop-*λ (compT⊇ rt1 rt2)
compT⊇ (drop-*∀ rt1) (drop-*∀ rt2) = drop-*∀ (compT⊇ rt1 rt2)

compV⊇ drop-KZ drop-refl = drop-KZ
compV⊇ drop-KZ drop-KZ = drop-KZ
compV⊇ (drop-EZ rt1) (drop-EZ rt2) = drop-EZ (compT⊇ rt1 rt2)
compV⊇ (drop-EZ rt) drop-refl = drop-EZ rt
compV⊇ drop-refl rv2 = rv2
compV⊇ (drop-keepK rv) drop-refl = drop-keepK rv
compV⊇ (drop-keepK rv1) (drop-keepK rv2) =
  drop-keepK (compV⊇ rv1 rv2)
compV⊇ (drop-keepT rv rt) drop-refl = drop-keepT rv rt
compV⊇ (drop-keepT rv1 rt1) (drop-keepT rv2 rt2) =
  drop-keepT (compV⊇ rv1 rv2) (compT⊇ rt1 rt2)

weakenV⊇ : ∀ {Φ Ψ tag} → Φ ⊇ Ψ → InCtx tag Ψ → InCtx tag Φ
weakenV⊇ refl⊇ i = i
weakenV⊇ (keepK⊇ ss) KZ = KZ
weakenV⊇ (keepK⊇ ss) (SK i) = SK (weakenV⊇ ss i)
weakenV⊇ (skipT⊇ ss) i = ST (weakenV⊇ ss i)
weakenV⊇ (keepT⊇ ss x) EZ = EZ
weakenV⊇ (keepT⊇ ss rt) (ST i) = ST (weakenV⊇ ss i)

weaken⊇ : ∀ {Φ Ψ K} → Φ ⊇ Ψ → Ψ ⊢* K → Φ ⊢* K
weaken⊇ ss 𝔹 = 𝔹
weaken⊇ ss (*var x) = *var (weakenV⊇ ss x)
weaken⊇ ss (*' x) = *' (weakenV⊇ ss x)
weaken⊇ ss (*& A1 A2) = *& (weaken⊇ ss A1) (weaken⊇ ss A2)
weaken⊇ ss (A1 ⇒ A2) = weaken⊇ ss A1 ⇒ weaken⊇ ss A2
weaken⊇ ss (A1 r⇒ A2) = weaken⊇ ss A1 r⇒ weaken⊇ ss A2
weaken⊇ ss (A1 ·* A2) = weaken⊇ ss A1 ·* weaken⊇ ss A2
weaken⊇ ss (*λ A) = *λ (weaken⊇ (keepK⊇ ss) A)
weaken⊇ ss (*∀ A) = *∀ (weaken⊇ (keepK⊇ ss) A)

-- Consume a term variable in the left context so that it doesn't appear in the
-- right context.
data _∋_!_ : ∀ Γ → Γ ⊢* Type* → Ctx → Set
conv⊇ : ∀ {Φ Ψ A} → Φ ∋ A ! Ψ → Φ ⊇ Ψ

data _∋_!_ where
  UZ : ∀ {Γ A} → (Γ , A) ∋ weakenT* A ! Γ
  UK : ∀ {Φ K A Ψ} → Φ ∋ A ! Ψ → (Φ ,* K) ∋ weaken* A ! (Ψ ,* K)
  UT : ∀ {Φ A B Ψ B'} → (u : Φ ∋ A ! Ψ) → RestrictType (conv⊇ u) B B'
    → (Φ , B) ∋ weakenT* A ! (Ψ , B')

conv⊇ UZ = skipT⊇ refl⊇
conv⊇ (UK u) = keepK⊇ (conv⊇ u)
conv⊇ (UT u rt) = keepT⊇ (conv⊇ u) rt

infix 4 _∋r_
-- Inspect a reference term variable without consuming it.
data _∋r_ : ∀ Γ → Γ ⊢* Type* → Set where
  RZ : ∀ {Γ L A} → (Γ , *& L A) ∋r weakenT* (*& L A)
  RK : ∀ {Γ K A} → Γ ∋r A → (Γ ,* K) ∋r weaken* A
  RT : ∀ {Γ A B} → Γ ∋r A → (Γ , B) ∋r weakenT* A

peelK⊇ : ∀ {Φ Ψ K} → Φ ,* K ⊇ Ψ ,* K → Φ ⊇ Ψ
peelK⊇ refl⊇ = refl⊇
peelK⊇ (keepK⊇ ss) = ss

data _⊢_!_ Φ : Φ ⊢* Type* → (Ψ : Ctx) → {Φ ⊇ Ψ} → Set where
  -- boolean terms
  #true : _⊢_!_ Φ 𝔹 Φ {refl⊇}
  #false : _⊢_!_ Φ 𝔹 Φ {refl⊇}
  -- if then else
  #if_then_else_ : ∀ {Ψ Θ ss1 ss2 A}
    → _⊢_!_ Φ 𝔹 Ψ {ss1}
    → _⊢_!_ Ψ (weaken⊇ ss2 A) Θ {ss2}
    → _⊢_!_ Ψ (weaken⊇ ss2 A) Θ {ss2}
    → (let ss = comp⊇ ss1 ss2 in _⊢_!_ Φ (weaken⊇ ss A) Θ {ss})
  -- consume a term variable
  #use : ∀ {Ψ A} → (u : Φ ∋ A ! Ψ) → _⊢_!_ Φ A Ψ {conv⊇ u}
  -- Inspect a reference term variable without consuming it.
  #ref : ∀ {L A} → (r : Φ ∋r *& L A) → _⊢_!_ Φ (*& L A) Φ {refl⊇}
  -- drop a variable without doing anything with it.
  #drop : ∀ {Ψ Θ A B ss} → (u : Φ ∋ A ! Ψ) → _⊢_!_ Ψ B Θ {ss}
    → _⊢_!_ Φ (weaken⊇ (conv⊇ u) B) Θ {comp⊇ (conv⊇ u) ss}
  -- take a reference to a variable without consuming it.
  #& : ∀ {A} → (i : Φ ∋ A) → _⊢_!_ Φ (*& (*' (eraseTV i)) A) Φ {refl⊇}
  -- term lambda (one use)
  #λ : ∀ {Ψ A B ss} → _⊢_!_ (Φ , B) (weakenT* A) Ψ {skipT⊇ ss} → _⊢_!_ Φ (B ⇒ A) Ψ {ss}
  -- term lambda (multiple use)
  #λr : ∀ {A B} → _⊢_!_ (Φ , B) (weakenT* A) Φ {skipT⊇ refl⊇} → _⊢_!_ Φ (B r⇒ A) Φ {refl⊇}
  -- term app (consumes function)
  _·_ : ∀ {Ψ Θ A ss1 ss2} {B : Ψ ⊢* Type*} → _⊢_!_ Φ (weaken⊇ ss1 B ⇒ A) Ψ {ss1}
    → _⊢_!_ Ψ B Θ {ss2} → _⊢_!_ Φ A Θ {comp⊇ ss1 ss2}
  -- term app (doesn't consume function)
  _·r_ : ∀ {Ψ Θ L A B ss1 ss2} → _⊢_!_ Φ (*& L (weaken⊇ ss1 B r⇒ A)) Ψ {ss1}
    → _⊢_!_ Ψ B Θ {ss2} → _⊢_!_ Φ A Θ {comp⊇ ss1 ss2}
  -- type forall
  -- Note that `K`, since it's a type variable and thus can't be
  -- dropped from the context, needs to also occur in the output.
  -- TODO: figure out a better solution than this clumsy peelK⊇ hack.
  Λ : ∀ {Ψ K A ss} → _⊢_!_ (Φ ,* K) A (Ψ ,* K) {ss}
    → _⊢_!_ Φ (*∀ A) Ψ {peelK⊇ ss}
  -- type application (forall)
  _·*_ : ∀ {Ψ K A ss} → _⊢_!_ Φ (*∀ A) Ψ {ss} → (B : Ψ ⊢* K)
    → _⊢_!_ Φ (A [ weaken⊇ ss B ]*) Ψ {ss}
  -- type conversion
  #cast : ∀ {Ψ A B ss} → A ≡β B → _⊢_!_ Φ A Ψ {ss} → _⊢_!_ Φ B Ψ {ss}

andBool : ∅ ⊢ (𝔹 ⇒ (𝔹 ⇒ 𝔹)) ! ∅
andBool = #λ (#λ (#if (#use (UT UZ drop-𝔹)) then (#use UZ) else (#drop UZ #false)))

setBool : ∅ ⊢ (*∀ {K = Life*} (𝔹 r⇒ (*& (*var KZ) 𝔹 ⇒ 𝔹))) ! ∅
setBool = Λ
  (#λr
    (#λ
      (#drop UZ
        (#drop UZ
          (#true)))))

-- Needs type conversion rule.
test : (∅ , 𝔹) ⊢ ((*λ ((*& (*var KZ) 𝔹) ⇒ (*& (*var KZ) 𝔹))) ·* (*' EZ)) ! (∅ , 𝔹)
test = #cast conv (#λ (#use UZ))
  where
  left : ∅ , 𝔹 ⊢* Type*
  left = (*& (*' EZ) 𝔹) ⇒ (*& (*' EZ) 𝔹)
  right : ∅ , 𝔹 ⊢* Type*
  right = (*λ ((*& (*var KZ) 𝔹) ⇒ (*& (*var KZ) 𝔹))) ·* (*' EZ)
  conv : left ≡β right
  conv = sym≡β (β≡β
    ((*& (*var KZ) 𝔹) ⇒ (*& (*var KZ) 𝔹))
    (*' EZ))
