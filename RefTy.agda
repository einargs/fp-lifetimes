module RefTy where

open import Function using (id; _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst; cong₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_) renaming (_,_ to <_,_>)
open import Relation.Nullary using (¬_)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (_∷_; List⁺; _⁺++⁺_)

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

infixr 6 _[_]⊸_
infixr 6 _[_]⇒_
infixl 6 _*∩_

infix 4 _⊢*_
data _⊢*_ Γ where
  -- Boolean type
  𝔹 : Γ ⊢* Type*
  -- Static lifetime; the identity of lifetimes over intersection.
  *'static : Γ ⊢* Life*
  -- Type variables.
  *var : ∀ {K} → Γ ∋* K → Γ ⊢* K
  -- lifetime of the given term variable
  *' : TermVar Γ → Γ ⊢* Life*
  -- Intersection of two lifetimes.
  _*∩_ : Γ ⊢* Life* → Γ ⊢* Life* → Γ ⊢* Life*
  -- reference to a variable of the given type.
  -- We don't combine `*'` with it because we need *var to
  -- also work.
  *& : Γ ⊢* Life* → Γ ⊢* Type* → Γ ⊢* Type*
  -- The type of single use functions.
  _[_]⊸_ : Γ ⊢* Type* → Γ ⊢* Life* → Γ ⊢* Type* → Γ ⊢* Type*
  -- The type of re-usable functions.
  _[_]⇒_ : Γ ⊢* Type* → Γ ⊢* Life* → Γ ⊢* Type* → Γ ⊢* Type*
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
ren* p *'static = *'static
ren* p (*var x) = *var (p x)
ren* p (*' x) = *' (p x)
ren* p (L1 *∩ L2) = ren* p L1 *∩ ren* p L2
ren* p (*& A1 A2) = *& (ren* p A1) (ren* p A2)
ren* p (A1 [ L ]⊸ A2) = ren* p A1 [ ren* p L ]⊸ ren* p A2
ren* p (A1 [ L ]⇒ A2) = ren* p A1 [ ren* p L ]⇒ ren* p A2
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
sub* s *'static = *'static
sub* s (*var i) = s {TypeVarTag _} i
sub* s (*' i) = *' (s {ErasedTermVarTag} i)
sub* s (L1 *∩ L2) = sub* s L1 *∩ sub* s L2
sub* s (*& A1 A2) = *& (sub* s A1) (sub* s A2)
sub* s (A1 [ L ]⊸ A2) = sub* s A1 [ sub* s L ]⊸ sub* s A2
sub* s (A1 [ L ]⇒ A2) = sub* s A1 [ sub* s L ]⇒ sub* s A2
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
  *∩≡β : {A A' B B' : Γ ⊢* Life*}
    → A ≡β A' → B ≡β B' → (A *∩ B) ≡β (A' *∩ B')
  *&≡β : {L L' : Γ ⊢* Life*} {A A' : Γ ⊢* Type*}
    → L ≡β L' → A ≡β A' → (*& L A) ≡β (*& L' A')
  ⊸≡β : {A A' B B' : Γ ⊢* Type*} {L L' : Γ ⊢* Life*}
    → A ≡β A' → B ≡β B' → L ≡β L' → (A [ L ]⇒ B) ≡β (A' [ L' ]⇒ B')
  ⇒≡β : {A A' B B' : Γ ⊢* Type*} {L L' : Γ ⊢* Life*}
    → A ≡β A' → B ≡β B' → L ≡β L' → (A [ L ]⇒ B) ≡β (A' [ L' ]⇒ B')
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
  drop-*'static : ∀ {Φ Ψ} {ss : Φ ⊇ Ψ} → RestrictType ss *'static *'static
  drop-*var : ∀ {Φ Ψ K} {ss : Φ ⊇ Ψ} {i i'} → RestrictVar ss i i'
    → RestrictType {Φ} {Ψ} {K} ss (*var i) (*var i')
  drop-*' : ∀ {Φ Ψ} {ss : Φ ⊇ Ψ} {i i'} → RestrictVar ss i i'
    → RestrictType ss (*' i) (*' i')
  drop-*& : ∀ {Φ Ψ} {ss : Φ ⊇ Ψ} {L L' A A'} → RestrictType ss L L'
    → RestrictType ss A A' → RestrictType ss (*& L A) (*& L' A')
  drop-*∩ : ∀ {Φ Ψ} {ss : Φ ⊇ Ψ} {L L' M M'} → RestrictType ss L L'
    → RestrictType ss M M' → RestrictType ss (L *∩ M) (L' *∩ M')
  drop-⊸ : ∀ {Φ Ψ} {ss : Φ ⊇ Ψ} {A A' B B' L L'} → RestrictType ss A A'
    → RestrictType ss L L' → RestrictType ss B B'
    → RestrictType ss (A [ L ]⊸ B) (A' [ L' ]⊸ B')
  drop-⇒ : ∀ {Φ Ψ} {ss : Φ ⊇ Ψ} {A A' B B' L L'} → RestrictType ss A A'
    → RestrictType ss L L' → RestrictType ss B B'
    → RestrictType ss (A [ L ]⇒ B) (A' [ L' ]⇒ B')
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
compT⊇ drop-*'static drop-*'static = drop-*'static
compT⊇ (drop-*var rv1) (drop-*var rv2) = drop-*var (compV⊇ rv1 rv2)
compT⊇ (drop-*' rv1) (drop-*' rv2) = drop-*' (compV⊇ rv1 rv2)
compT⊇ {Φ} {Ψ} {Θ} (drop-*& rt1 rt3) (drop-*& rt2 rt4) =
  drop-*& (compT⊇ rt1 rt2) (compT⊇ rt3 rt4)
compT⊇ (drop-*∩ rt1 rt3) (drop-*∩ rt2 rt4) =
  drop-*∩ (compT⊇ rt1 rt2) (compT⊇ rt3 rt4)
compT⊇ (drop-⊸ rt1 rt3 rt5) (drop-⊸ rt2 rt4 rt6) =
  drop-⊸ (compT⊇ rt1 rt2) (compT⊇ rt3 rt4) (compT⊇ rt5 rt6)
compT⊇ (drop-⇒ rt1 rt3 rt5) (drop-⇒ rt2 rt4 rt6) =
  drop-⇒ (compT⊇ rt1 rt2) (compT⊇ rt3 rt4) (compT⊇ rt5 rt6)
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
weaken⊇ ss *'static = *'static
weaken⊇ ss (*var x) = *var (weakenV⊇ ss x)
weaken⊇ ss (*' x) = *' (weakenV⊇ ss x)
weaken⊇ ss (*& A1 A2) = *& (weaken⊇ ss A1) (weaken⊇ ss A2)
weaken⊇ ss (L1 *∩ L2) = weaken⊇ ss L1 *∩ weaken⊇ ss L2
weaken⊇ ss (A1 [ L ]⊸ A2) = weaken⊇ ss A1 [ weaken⊇ ss L ]⊸ weaken⊇ ss A2
weaken⊇ ss (A1 [ L ]⇒ A2) = weaken⊇ ss A1 [ weaken⊇ ss L ]⇒ weaken⊇ ss A2
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

peelK⊇ : ∀ {Φ Ψ K} → Φ ,* K ⊇ Ψ ,* K → Φ ⊇ Ψ
peelK⊇ refl⊇ = refl⊇
peelK⊇ (keepK⊇ ss) = ss

-- Erase a consuming term variable.
use2tv : ∀ {Φ A Ψ} → Φ ∋ A ! Ψ → TermVar Φ
use2tv UZ = EZ
use2tv (UK u) = SK (use2tv u)
use2tv (UT u x) = ST (use2tv u)

data Droppable : ∀ {Φ} → TermVar Φ → Set where
  droppable : ∀ {Φ A Ψ} → (u : Φ ∋ A ! Ψ) → Droppable (use2tv u)

data RefdIn : ∀ {Φ K} → Φ ⊢* K → TermVar Φ → Set where
  refd-*' : ∀ {Φ tv} → RefdIn {Φ} (*' tv) tv
  refd-*&1 : ∀ {Φ tv L A} → RefdIn {Φ} L tv → RefdIn (*& L A) tv
  refd-*&2 : ∀ {Φ tv L A} → RefdIn {Φ} A tv → RefdIn (*& L A) tv
  -- We ignore references in return or argument of functions.
  refd-⊸ : ∀ {Φ tv A L B} → RefdIn {Φ} L tv → RefdIn (A [ L ]⊸ B) tv
  refd-⇒ : ∀ {Φ tv A L B} → RefdIn {Φ} L tv → RefdIn (A [ L ]⇒ B) tv
  refd-·*1 : ∀ {Φ tv J K} {A : Φ ⊢* J ⇒* K} {B : Φ ⊢* J}
    → RefdIn {Φ} A tv → RefdIn (A ·* B) tv
  refd-·*2 : ∀ {Φ tv J K} {A : Φ ⊢* J ⇒* K} {B : Φ ⊢* J}
    → RefdIn {Φ} B tv → RefdIn (A ·* B) tv
  refd-*λ : ∀ {Φ J K tv A} → RefdIn {Φ ,* J} {K} A (SK tv) → RefdIn (*λ A) tv
  refd-*∀ : ∀ {Φ K tv A} → RefdIn {Φ ,* K} A (SK tv) → RefdIn (*∀ A) tv

-- Referenced.
data Refd : ∀ {Φ A} → Φ ∋ A → TermVar Φ → Set where
  refd-TZ : ∀ {Φ} {A : Φ ⊢* Type*} {tv : TermVar (Φ , A)} → RefdIn (weakenT* A) tv
    → Refd (TZ {A = A}) tv
  refd-TK : ∀ {Φ A K i tv} → Refd {Φ} {A} i tv → Refd {A = weaken* A} (TK i) (SK {K = K} tv)
  refd-TT : ∀ {Φ A B i tv} → Refd {Φ} {A} i tv → Refd {A = weakenT* A} (TT i) (ST {A = B} tv)

-- Shows that a context is a prefix of another context.
data PreCtx : Ctx → Ctx → Set where
  pre-refl : ∀ {Φ} → PreCtx Φ Φ
  pre-dropK : ∀ {Φ Ψ} K → PreCtx Φ (Ψ ,* K) → PreCtx Φ Ψ
  pre-dropT : ∀ {Φ Ψ} A → PreCtx Φ (Ψ , A) → PreCtx Φ Ψ

pre∅ : ∀ Φ → PreCtx Φ ∅
pre∅ C = f C pre-refl
  where
  f : ∀ G → PreCtx C G → PreCtx C ∅
  f ∅ sc = sc
  f (G ,* K) sc = f G (pre-dropK K sc)
  f (G , A) sc = f G (pre-dropT A sc)

pre2tv : ∀ {Φ Ψ A} → PreCtx Φ (Ψ , A) → TermVar Φ
pre2tv {Φ} preCtx = f preCtx EZ
  where
  f : ∀ {G} → PreCtx Φ G → TermVar G → TermVar Φ
  f pre-refl i = i
  f (pre-dropK K pc) i = f pc (SK i)
  f (pre-dropT A pc) i = f pc (ST i)

-- Counts all referrers.
data Referrer (Φ : Ctx) (tv : TermVar Φ) : Set where
  referrer : ∀ {A} {i : Φ ∋ A} → Refd i tv → Referrer Φ tv

data MultCtx (Φ : Ctx) : (Ψ : Ctx) → {PreCtx Φ Ψ} → Set where
  ∅ : MultCtx Φ ∅ {pre∅ Φ}
  ConK : ∀ {K Ψ pc} → MultCtx Φ Ψ {pre-dropK K pc} → MultCtx Φ (Ψ ,* K) {pc}
  ConFree : ∀ {Ψ A pc} → MultCtx Φ Ψ {pre-dropT A pc}
    → Droppable (pre2tv pc) → MultCtx Φ (Ψ , A) {pc}
  ConRefd : ∀ {Ψ A pc} → MultCtx Φ Ψ {pre-dropT A pc}
    → List⁺ (Referrer Φ (pre2tv pc)) → MultCtx Φ (Ψ , A) {pc}

Ctx# : Ctx → Set
Ctx# Φ = MultCtx Φ Φ {pre-refl}

data IsUsed : Set where
  used : IsUsed
  unused : IsUsed
data RefCtx : Ctx → Set where
  ∅ : RefCtx ∅
  ConsK : ∀ {Γ} → RefCtx Γ → (K : Kind) → IsUsed → RefCtx (Γ ,* K)
  ConsT : ∀ {Γ} → RefCtx Γ → (A : Γ ⊢* Type*) → IsUsed → RefCtx (Γ , A)

addRef : ∀ {Φ tag} → RefCtx Φ → InCtx tag Φ → RefCtx Φ
addRef (ConsK Γ K u) (SK i) = ConsK (addRef Γ i) K u
addRef (ConsK Γ K u) KZ = ConsK Γ K used
addRef (ConsT Γ A u) EZ = ConsT Γ A used
addRef (ConsT Γ A u) (ST i) = ConsT (addRef Γ i) A u

noRefs : ∀ Φ → RefCtx Φ
noRefs ∅ = ∅
noRefs (G ,* K) = ConsK (noRefs G) K unused
noRefs (G , A) = ConsT (noRefs G) A unused

singleRef : ∀ {Φ tag} → InCtx tag Φ → RefCtx Φ
singleRef {Φ} i = addRef (noRefs Φ) i

use-or : IsUsed → IsUsed → IsUsed
use-or used used = used
use-or used unused = used
use-or unused used = used
use-or unused unused = unused

infixl 4 _∪_
_∪_ : ∀ {Φ} → RefCtx Φ → RefCtx Φ → RefCtx Φ
∅ ∪ ∅ = ∅
ConsK G1 K u1 ∪ ConsK G2 .K u2 = ConsK (G1 ∪ G2) K (use-or u1 u2)
ConsT G1 A u1 ∪ ConsT G2 .A u2 = ConsT (G1 ∪ G2) A (use-or u1 u2)

restrictRCK : ∀ {Φ K} → RefCtx (Φ ,* K) → RefCtx Φ
restrictRCK (ConsK G K u) = G

-- Convert a lifetime to a reference.
lt2ref : ∀ {Φ} → Φ ⊢* Life* → RefCtx Φ
lt2ref L = f L
  where
  f : ∀ {Φ K} → Φ ⊢* K → RefCtx Φ
  f {Φ} *'static = noRefs Φ
  f (*var x) = singleRef x
  f (*' x) = singleRef x
  f (L1 *∩ L2) = f L1 ∪ f L2
  f (A ·* B) = f A ∪ f B
  f (*λ A) = restrictRCK (f A)
  f {Φ} A = noRefs Φ

data RefOrUse {Φ} : Φ ⊢* Type* → Φ ⊢* Type* → Set where
  isRef : ∀ {L A} → RefOrUse A (*& L A)
  isUse : ∀ {A} → RefOrUse A A

data _⊢_!_ Φ : Φ ⊢* Type* → (Ψ : Ctx) → {Φ ⊇ Ψ} → Set
refIn : ∀ {Φ B A Ψ ss} → _⊢_!_ (Φ , B) A Ψ {ss} → RefCtx Φ

data _⊢_!_ Φ where
  -- boolean terms
  #true : _⊢_!_ Φ 𝔹 Φ {refl⊇}
  #false : _⊢_!_ Φ 𝔹 Φ {refl⊇}
  -- if then else (consumes)
  #if_then_else_ : ∀ {Ψ Θ ss1 ss2 A B} {ru : RefOrUse 𝔹 B}
    → _⊢_!_ Φ 𝔹 Ψ {ss1}
    → _⊢_!_ Ψ (weaken⊇ ss2 A) Θ {ss2}
    → _⊢_!_ Ψ (weaken⊇ ss2 A) Θ {ss2}
    → (let ss = comp⊇ ss1 ss2 in _⊢_!_ Φ (weaken⊇ ss A) Θ {ss})
  -- consume a term variable
  #use : ∀ {Ψ A} → (u : Φ ∋ A ! Ψ) → _⊢_!_ Φ A Ψ {conv⊇ u}
  -- Inspect a reference term variable without consuming it.
  #ref : ∀ {L A} → (r : Φ ∋ *& L A) → _⊢_!_ Φ (*& L A) Φ {refl⊇}
  -- drop a variable without doing anything with it before the term.
  -- TODO: I may want to add a drop clause for after a term. (I could
  -- mimic that with let in as well.)
  #drop : ∀ {Ψ Θ A B ss} → (u : Φ ∋ A ! Ψ) → _⊢_!_ Ψ B Θ {ss}
    → _⊢_!_ Φ (weaken⊇ (conv⊇ u) B) Θ {comp⊇ (conv⊇ u) ss}
  -- take a reference to a variable without consuming it.
  #& : ∀ {A} → (i : Φ ∋ A) → _⊢_!_ Φ (*& (*' (eraseTV i)) A) Φ {refl⊇}
  -- term lambda (one use)
  #λ : ∀ {Ψ A L B ss} → (t : _⊢_!_ (Φ , B) (weakenT* A) Ψ {skipT⊇ ss})
    → {refIn t ≡ lt2ref L} → _⊢_!_ Φ (B [ L ]⊸ A) Ψ {ss}
  -- term lambda (multiple use)
  #λr : ∀ {A L B} → (t : _⊢_!_ (Φ , B) (weakenT* A) Φ {skipT⊇ refl⊇})
    → {refIn t ≡ lt2ref L} → _⊢_!_ Φ (B [ L ]⇒ A) Φ {refl⊇}
  -- term app (consumes function)
  _·_ : ∀ {Ψ Θ A L ss1 ss2} {B : Ψ ⊢* Type*} → _⊢_!_ Φ (weaken⊇ ss1 B [ L ]⊸ A) Ψ {ss1}
    → _⊢_!_ Ψ B Θ {ss2} → _⊢_!_ Φ A Θ {comp⊇ ss1 ss2}
  -- term app (doesn't consume function)
  _·r_ : ∀ {Ψ Θ L A M B ss1 ss2} → _⊢_!_ Φ (*& L (weaken⊇ ss1 B [ M ]⇒ A)) Ψ {ss1}
    → _⊢_!_ Ψ B Θ {ss2} → _⊢_!_ Φ A Θ {comp⊇ ss1 ss2}
  -- type forall
  -- Note that `K`, since it's a type variable and thus can't be
  -- dropped from the context, needs to also occur in the output.
  Λ : ∀ {Ψ K A ss} → _⊢_!_ (Φ ,* K) A (Ψ ,* K) {ss}
    → _⊢_!_ Φ (*∀ A) Ψ {peelK⊇ ss}
  -- type application (forall)
  _·*_ : ∀ {Ψ K A ss} → _⊢_!_ Φ (*∀ A) Ψ {ss} → (B : Ψ ⊢* K)
    → _⊢_!_ Φ (A [ weaken⊇ ss B ]*) Ψ {ss}
  -- type conversion
  #cast : ∀ {Ψ A B ss} → A ≡β B → _⊢_!_ Φ A Ψ {ss} → _⊢_!_ Φ B Ψ {ss}

expandRC : ∀ {Φ Ψ} → Φ ⊇ Ψ → RefCtx Ψ → RefCtx Φ
expandRC refl⊇ G = G
expandRC (keepK⊇ ss) (ConsK G K u) = ConsK (expandRC ss G) K u
expandRC (skipT⊇ {A = A} ss) G = ConsT (expandRC ss G) A unused
expandRC (keepT⊇ {A = A} ss x) (ConsT G A' u) = ConsT (expandRC ss G) A u

refIn {Φ} {B} t = restrictRC (f t)
  where
  restrictRC : ∀ {Φ A} → RefCtx (Φ , A) → RefCtx Φ
  restrictRC (ConsT G A u) = G

  f : ∀ {Φ Ψ A ss} → _⊢_!_ Φ A Ψ {ss} → RefCtx Φ
  f {Φ} #true = noRefs Φ
  f {Φ} #false = noRefs Φ
  f (#if_then_else_ {ss1 = ss} {ru = ru} t1 t2 t3) = ? -- f t1 ∪ expandRC ss (f t2 ∪ f t3)
  f {A = *& L A} (#use u) = lt2ref L
  f {Φ} (#use u) = noRefs Φ
  f {A = *& L A} (#ref r) = lt2ref L
  f (#drop u t) = expandRC (conv⊇ u) (f t)
  f (#& i) = singleRef (eraseTV i)
  f (#λ t) = restrictRC (f t)
  f (#λr t) = restrictRC (f t)
  f (_·_ {ss1 = ss} t1 t2) = f t1 ∪ expandRC ss (f t2)
  f (_·r_ {ss1 = ss} t1 t2) = f t1 ∪ expandRC ss (f t2)
  f (Λ t) = restrictRCK (f t)
  f (t ·* B) = f t
  f (#cast x t) = f t

{-
problem : (∅ , 𝔹) ⊢ 𝔹 ! ∅
problem = gets2nd · (#drop UZ #true)
  where
  -- imagine if instead of dropping the reference this matched on
  -- or otherwise read the reference. In this case, imagine you clone
  -- the boolean to return it as the final result; you could return
  -- the closure and call it later when that boolean is out of scope.
  takesRef : (∅ , 𝔹) ⊢ ((*& (*' EZ) 𝔹) [ *'static ]⇒ (𝔹 [ *' EZ ]⊸ 𝔹)) ! (∅ , 𝔹)
  takesRef = (#λr (#λ
    (#if (#ref (UT UZ drop-𝔹)) then (#use UZ) else (#drop UZ #false)) {refl}) {refl})
  gets2nd : (∅ , 𝔹) ⊢ 𝔹 [ *' EZ ]⊸ 𝔹 ! (∅ , 𝔹)
  gets2nd = (#λ ((#& TZ) ·r (#drop UZ (#& TZ))) {refl}) · takesRef
  -}

{-
{-
infixl 4 _,^_
{-
I need a way to remove a reference, to say "this reference has gone out of scope."
-}
data RefCtx : Ctx → Set where
  ∅ : RefCtx ∅
  _,*_ : ∀ {Γ} → RefCtx Γ → (K : Kind) → RefCtx (Γ ,* K)
  -- Indicates it has not been used as a reference.
  _,_ : ∀ {Γ} → RefCtx Γ → (A : Γ ⊢* Type*) → RefCtx (Γ , A)
  -- indicates it has been used as a reference.
  _,^_ : ∀ {Γ} → RefCtx Γ → (A : Γ ⊢* Type*) → RefCtx (Γ , A)

addRef : ∀ {Φ} → RefCtx Φ → TermVar Φ → RefCtx Φ
addRef (Γ ,* K) (SK i) = addRef Γ i ,* K
addRef (Γ , A) EZ = Γ ,^ A
addRef (Γ , A) (ST i) = addRef Γ i , A
addRef (Γ ,^ A) EZ = Γ ,^ A
addRef (Γ ,^ A) (ST i) = addRef Γ i ,^ A

noRefs : ∀ Φ → RefCtx Φ
noRefs Φ = {!!}

-- Convert a lifetime to a reference.
lt2ref : ∀ {Φ} → Φ ⊢* Life* → RefCtx Φ
lt2ref L = {!!}

-- Convert a term variable to a reference.
tv2ref : ∀ {Φ A} → Φ ∋ A → RefCtx Φ
tv2ref i = {!!}

infixl 4 _∪_
_∪_ : ∀ {Φ} → RefCtx Φ → RefCtx Φ → RefCtx Φ
∅ ∪ ∅ = ∅
(Γ ,* K) ∪ (Δ ,* .K) = (Γ ∪ Δ) ,* K
(Γ , A) ∪ (Δ , .A) = (Γ ∪ Δ) , A
(Γ ,^ A) ∪ (Δ , .A) = (Γ ∪ Δ) ,^ A
(Γ , A) ∪ (Δ ,^ .A) = (Γ ∪ Δ) ,^ A
(Γ ,^ A) ∪ (Δ ,^ .A) = (Γ ∪ Δ) ,^ A

join : ∀ {Φ Ψ} (ss : Φ ⊇ Ψ) → RefCtx Φ → RefCtx Ψ → RefCtx Ψ
join ss rc1 rc2 = (strengthenRC ss rc1) ∪ rc2
  where
  strengthenRC : ∀ {C1 C2} → C1 ⊇ C2 → RefCtx C1 → RefCtx C2
  strengthenRC refl⊇ Γ = Γ
  strengthenRC (keepK⊇ ss) (Γ ,* K) = strengthenRC ss Γ ,* K
  strengthenRC (skipT⊇ ss) (Γ , _) = {!!}
  -- TODO: I need to integrate RefCtx into _⊇_, and possibly into the before
  -- and after contexts of a term, since references can go out of scope.
  strengthenRC (skipT⊇ ss) (Γ ,^ _) = {!!}
  strengthenRC (keepT⊇ ss x) (Γ , _) = {!!}
  strengthenRC (keepT⊇ ss x) (Γ ,^ _) = {!!}

peelKRef : ∀ {Φ K} → RefCtx (Φ ,* K) → RefCtx Φ
peelKRef rc = {!!}
-}
-- TODO: this approach might not work because it doesn't take into account that you
-- could use a reference in the middle of a function, then drop it. It wouldn't show
-- up, but would still cause problems. Maybe I need to just write a function that
-- counts references in a term inside a function?
data _⊢_!_ Φ : Φ ⊢* Type* → (Ψ : Ctx) → {Φ ⊇ Ψ} → {RefCtx Ψ} → Set where
  -- boolean terms
  #true : _⊢_!_ Φ 𝔹 Φ {refl⊇} {noRefs Φ}
  #false : _⊢_!_ Φ 𝔹 Φ {refl⊇} {noRefs Φ}
  -- if then else
  #if_then_else_ : ∀ {Ψ Θ ss1 ss2 A R1 R2 R3}
    → _⊢_!_ Φ 𝔹 Ψ {ss1} {R1}
    → _⊢_!_ Ψ (weaken⊇ ss2 A) Θ {ss2} {R2}
    → _⊢_!_ Ψ (weaken⊇ ss2 A) Θ {ss2} {R3}
    → (let ss = comp⊇ ss1 ss2 in _⊢_!_ Φ (weaken⊇ ss A) Θ {ss} {join ss2 R1 (R2 ∪ R3)})
  -- consume a term variable
  #use : ∀ {Ψ A} → (u : Φ ∋ A ! Ψ) → _⊢_!_ Φ A Ψ {conv⊇ u} {noRefs Ψ}
  -- Inspect a reference term variable without consuming it.
  #ref : ∀ {L A} → (r : Φ ∋ *& L A) → _⊢_!_ Φ (*& L A) Φ {refl⊇} {lt2ref L}
  -- drop a variable without doing anything with it before the term.
  -- TODO: I may want to add a drop clause for after a term. (I could
  -- mimic that with let in as well.)
  #drop : ∀ {Ψ Θ A B ss R} → (u : Φ ∋ A ! Ψ) → _⊢_!_ Ψ B Θ {ss} {R}
    → _⊢_!_ Φ (weaken⊇ (conv⊇ u) B) Θ {comp⊇ (conv⊇ u) ss} {R}
  -- take a reference to a variable without consuming it.
  #& : ∀ {A} → (i : Φ ∋ A) → _⊢_!_ Φ (*& (*' (eraseTV i)) A) Φ {refl⊇} {tv2ref i}
  -- term lambda (one use)
  #λ : ∀ {Ψ A B ss R} → _⊢_!_ (Φ , B) (weakenT* A) Ψ {skipT⊇ ss} {R} → _⊢_!_ Φ (B ⇒ A) Ψ {ss} {R}
  -- term lambda (multiple use)
  #λr : ∀ {A B R} → _⊢_!_ (Φ , B) (weakenT* A) Φ {skipT⊇ refl⊇} {R} → _⊢_!_ Φ (B r⇒ A) Φ {refl⊇} {R}
  -- term app (consumes function)
  _·_ : ∀ {Ψ Θ A ss1 ss2 R1 R2} {B : Ψ ⊢* Type*} → _⊢_!_ Φ (weaken⊇ ss1 B ⇒ A) Ψ {ss1} {R1}
    → _⊢_!_ Ψ B Θ {ss2} {R2} → _⊢_!_ Φ A Θ {comp⊇ ss1 ss2} {join ss2 R1 R2}
  -- term app (doesn't consume function)
  _·r_ : ∀ {Ψ Θ L A B ss1 ss2 R1 R2} → _⊢_!_ Φ (*& L (weaken⊇ ss1 B r⇒ A)) Ψ {ss1} {R1}
    → _⊢_!_ Ψ B Θ {ss2} {R2} → _⊢_!_ Φ A Θ {comp⊇ ss1 ss2} {join ss2 R1 R2}
  -- type forall
  -- Note that `K`, since it's a type variable and thus can't be
  -- dropped from the context, needs to also occur in the output.
  Λ : ∀ {Ψ K A ss R} → _⊢_!_ (Φ ,* K) A (Ψ ,* K) {ss} {R}
    → _⊢_!_ Φ (*∀ A) Ψ {peelK⊇ ss} {peelKRef R}
  -- type application (forall)
  _·*_ : ∀ {Ψ K A ss R} → _⊢_!_ Φ (*∀ A) Ψ {ss} {R} → (B : Ψ ⊢* K)
    → _⊢_!_ Φ (A [ weaken⊇ ss B ]*) Ψ {ss} {R}
  -- type conversion
  #cast : ∀ {Ψ A B ss R} → A ≡β B → _⊢_!_ Φ A Ψ {ss} {R} → _⊢_!_ Φ B Ψ {ss} {R}

-- Demonstration of the escape problem in this calculus:
problem : (∅ , 𝔹) ⊢ 𝔹 ! ∅
problem = gets2nd · (#drop UZ #true)
  where
  -- imagine if instead of dropping the reference this matched on
  -- or otherwise read the reference. In this case, imagine you clone
  -- the boolean to return it as the final result; you could return
  -- the closure and call it later when that boolean is out of scope.
  takesRef : (∅ , 𝔹) ⊢ ((*& (*' EZ) 𝔹) r⇒ (𝔹 ⇒ 𝔹)) ! (∅ , 𝔹)
  takesRef = (#λr (#λ (#drop (UT UZ drop-𝔹) (#use UZ))))
  gets2nd : (∅ , 𝔹) ⊢ 𝔹 ⇒ 𝔹 ! (∅ , 𝔹)
  gets2nd = (#λ ((#& TZ) ·r (#drop UZ (#& TZ)))) · takesRef

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
-}

{-
module CustomTactic where
open import Data.Unit
open import Reflection
open import Data.List
open import Data.Nat

infer⊇-tactic : Term → TC ⊤
infer⊇-tactic hole = do
rf ← (quoteTC refl⊇)
catchTC (unify hole rf) fallback
where
searchEnv : Type → List Type → ℕ → TC ⊤
searchEnv ty [] n = return tt
searchEnv ty (ty' ∷ xs) n = catchTC
(do
unify ty ty'
v ← unquoteTC (var n [])
unify hole v)
(searchEnv ty xs (n + 1))

extractTy : Arg Type → Type
extractTy (arg ai t) = t
fallback : TC ⊤
fallback = do
ty ← inferType hole
ctx ← getContext
let ctx' = map extractTy ctx
searchEnv ty ctx' 0
open CustomTactic
-}
