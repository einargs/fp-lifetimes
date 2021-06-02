{-# OPTIONS --sized-types #-}
module RefTy where

open import Function using (id; _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst; cong₂)
open import Size

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

infix 4 _∋*_
data _∋*_ : Ctx → Kind → Set where
  KZ : ∀ {Γ K} → Γ ,* K ∋* K
  -- deals with kinds
  KK : ∀ {Γ K K'} → Γ ∋* K → Γ ,* K' ∋* K
  -- deals with types
  KT : ∀ {Γ K} {A : Γ ⊢* Type*} → Γ ∋* K → Γ , A ∋* K

{-
-- weaken⊇ : ∀ {Φ Ψ K} → Φ ⊇ Ψ → Ψ ⊢* K → Φ ⊢* K
infix 4 _⊇_
data _⊇_ : Ctx → Ctx → Set
data _⊇_ where
  Empty : ∅ ⊇ ∅
  SkipK : ∀ {Φ Ψ K} → Φ ⊇ Ψ → Φ ,* K ⊇ Ψ
  SkipT : ∀ {Φ Ψ} {A : Φ ⊢* Type*} → Φ ⊇ Ψ → Φ , A ⊇ Ψ
  KeepK : ∀ {Φ Ψ K} → Φ ⊇ Ψ → Φ ,* K ⊇ Ψ ,* K
  KeepT : ∀ {Φ Ψ} {A : Ψ ⊢* Type*} (super : Φ ⊇ Ψ)
    → Φ , weaken⊇ super A ⊇ Ψ , A
-}

data TermVar : Ctx → Set where
  TVZ : ∀ {Γ} {A : Γ ⊢* Type*} → TermVar (Γ , A)
  TVK : ∀ {Γ K} → TermVar Γ → TermVar (Γ ,* K)
  TVT : ∀ {Γ} {A : Γ ⊢* Type*} → TermVar Γ → TermVar (Γ , A)

-- Okay, maybe I can get around having a term index in the type
-- by instead using unique barriers that are inserted into the
-- type-level context, which then correspond to a barrier introduced
-- by a term. Hmmmm. No, still a problem with tracking lifetimes.
--
-- Okay, I think I have to use regions/barriers; this isn't working.
--
-- IDEA: Maybe I can use HOAS to get around this? That's what you do
-- for dependently typed languages, so hopefully the same technique
-- would work here. No, PHOAS/HOAS is a way to avoid variables; I need
-- a way to... I dunno. I should ask on a server tomorrow.
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
  _⇒_ : Γ ⊢* Type* → Γ ⊢* Type* → Γ ⊢* Type*
  _·*_ : ∀ {J K} → Γ ⊢* K ⇒* J → Γ ⊢* K → Γ ⊢* J
  *λ : ∀ {J K} → Γ ,* K ⊢* J → Γ ⊢* K ⇒* J
  *∀ : ∀ {K} → Γ ,* K ⊢* Type* → Γ ⊢* Type*

-- I can still prove some properties about this substitution!
--
-- Oh! This is great! It easily solves my problem of combining
-- renaming/substitution functions for functions.
--
-- Actually, something I've realized about substitution functions
-- is that on the type level there's no substitution for term
-- variables, so combining substitution functions was never a
-- problem.
data WeakenBy : Ctx → Ctx → Set where
  -- the root; weaken by nothing
  WZ : ∀ {Γ} → WeakenBy Γ Γ
  -- introduce a type variable
  WK : ∀ {Φ Ψ K} → WeakenBy Φ Ψ → WeakenBy Φ (Ψ ,* K)
  -- introduce a term variable
  WT : ∀ {Φ Ψ} {A : Ψ ⊢* Type*} → WeakenBy Φ Ψ → WeakenBy Φ (Ψ , A)


-- Gives semantics for `WeakenBy` on type variables.
weaken* : ∀ {Φ Ψ K} → WeakenBy Φ Ψ → Φ ∋* K → Ψ ∋* K
weaken* WZ i = i
weaken* (WK wb) i = KK (weaken* wb i)
weaken* (WT wb) i = KT (weaken* wb i)

-- Gives semantics for `WeakenBy` on erased term variables.
weakenTV : ∀ {Φ Ψ} → WeakenBy Φ Ψ → TermVar Φ → TermVar Ψ
weakenTV WZ i = i
weakenTV (WK wb) i = TVK (weakenTV wb i)
weakenTV (WT wb) i = TVT (weakenTV wb i)

-- This can only substitute for type variables, but it can rename
-- weaken by term or type variables.
data Sub* : {_ : Size} → Ctx → Ctx → Set where
  Weaken* : ∀ {i Φ Ψ} → (wb : WeakenBy Φ Ψ) → Sub* {↑ i} Φ Ψ
  Extend* : ∀ {i Φ Ψ K} (A : Ψ ⊢* K) → (s : Sub* {i} Φ Ψ) → Sub* {↑ i} (Φ ,* K) Ψ
  Compose* : ∀ {i Φ Ψ Θ} → (s1 : Sub* {i} Φ Ψ) → (s2 : Sub* {i} Ψ Θ) → Sub* {↑ i} Φ Θ

idSub* : ∀ {Γ} → Sub* Γ Γ
idSub* = Weaken* WZ

lift* : ∀ {i Φ Ψ K} → Sub* {i} Φ Ψ → Sub* {↑ ↑ i} (Φ ,* K) (Ψ ,* K)
lift* {i} s = Extend* {↑ ↑ i} (*var KZ) (Compose* {↑ i} s (Weaken* {i} (WK WZ)))

applySubTV : ∀ {Φ Ψ} → Sub* Φ Ψ → TermVar Φ → TermVar Ψ
applySubTV (Weaken* wb) i = weakenTV wb i
applySubTV {Φ ,* K} {Ψ} (Extend* A s) (TVK i) = applySubTV s i
applySubTV (Compose* s1 s2) i = applySubTV s2 (applySubTV s1 i)

-- Gives semantics for defunctionalized `Sub`.
applySub* : ∀ {i Φ Ψ K} → Sub* {i} Φ Ψ → Φ ∋* K → Ψ ⊢* K
sub* : ∀ {i Φ Ψ} → Sub* {i} Φ Ψ → ∀ {K} → Φ ⊢* K → Ψ ⊢* K

applySub* (Weaken* wb) x = *var (weaken* wb x)
applySub* (Extend* A s) KZ = A
applySub* .{↑ i} (Extend* {i} A s) (KK x) = applySub* {i} s x
applySub* .{↑ i} (Compose* {i} s1 s2) x = sub* {i} s2 (applySub* {i} s1 x)

sub* s 𝔹 = 𝔹
sub* {i} s (*var x) = applySub* {i} s x
sub* s (*' x) = *' (applySubTV s x)
sub* s (*& A1 A2) = *& (sub* s A1) (sub* s A2)
sub* s (A1 ⇒ A2) = sub* s A1 ⇒ sub* s A2
sub* {i} s (A1 ·* A2) = (sub* {i} s A1) ·* sub* {i} s A2
sub* {i} s (*λ A) = *λ (sub* {↑ ↑ i} (lift* {i} s) A)
sub* {i} s (*∀ A) = *∀ (sub* {↑ ↑ i} (lift* {i} s) A)

{-
(let x : (Bool, Int) = (true, 0) in
  (#Λ (l : Life*).
    (#λ (x : &* l (Bool, Int)).
      case x of
        (true, i : &* l Int) → i + 1
        (false, i : &* l Int) → i - 1)) ·* (x) · (& x))
-}
{-
weakenK* : ∀ {Γ J K} → Γ ⊢* J → Γ ,* K ⊢* J
weakenT* : ∀ {Γ K} {A : Γ ⊢* Type*} → Γ ⊢* K → Γ , A ⊢* K

infix 4 _∋_
data _∋_ : ∀ (Γ : Ctx) → Γ ⊢* Type* → Set where
TZ : ∀ {Γ} {A : Γ ⊢* Type*} → Γ , A ∋ weakenT* A
TK : ∀ {Γ K} {A : Γ ⊢* Type*} → Γ ∋ A → Γ ,* K ∋ weakenK* A
TT : ∀ {Γ} {A : Γ ⊢* Type*} {B : Γ ⊢* Type*} → Γ ∋ A → Γ , B ∋ weakenT* A
-}
