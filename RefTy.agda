module RefTy where

open import Function using (id; _∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst; cong₂)

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

weakenT* : ∀ {Γ K} {A : Γ ⊢* Type*} → Γ ⊢* K → Γ , A ⊢* K
weakenK* : ∀ {Γ J K} → Γ ⊢* J → Γ ,* K ⊢* J

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

infix 4 _∋_
data _∋_ : ∀ (Γ : Ctx) → Γ ⊢* Type* → Set where
  TZ : ∀ {Γ} {A : Γ ⊢* Type*} → Γ , A ∋ weakenT* A
  TK : ∀ {Γ K} {A : Γ ⊢* Type*} → Γ ∋ A → Γ ,* K ∋ weakenK* A
  TT : ∀ {Γ} {A : Γ ⊢* Type*} {B : Γ ⊢* Type*} → Γ ∋ A → Γ , B ∋ weakenT* A

-- Okay, maybe I can get around having a term index in the type
-- by instead using unique barriers that are inserted into the
-- type-level context, which then correspond to a barrier introduced
-- by a term. Hmmmm. No, still a problem with tracking lifetimes.
infix 4 _⊢*_
data _⊢*_ Γ where
  𝔹 : Γ ⊢* Type*
  *var : ∀ {K} → Γ ∋* K → Γ ⊢* K
  &* : (A : Γ ⊢* Type*) → Γ ∋ A → Γ ⊢* Life*
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

-- Gives semantics for `WeakenBy`
weakenBy* : ∀ {Φ Ψ K} → WeakenBy Φ Ψ → Φ ∋* K → Ψ ∋* K
weakenBy* WZ i = i
weakenBy* (WK wb) i = KK (weakenBy* wb i)
weakenBy* (WT wb) i = KT (weakenBy* wb i)

-- This can only substitute for type variables, but it can rename
-- weaken by term or type variables.
data Sub* : Ctx → Ctx → Set where
  Weaken* : ∀ {Φ Ψ} → (wb : WeakenBy Φ Ψ) → Sub* Φ Ψ
  Extend* : ∀ {Φ Ψ K} (A : Ψ ⊢* K) → (s : Sub* Φ Ψ) → Sub* (Φ ,* K) Ψ
  Compose* : ∀ {Φ Ψ Θ} → (s1 : Sub* Φ Ψ) → (s2 : Sub* Ψ Θ) → Sub* Φ Θ

idSub* : ∀ {Γ} → Sub* Γ Γ
idSub* = Weaken* WZ

lift* : ∀ {Φ Ψ K} → Sub* Φ Ψ → Sub* (Φ ,* K) (Ψ ,* K)
lift* s = Extend* (*var KZ) (Compose* s (Weaken* (WK WZ)))

-- Gives semantics for defunctionalized `Sub`.
applySub* : ∀ {Φ Ψ K} → Sub* Φ Ψ → Φ ∋* K → Ψ ⊢* K
sub* : ∀ {Φ Ψ} → Sub* Φ Ψ → ∀ {K} → Φ ⊢* K → Ψ ⊢* K

-- weakenK* : ∀ {Γ J K} → Γ ⊢* J → Γ ,* K ⊢* J
weakenK* A = sub* (Weaken* (WK WZ)) A

-- weakenT* : ∀ {Γ K} {A : Γ ⊢* Type*} → Γ ⊢* K → Γ , A ⊢* K
weakenT* B = sub* (Weaken* (WT WZ)) B

{-
weakenBy : ∀ {Φ Ψ} {A : Φ ⊢* Type*} (wb : WeakenBy Φ Ψ)
  → Φ ∋ A → Ψ ∋ (sub* (Weaken* wb) A)

-- Rename term variables/indices according to a type level substitution.
renTerm* : ∀ {Φ Ψ} {A : Φ ⊢* Type*} (s : Sub* Φ Ψ) → Φ ∋ A → Ψ ∋ (sub* s A)

renTerm* (Weaken* wb) i = weakenBy wb i
renTerm* (Extend* A s) i = {!!}
renTerm* {Φ} {Ψ} (Compose* {.(Φ)} {Γ} {.(Ψ)} s1 s2) i = {!!}

weakenBy {A = A} WZ i rewrite sub*-weakenId A = i
weakenBy {A = A} (WK wb) i = {!!} -- TK (weakenBy wb i)
weakenBy {A = A} (WT wb) i = {!!} -- TT (weakenBy wb i)
-}

applySub* (Weaken* wb) i = *var (weakenBy* wb i)
applySub* (Extend* A s) KZ = A
applySub* (Extend* A s) (KK i) = applySub* s i
applySub* (Compose* s1 s2) i = sub* s2 (applySub* s1 i)

sub* s 𝔹 = 𝔹
sub* s (*var x) = applySub* s x
-- yes! The answer to the recursion knot falls out here!
sub* {Φ} {Ψ} s (&* A i) = &* A' (f A s i)
  where
  A' = sub* s A
  {-
  mkPrf : ∀ (C1 C2 : Ctx) (wb : WeakenBy C1 C2) (C : C1 ⊢* Type*)
    → (C2 ∋ sub* (Weaken* wb) (weakenT* C)) ≡ (let C' = sub* (Weaken* wb) C in C2 , C' ∋ weakenT* C')
  mkPrf C2 wb C = ?
  -}
  g : ∀ C1 C2 (B : C1 ⊢* Type*) (wb : WeakenBy C1 C2) → C1 ∋ B → C2 ∋ sub* (Weaken* wb) B
  g (C1' , C) C2 .(sub* (Weaken* (WT WZ)) C) wb TZ = {!!}
  g (C1' , C) C2 .(sub* (Weaken* (WT WZ)) C) wb (TT i) = {!!}
  f : ∀ {C1 C2} (B : C1 ⊢* Type*) (σ : Sub* C1 C2) → C1 ∋ B → C2 ∋ sub* σ B
  f {C1' , C} {C2} .(sub* (Weaken* (WT WZ)) C) (Weaken* wb) TZ = {!!} --rewrite mkPrf C1 C2 wb C = TZ
  f {C1' , C} {C2} .(sub* (Weaken* (WT WZ)) C) (Compose* σ σ₁) TZ = {!!}
  f {C1} {C2} B σ (TK i) = {!!}
  f {C1} {C2} B σ (TT i) = {!!}
  {-
  f B (Weaken* wb) i = {!!}
  f {C1 ,* K} {C2} B (Extend* C σ) i = f B' σ i
    where
    B' : C2 ⊢* Type*
    B' = sub* (Extend* C σ) B
  f B (Compose* s1 s2) i = {!!} -}
sub* s (t1 ⇒ t2) = {!!}
sub* s (t1 ·* t2) = {!!}
sub* s (*λ t) = {!!}
sub* s (*∀ t) = {!!}

{-
weakenK*-unfold : ∀ {Γ K} (A : Γ ⊢* K) → sub* (Weaken* (WK WZ)) A ≡ weakenK* A
weakenK*-unfold A = {!!}

weakenT*-unfold : ∀ {Γ K} (A : Γ ⊢* K) → sub* (Weaken* (WT WZ)) A ≡ weakenT* A
weakenT*-unfold A = {!!}

sub*-weakenId : ∀ {Φ} (A : Φ ⊢* Type*) → sub* (Weaken* WZ) A ≡ A
sub*-weakenId A = {!!}
-}

-- I need to figure out a way to have the rename function also
-- rename term variables. Maybe...
--
-- frankly, I don't think I can do this with a renaming function.
-- I'll ask on a server after I've gotten some sleep.
{-
data level : Set where
  TypeLevel : level
  KindLevel : level

Ren* : Ctx → Ctx → Set
Ren* Φ Ψ = ∀ {K} → Φ ∋* K → Ψ ∋* K

Ren : Ctx → Ctx → Set
Ren Φ Ψ = ∀ {A : Φ ⊢* Type*} → Φ ∋ A → 

postulate
  ren* : ∀ {Φ Ψ} → Ren* Φ Ψ → ∀ {K} → Φ ⊢* K → Ψ ⊢* K
-}

{-
lift* : ∀ {Φ Ψ} → Ren* Φ Ψ → ∀ {K} → Ren* (Φ ,* K) (Ψ ,* K)
lift* p KZ = KZ
lift* p (KK x) = KK (p x)

ren*-& : ∀ {Φ Ψ} → Ren* Φ Ψ → ∀ {A : Φ ⊢* Type*} → 

ren* : ∀ {Φ Ψ} → Ren* Φ Ψ → ∀ {K} → Φ ⊢* K → Ψ ⊢* K
ren* p 𝔹 = 𝔹
ren* p (*var x) = *var (p x)
ren* p (&* l) = &* (pretty l)

-- weakenT* : ∀ {Γ K} {A : Γ ⊢* Type*} → Γ ⊢* K → Γ , A ⊢* K
-- weaken*K : ∀ {Γ J K} → Γ ⊢* J → Γ , K ⊢* J
-}

{-
infix 4 _⊢*_
data _⊢*_ (Φ : Ctx) : Kind → Set where
  *var : ∀ {K} → Φ ∋* K → Φ ⊢* K
  &* : Φ ∋* Type* → Φ ⊢* Life*
-}

{-
(let x : (Bool, Int) = (true, 0) in
  (#Λ (l : Life*).
    (#λ (x : &* l (Bool, Int)).
      case x of
        (true, i : &* l Int) → i + 1
        (false, i : &* l Int) → i - 1)) ·* (x) · (& x))
-}
