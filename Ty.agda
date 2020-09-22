module Ty where

open import Data.List using (List; _∷_; [])

data Kind : Set where
  Mono : Kind

infixl 5 _k%_

-- The context of a type is a context of kinds.
data TyCtxt : Set where
  k∅ : TyCtxt
  _k%_ : TyCtxt → Kind → TyCtxt

infixl 4 _<k>_

_<k>_ : TyCtxt → TyCtxt → TyCtxt
G <k> k∅ = G
G <k> (G' k% k) = (G <k> G') k% k

infix 4 _K∈_

data _K∈_ : Kind → TyCtxt → Set where
  KZ : ∀ {G k} → k K∈ G k% k
  KS : ∀ {G k k'} → k K∈ G → k K∈ G k% k'

data IncBy : TyCtxt → Set where
  IZ : IncBy k∅
  IS : ∀ {G k} → IncBy G → IncBy (G k% k)

data Ty : TyCtxt → Kind → Set where
  #tvar : ∀ {G k} → k K∈ G → Ty G k
  _⇒_ : ∀ {G} → Ty G Mono → Ty G Mono → Ty G Mono
  𝔹 : ∀ {G} → Ty G Mono
  #∀ : ∀ {G k} → (k' : Kind) → Ty (G k% k') k → Ty G k

data TySub : TyCtxt → TyCtxt → Set where
  Inc : ∀ {G Gadd} → IncBy Gadd → TySub G (G <k> Gadd)
  _#<_ : ∀ {G G' k} → Ty G' k → TySub G G' → TySub (G k% k) G'
  _#<>_ : ∀ {G1 G2 G3} → TySub G1 G2 → TySub G2 G3 → TySub G1 G3

nilSub : ∀ {G} → TySub G G
nilSub = Inc IZ

singleSub : ∀ {G k} → Ty G k → TySub (G k% k) G
singleSub t = t #< nilSub

lift : ∀ {G G' k} → TySub G G' → TySub (G k% k) (G' k% k)
lift s = #tvar KZ #< (s #<> Inc (IS IZ))

add : ∀ {G Gadd k} → IncBy Gadd → k K∈ G → k K∈ (G <k> Gadd)
add IZ i = i
add (IS xs) i = KS (add xs i)

private
  substTy : ∀ {G G' k} → TySub G G' → Ty G k → Ty G' k

  -- value of index x in the substitution s
  applySub : ∀ {G G' k} → TySub G G' → k K∈ G → Ty G' k

  substTy s 𝔹 = 𝔹
  substTy s (#tvar x) = applySub s x
  substTy s (#∀ k body) = #∀ k (substTy (lift s) body)
  substTy s (t1 ⇒ t2) = (substTy s t1) ⇒ (substTy s t2)

  applySub (Inc n) x = #tvar (add n x)
  applySub (k #< s) KZ = k
  applySub (k #< s) (KS x) = applySub s x
  applySub (s1 #<> s2) x = substTy s2 (applySub s1 x)
