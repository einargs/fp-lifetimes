{-# OPTIONS --sized-types #-}
{-# OPTIONS --show-implicit #-}

module Ty where

open import Data.List using (List; _∷_; [])
open import Size
-- open import Agda.Builtin.Size

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

data Ty : {Size} → TyCtxt → Kind → Set where
  #tvar : ∀ {i G k} → k K∈ G → Ty {↑ i} G k
  _⇒_ : ∀ {i G} → Ty {i} G Mono → Ty {i} G Mono → Ty {↑ i} G Mono
  𝔹 : ∀ {i G} → Ty {i} G Mono
  #∀ : ∀ {i G k} → (k' : Kind) → Ty {i} (G k% k') k → Ty {↑ i} G k

data TySub : {Size} → {Size} → TyCtxt → TyCtxt → Set where
  Inc : ∀ {i ti G Gadd} → IncBy Gadd → TySub {↑ i} {ti} G (G <k> Gadd)
  _#<_ : ∀ {i ti G G' k}
    → Ty {ti} G' k
    → TySub {i} {ti} G G'
    → TySub {↑ i} {ti} (G k% k) G'
  _#<>_ : ∀ {i ti G1 G2 G3}
    → TySub {i} {ti} G1 G2
    → TySub {i} {ti} G2 G3
    → TySub {↑ i} {ti} G1 G3

nilSub : ∀ {G i ti} → TySub {↑ i} {ti} G G
nilSub = Inc IZ

singleSub : ∀ {G k i ti} → Ty {ti} G k → TySub {↑ ↑ i} {ti} (G k% k) G
singleSub t = t #< nilSub

lift : ∀ {G G' k i ti} → TySub {↑ i} {↑ ti} G G' → TySub {↑ ↑ ↑ i} {↑ ti} (G k% k) (G' k% k)
lift s = #tvar KZ #< (s #<> Inc (IS IZ))

add : ∀ {G Gadd k} → IncBy Gadd → k K∈ G → k K∈ (G <k> Gadd)
add IZ i = i
add (IS xs) i = KS (add xs i)

private
  substTy : ∀ {i} {si G G' k} → TySub {si} {↑ i} G G' → Ty {↑ i} G k → Ty {↑ i} G' k
  substTy s 𝔹 = 𝔹
  substTy s (#tvar x) = applySub s x where
    applySub : ∀ {i} {si G G' k} → TySub {↑ ↑ si} {↑ i} G G' → k K∈ G → Ty {↑ i} G' k
    applySub (Inc n) x = #tvar (add n x)
    applySub (k #< s) KZ = k
    applySub (k #< s) (KS x) = applySub s x
    applySub {i} (s1 #<> s2) x = substTy s2 (applySub s1 x)
  substTy {i} s (#∀ {i'} k body) = #∀ k {! substTy (lift s) body !}
  substTy s (t1 ⇒ t2) = {! (substTy s t1) ⇒ (substTy s t2) !}

