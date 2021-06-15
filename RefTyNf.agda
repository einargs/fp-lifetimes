open import RefTy

-- A context with only normal form types.
data CtxNf : Set

-- A normal form of the type that precludes type-level beta-redux.
data _⊢Nf*_ (Γ : CtxNf) : Kind → Set

infixl 5 _,*_
infixl 5 _,_
data CtxNf where
  ∅ : CtxNf
  _,*_ : CtxNf → Kind → CtxNf
  _,_ : ∀ (Γ : CtxNf) → Γ ⊢Nf* Type* → CtxNf

data CtxNfTag : Set where
  NfTypeVarTag : Kind → CtxNfTag
  NfErasedTermVarTag : CtxNfTag

data InCtxNf : CtxNfTag → CtxNf → Set where
  NKZ : ∀ {Γ K} → InCtxNf (NfTypeVarTag K) (Γ ,* K)
  NEZ : ∀ {Γ} {A : Γ ⊢Nf* Type*} → InCtxNf NfErasedTermVarTag (Γ , A)
  NSK : ∀ {P Γ K} → InCtxNf P Γ → InCtxNf P (Γ ,* K)
  NST : ∀ {P Γ} {A : Γ ⊢Nf* Type*} → InCtxNf P Γ → InCtxNf P (Γ , A)

infix 4 _∋Nf*_
_∋Nf*_ : CtxNf → Kind → Set
Γ ∋Nf* K = InCtxNf (NfTypeVarTag K) Γ

NfTermVar : CtxNf → Set
NfTermVar = InCtxNf NfErasedTermVarTag

-- A neutral type, which is either a type variable
-- or a type application that is stuck on a type variable
-- in the function position.
infix 4 _⊢Ne*_
data _⊢Ne*_ Γ K : Set where
  *var : Γ ∋Nf* K → Γ ⊢Ne* K
  _·*_ : ∀ {J} → Γ ⊢Ne* (J ⇒* K) → Γ ⊢Nf* J → Γ ⊢Ne* K

infixr 6 _⇒_
infixr 6 _r⇒_
infix 4 _⊢Nf*_
data _⊢Nf*_ Γ where
  *' : NfTermVar Γ → Γ ⊢Nf* Life*
  *& : Γ ⊢Nf* Life* → Γ ⊢Nf* Type* → Γ ⊢Nf* Type*
  _⇒_ : Γ ⊢Nf* Type* → Γ ⊢Nf* Type* → Γ ⊢Nf* Type*
  _r⇒_ : Γ ⊢Nf* Type* → Γ ⊢Nf* Type* → Γ ⊢Nf* Type*
  *λ : ∀ {K J} → Γ ,* K ⊢Nf* J → Γ ⊢Nf* (K ⇒* J)
  *∀ : ∀ {K} → Γ ,* K ⊢Nf* Type* → Γ ⊢Nf* Type*
  ne : ∀ {K} → Γ ⊢Ne* K → Γ ⊢Nf* K

RenNf* : CtxNf → CtxNf → 
