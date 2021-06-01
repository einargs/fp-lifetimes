# Proof of composition of renaming (`ren*-comp`)
## Definitions:
`Ctxt*` is a context of type variables with `Kind`s.

`Ren* Φ Ψ` is a function from an index in the context Φ to an index in
the context Ψ.

`lift* p` lifts a renaming `p : Ren* Φ Ψ` over a new type variable `t` of
kind `K`, returning a renaming `Ren* (Φ , t : K) (Ψ , t : K)`. (Since the
actual code doesn't use named variables, but instead de brujin indicies, the
actual return type is `Ren* (Φ ,* K) (Ψ ,* K)`.)

`Φ ∋* K` is an index of kind `K` in the context Φ.

`Φ ⊢* K` is a type of kind `K` in the context `Φ`.

`ren* p t` takes a renaming `Ren* Φ Ψ` and a type `Φ ⊢* K` and renames the
type variables in `t` so that it is in Ψ (i.e. turns it into `Ψ ⊢* K`).

## Proof:
The goal is to prove that, given two renamings `p : Ren* Φ Ψ` and
`p' : Ren* Ψ Θ`, renaming a type `a : Φ ⊢* J` by the composition of
p' and p (`p' ∘ p`) is the same as renaming by p and then renaming by
p': `ren* (p' ∘ p) a ≡ ren* p' (ren* p a)`.

To prove this we begin by induction on the shape of `a`.

### `*var` case (a type variable)
This is trivially true by the way `ren*` is defined on the `*var` case;
it simply directly applies the renaming to the index inside the `*var`.

### `𝔹` case (the boolean type)
This is trivially true, since `𝔹` has no type variables in it.

### `t1 ⇒ t2` case (a function type)
In this case, we apply the induction hypothesis to t1 and t2. Then,
via congruence, we know the equality holds true for `t1 ⇒ t2`.

### `t1 ·* t2` case (a type application)
In this case, we apply the induction hypothesis to t1 and t2. Then,
via congruence, we know the equality holds true for `t1 ·* t2`.

### `*λ t` case (a type level lambda)
`ren* p (*λ t)` is defined on the `*λ` as renaming the internal type t
by p lifted over the new type variable.
```
ren* p (*λ t) = *λ (ren* (lift* p) t)
```

Applying that to the goal, we now need to prove that renaming `t` by
the lifted composition of p' and p (`lift* (p' ∘ p)`) is the same as
renaming by the lifted p (`lift* p`) and then by the lifted p' (`lift* p'`).
```
*λ (ren* (lift* (p' ∘ p)) t) ≡ *λ (ren* (lift* p') (ren* (lift* p) t))
```

Congruence means we don't have to worry about the enclosing `*λ`; as long
as we can prove the internal types are equal, we're fine.
```
ren* (lift* (p' ∘ p)) t ≡ ren* (lift* p') (ren* (lift* p) t)
```

Our induction hypothesis is that renaming by the composition of a lifted
p' and lifted p (`lift* p' ∘ lift* p`) is the same as renaming by a lifted p
and then a lifted p'.
```
ren* (lift* p' ∘ lift* p) t ≡ ren* (lift* p') (ren* (lift* p) t)
```

The left side of our induction hypothesis is already correct, so we just need
an equality that shows that the lifted composition p' of p (`lift* (p' ∘ p)`)
is the same as the composition lifted p' of lifted p (`lift* p' ∘ lift* p`).
Once we have that equality, we can use a variant of the congruence principle
for `ren*` to show that if the renaming functions are equal extensionally
(i.e. they return the same output for all inputs) then renaming by them is
equal as well. (This is `ren*-cong` in the code.)
```
lift* (p' ∘ p) ≡ lift* p' ∘ lift* p
```

As it turns out, this is a principle we've already proven and called `lift*-comp`,
which is quite trivial to prove, not even requiring induction, only simple
discrimination on the case (since `lift*` doesn't recurse in its own definition).

### `*∀ t` case (a polymorphic type)
Proof is the same as for the `*λ` case.
