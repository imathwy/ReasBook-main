import Mathlib
import stacks_project.Chap10.Lemma_10_51_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

/-
Domain-style sampling:
- primary domain: commutative algebra, specifically Artin-Rees bounds and exactness of perturbed
  two-term complexes of modules;
- sampled declarations:
  `LinearMap.IsArtinReesBound`,
  `LinearMap.isArtinReesBound_of_preimage_pow_smul_eq`,
  `Ideal.exists_artin_rees_constant_of_exact`,
  `surjective_of_quotientMap_surjective_of_le_ring_jacobson`;
- core/canonical owners: `LinearMap.IsArtinReesBound` for the Artin-Rees clause and
  `Function.Exact` for the exactness clause;
- source-facing layer: the Stacks perturbation lemma for `L ⟶ M ⟶ N`;
- bridge/view layer: the Jacobson/Nakayama upgrade from an `I`-adic correction statement to the
  exactness of the perturbed complex.

Primitive data are the linear maps `f`, `f'`, `g`, `g'`, the owner-level Artin-Rees bounds,
the exactness relation `Function.Exact f g`, and congruence modulo `I ^ (c + 1)`. The perturbed
exactness conclusion is derived API built from those owners, so this file should stay owner-driven
rather than introducing a parallel local package.
-/

/- Source/core/bridge triage for Lemma 15.4.1:
- `source-facing`: the perturbation statements for an exact two-term complex `L ⟶ M ⟶ N`;
- `core/canonical`: `LinearMap.IsArtinReesBound` and `Function.Exact`;
- `bridge/view`: the congruence modulo `I ^ (c + 1)` together with the Jacobson-radical
  upgrade supplied by `surjective_of_quotientMap_surjective_of_le_ring_jacobson`.
-/

section

open scoped Pointwise
open LinearMap

variable {A : Type u} [CommRing A]
variable {L : Type v} [AddCommGroup L] [Module A L]
variable {M : Type w} [AddCommGroup M] [Module A M]
variable {N : Type x} [AddCommGroup N] [Module A N]
variable (I : Ideal A) {c : ℕ}
variable {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}

namespace LinearMap

-- Proof sketch: repeat the textbook adjustment argument. For `a ∈ M` with `g' a ∈ I^n N`, compare
-- `g a` and `g' a` modulo `I^(c+1)`, use the Artin-Rees bound for `g` to replace `a` by
-- `a - f b + f' b`, and use the Artin-Rees bound for `f` to ensure the correction term raises the
-- `I`-adic order by one. Iterating yields the required Artin-Rees bound for `g'`.
/-- Lemma 15.4.1 (1): if `c` is an Artin-Rees bound for `f` and `g`, the complex `L ⟶ M ⟶ N`
is exact, and `f'`, `g'` agree with `f`, `g` modulo `I^(c + 1)`, then `c` is also an
Artin-Rees bound for `g'`. -/
theorem IsArtinReesBound.of_exact_of_congr_mod_pow
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    g'.IsArtinReesBound I c := sorry

end LinearMap

section

variable [IsNoetherianRing A] [Module.Finite A M]

namespace Function.Exact

-- Proof sketch: first apply clause `(1)` to obtain the Artin-Rees bound for `g'`. Then for
-- `a ∈ ker g'`, the same adjustment argument shows `a ∈ LinearMap.range f' + I^(n-c) M` for every
-- `n ≥ c`. Intersect over all `n` and use Krull intersection for finite modules together with
-- `I ≤ Ring.jacobson A` to deduce `a ∈ LinearMap.range f'`.
/-- Lemma 15.4.1 (2): if `I` is contained in the Jacobson radical, `S' : L ⟶ M ⟶ N` is a
complex, and `f'`, `g'` agree with an exact complex `S : L ⟶ M ⟶ N` modulo `I^(c + 1)`, then
the perturbed complex `S'` is exact. -/
theorem of_congr_mod_pow_and_artin_rees
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (hI : I ≤ Ring.jacobson A) (hcomplex' : g'.comp f' = 0) :
    Exact f' g' := sorry

end Function.Exact

end

end
