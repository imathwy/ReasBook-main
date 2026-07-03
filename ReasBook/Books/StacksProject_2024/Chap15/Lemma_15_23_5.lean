import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

/-
Domain-style sampling:
- primary domain: duality and reflexivity of finite modules over a commutative domain;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.Dual.eval`,
  `Module.evalEquiv`,
  `Module.IsReflexive.to_isTorsionFree`,
  `Module.Finite.of_injective`,
  `Module.Finite.range`;
- best owner abstraction: the canonical owner is the reflexivity class `Module.IsReflexive`,
  with the evaluation map `Module.Dual.eval` supplying the intrinsic comparison to the double
  dual; finiteness of the source and of the quotient object is derived API from the ambient finite
  middle term together with the exact pair;
- source/core/bridge triage:
  - `source-facing`: this closure lemma for reflexive modules under kernels with torsion-free
    quotient;
  - `core/canonical`: `Module.IsReflexive`, `Module.Dual.eval`, `Module.IsTorsionFree`,
    `Module.Finite`;
  - `bridge/view`: the quotient seen here is the canonical submodule `LinearMap.range g`, not an
    auxiliary wrapper around the ambient codomain.

Primitive data are the exact pair `f, g`, the injectivity of `f`, the reflexivity of the middle
term, and the torsion-freeness of the actual quotient object `LinearMap.range g`. The finiteness
of `M` is derived from `Module.Finite.of_injective hf`, and the finiteness of `LinearMap.range g`
is derived from the canonical range instance on linear maps out of finite modules. Requiring the
ambient codomain `M''` or the source `M` themselves to be finite as primitive public assumptions is
therefore redundant.
-/

section

open Function Module

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} {M' : Type w} {M'' : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M'] [Module R M'] [Module.Finite R M']
variable [AddCommGroup M''] [Module R M'']

-- Proof sketch: replace `g` by the canonical surjection `M' → range g`, so the exact pair
-- becomes `0 → M → M' → range g → 0`. Dualize this short exact sequence to compare the
-- evaluation maps into the double duals. Reflexivity of `M'` identifies the middle vertical map
-- with an isomorphism, while torsion-freeness of `range g` makes the right evaluation map
-- injective by Lemma `15.23.2`. The remaining diagram chase shows the evaluation map for `M` is
-- bijective.
/-- Lemma 15.23.5: if `0 → M → M' → M''` is exact over a domain, `M'` is finite and
reflexive, and the quotient `M'/M` identified with `LinearMap.range g` is torsion free, then `M`
is reflexive. -/
theorem isReflexive_of_exact_of_isReflexive_of_isTorsionFree
    {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Function.Exact f g) (hf : Injective f)
    [IsReflexive R M'] [IsTorsionFree R (LinearMap.range g)] :
    IsReflexive R M := sorry

end
