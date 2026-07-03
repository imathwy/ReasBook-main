import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open scoped Simplicial

scoped[Simplicial] notation3 "C[" n "]" =>
  (coyoneda.obj (op ⦋n⦌) : CosimplicialObject (Type))

variable (n : ℕ)

/- Domain-style sampling for Example 14.5.6:
- primary domain: representable functors on `SimplexCategory`, viewed covariantly as cosimplicial
  sets;
- sampled owner API:
  `CategoryTheory.coyoneda.obj`,
  `CategoryTheory.coyonedaEquiv`,
  `CategoryTheory.coyonedaEquiv_apply`,
  `CategoryTheory.coyonedaEquiv_symm_app_apply`;
- source/core/bridge triage:
  `source-facing`: the Stacks notation `C[n]` for the covariant representable functor on `Δ`
  represented by `[n]`;
  `core/canonical`: `coyoneda.obj (op ⦋n⦌)`;
  `bridge/view`: evaluation in cosimplicial degree `k`, written canonically as `^⦋k⦌`, giving the
  hom-set `Hom([n], [k])`.

Primitive data are only the simplex `[n]`. The value at `[k]` is derived API from the canonical
owner `coyoneda.obj`, so any local alias or theorem shell around that evaluation should be deleted
rather than kept as a parallel public wrapper.
-/

/- Example 14.5.6: for each `n ≥ 0`, the cosimplicial set denoted `C[n]` is the covariant
representable functor on `SimplexCategory` represented by `[n]`, with canonical owner
`coyoneda.obj (op ⦋n⦌)`. The source-facing chapter surface uses the notation `C[n]`. -/
#check (C[n] : CosimplicialObject (Type))

variable (k : ℕ)

/- Companion check: evaluating the costandard simplex `C[n]` at `[k]` is definitionally the
hom-set `Hom([n], [k])` in `SimplexCategory`, so this should stay a direct check of the owner’s
evaluation formula rather than a second named theorem. -/
#check
  (rfl :
    (C[n] : CosimplicialObject (Type)) ^⦋k⦌ = (⦋n⦌ ⟶ ⦋k⦌))
