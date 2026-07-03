import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open SSet.stdSimplex
open scoped Simplicial

universe u

/- Domain-style sampling for Lemma 14.11.3:
- primary domain: standard simplices and the simplicial Yoneda equivalence in `SSet`;
- sampled owner API:
  `SSet.stdSimplex`,
  `stdSimplex.objEquiv`,
  `SSet.yonedaEquiv`,
  `CategoryTheory.yonedaEquiv_apply`;
- best owner abstraction: the source-facing bijection is already the simplicial specialization
  `SSet.yonedaEquiv`, and its evaluation formula is the corresponding specialization of
  `CategoryTheory.yonedaEquiv_apply`;
- source/core/bridge triage:
  `source-facing`: the canonical bijection `(Δ[n] ⟶ U) ≃ U _⦋n⦌`;
  `core/canonical`: `SSet.yonedaEquiv`;
  `bridge/view`: the explicit evaluation formula at the identity simplex of `Δ[n]`.

Primitive data are only the simplicial set `U` and the standard simplex degree `n`. The identity
simplex of `Δ[n]` is derived from the owner presentation `stdSimplex.objEquiv`, and the
source’s evaluation description is derived API of `SSet.yonedaEquiv`. The file should therefore
keep `SSet.yonedaEquiv` as the main entry and expose only the thin evaluation bridge. -/

section

variable (U : SSet.{u}) (n : ℕ)

/- Lemma 14.11.3: for a simplicial set `U` and an integer `n ≥ 0`, there is a canonical bijection
`(Δ[n] ⟶ U) ≃ U _⦋n⦌`; this is exactly the simplicial Yoneda owner `SSet.yonedaEquiv`. -/
recall SSet.yonedaEquiv

variable (f : Δ[n] ⟶ U)

/- Companion check: the source’s evaluation description is not a second owner theorem; it is the
definitional simplicial specialization of `CategoryTheory.yonedaEquiv_apply`, evaluating `f` on
the identity simplex `objEquiv.symm (𝟙 ⦋n⦌)` of `Δ[n]`. -/
#check
  (show SSet.yonedaEquiv f =
      f.app (op ⦋n⦌) (objEquiv.symm (𝟙 ⦋n⦌)) from
    rfl)

end
