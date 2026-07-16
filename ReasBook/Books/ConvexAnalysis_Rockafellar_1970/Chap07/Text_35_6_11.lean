import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_3

noncomputable section

open Function
open scoped Rockafellar Topology

universe u v w

namespace Bifunction

section

variable {𝕜 : Type w}
variable [Field 𝕜] [LinearOrder 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [T2Space (WithTopBot 𝕜)]
variable [SupSet (WithTopBot 𝕜)]
variable [Filter.NeBot (𝓝[>] (0 : 𝕜))]
variable {U : Type u} {V : Type v}
variable [AddCommMonoid U] [SMulZeroClass 𝕜 U]
variable [AddCommGroup V] [Module 𝕜 V]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.11 identifies the second partial directional derivative
  `K'(u, v; 0, v')` with the support function of the second partial subdifferential
  `∂₂ K(u, v)`.
- `core/canonical`: the owner formula already lives upstream as the one-variable Chapter 23
  theorem for the second slice `K u`, namely
  `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt`.
- `bridge/view`: this file contributes only the uncurried partial-derivative bridge via
  `Function.directionalDerivativeAt_uncurry_second_eq` and the chapter bridge
  `Bifunction.subdifferential2At`.

Primary mathematical domain:
- convex analysis of concave-convex saddle bifunctions and their second partial subdifferentials.

Domain-style sampling used here:
- `Function.directionalDerivativeAt` from `Chap05.Lemma_23_0_1`;
- `Function.directionalDerivativeAt_uncurry_second_eq` from `Chap07.Text_35_5_3` as the slice
  bridge behind the displayed source notation;
- `Bifunction.subdifferential2At` from `Chap07.Text_35_5_2`;
- `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt` from
  `Chap05.Lemma_23_0_1`, whose slice specialization is the intended proof route.

Primitive data vs derived API:
- primitive inputs for the owner theorem: convexity of the second-variable slice `K u`, a finite
  point `v`, nonemptiness of `subdifferential2At K u v`, and a second-variable direction `v'`;
- derived API here: only the source-facing uncurried-partial formula for the same fixed second
  slice.

Layer target:
- `bridge/view`.

Finite-value convention:
- the project encodes scalar finiteness of `K(u, v)` as `v ∈ dom(K u)` together with
  `K u v ≠ ⊥`, i.e. the value
  is neither `⊤` nor `⊥`.
-/

-- Proof sketch: fix `u` and apply the Chapter 23 support-function formula to the convex
-- second-variable slice `f := K u` at the finite point `v`. The second partial subdifferential
-- `∂₂[Y] K(u, v)` is exactly the Chapter 23 subdifferential of that slice, and the
-- source notation `K'(u, v; 0, v')` is the directional derivative of `uncurry K` in direction
-- `(0, v')`, which matches the slice derivative by the existing Chapter 35 bridge.
/-- Text 35.6.11, source-facing bridge form: for a fixed second slice `K u`, once that slice is
convex and its second partial subdifferential at `(u, v)` is known to be nonempty, the second
partial directional derivative `K'(u, v; 0, v')` is the support function of `∂₂ K(u, v)`. -/
theorem directionalDerivativeAt_uncurry_second_eq_supportFunction_subdifferential2At
    {Y : Type (max v w)} [HasPairing V Y 𝕜]
    {K : U → V → WithTopBot 𝕜} {u : U} (hKu_convex : (K u).IsConvex 𝕜)
    {v : V} (hv : v ∈ dom(K u)) (hv_bot : K u v ≠ ⊥)
    (hsub : (∂₂[Y]K(u, v)).Nonempty)
    (v' : V) :
    directionalDerivativeAt (uncurry K) (u, v) (0, v') =
      δᵛ(v' | ∂₂[Y]K(u, v)) := by
  rw [Function.directionalDerivativeAt_uncurry_second_eq K u v v']
  simpa using
    (Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt
      (f := K u) (x := v) hKu_convex hv hv_bot hsub v')

end

end Bifunction
