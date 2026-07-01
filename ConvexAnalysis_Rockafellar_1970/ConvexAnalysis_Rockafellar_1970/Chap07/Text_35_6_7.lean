import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Mul
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_2

noncomputable section

open Function
open scoped Rockafellar

universe u v w

namespace Bifunction

section

variable {𝕜 : Type w} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [AddCommMonoid V] [SMul 𝕜 V]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.7 fixes a second-variable slice `K u`, a finite point `v`, and the
  second partial directional-derivative profile `v' ↦ K'(u, v; 0, v')`.
- `core/canonical`: the owner abstractions are the convex slice predicate `(K u).IsConvex 𝕜` and
  the Chapter 23 directional-derivative owner `Function.directionalDerivativeAt`.
- `bridge/view`: the source notation `K'(u, v; 0, v')` is rendered directly by the slice owner
  `directionalDerivativeAt (K u) v`.

Domain-style sampling used here:
- `Function.IsConvex 𝕜` from `Chap01/Theorem_4_2`;
- `Function.directionalDerivativeAt` from `Chap05/Lemma_23_0_1`;
- `Function.isConvex_directionalDerivativeAt_of_finite_point` from `Chap05/Theorem_23_1`.

Primitive data vs derived API:
- primitive inputs: the slice `K u`, the fixed point `v`, convexity of that slice, and finiteness
  of `K u v`;
- derived API: convexity of the second partial directional-derivative profile.

Layer target: `source-facing`, stated directly on the canonical chapter owners.

Ambient-assumption minimization:
- the first variable is only a parameter indexing the slice `K u`, so no algebraic structure on
  `U` belongs in the public API;
- the second variable here needs the scalar-action layer used by the Chapter 23 finite-point
  convexity theorem for directional derivatives.
-/

-- Proof sketch: fix `u` and set `f := K u`. The convex-slice hypothesis applies directly to `f`.
-- The source profile `v' ↦ K'(u, v; 0, v')` is the Chapter 23 directional
-- derivative `v' ↦ directionalDerivativeAt f v v'`, and directional derivatives of a convex slice
-- at a finite point are convex in the direction variable.
/-- Text 35.6.7 (1): if the second-variable slice `K u` is convex and `K u v` is finite, then the
second partial directional-derivative profile `v' ↦ K'(u, v; 0, v')`, rendered here by the slice
owner `directionalDerivativeAt (K u) v`, is a convex function on the second variable space. -/
theorem isConvex_directionalDerivativeAt_second
    {K : U → V → WithTopBot 𝕜} {u : U} (hKu_convex : (K u).IsConvex 𝕜)
    {v : V} (hv : v ∈ dom(K u)) (hv_bot : K u v ≠ ⊥) :
    (directionalDerivativeAt (K u) v).IsConvex 𝕜 := by
  simpa using
    Function.isConvex_directionalDerivativeAt_of_finite_point hKu_convex hv hv_bot

end

section

variable {𝕜 : Type w}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.7 also identifies the lower-semicontinuous hull of the same second
  partial directional-derivative profile with the support function of the second partial
  subdifferential.
- `core/canonical`: the owner abstractions are the convex slice predicate `(K u).IsConvex 𝕜`,
  the lower-semicontinuous hull `cl(·)`, the support function `δᵛ(· | ·)`, and the chapter
  bifunction owner `Bifunction.subdifferential2At`.
- `bridge/view`: the source-facing `∂₂ K(u, v)` is the thin chapter bridge to the upstream slice
  owner `_root_.subdifferentialAt (K u) v` on the canonical dual `StrongDual 𝕜 V`.

Domain-style sampling used here:
- `Function.IsConvex 𝕜` from `Chap01/Theorem_4_2`;
- `Function.directionalDerivativeAt` from `Chap05/Lemma_23_0_1`;
- `Bifunction.subdifferential2At` from `Chap07/Text_35_5_2`;
- `_root_.subdifferentialAt` from `Chap05/Definition_23_0_6`, as the upstream owner reused by
  `subdifferential2At`;
- chapter owners `cl(·)` and `δᵛ(· | ·)`.

Primitive data vs derived API:
- primitive inputs: the slice `K u`, convexity/properness of that slice, and a base point in the
  intrinsic relative interior `v ∈ riDom[𝕜](K u)`;
- derived API: the lower-semicontinuous-hull/support-function identity for the second partial
  directional-derivative profile.

Layer target: `source-facing`, with the second partial subdifferential surfaced through the
chapter's canonical bifunction owner `∂₂ K(u, v)`.

Ambient-assumption minimization:
- the first variable again only indexes the slice `K u`, so no algebraic structure on `U` enters
  this theorem surface;
- this clause is rebased to the existing Chapter 23 `riDom` owner theorem for support-function
  representation, so its order-topology and properness hypotheses are retained explicitly.
-/

-- Proof sketch: set `f := K u`. The Chapter 23 `riDom` theorem gives
-- `directionalDerivativeAt f v = δᵛ(· | ∂ f at v)` and `IsClosedProperConvex` for the same
-- directional-derivative profile. Closedness yields `cl(directionalDerivativeAt f v) =
-- directionalDerivativeAt f v`, and the chapter bridge `∂₂ K(u, v)` identifies the slice
-- subdifferential term on the source-facing theorem surface.
/-- Text 35.6.7, support-owner bridge: for a convex proper second-variable slice `K u` and
`v ∈ riDom[𝕜](K u)`, the second partial directional-derivative profile is exactly the support
function of the second partial subdifferential. -/
theorem directionalDerivativeAt_second_eq_supportFunction_subdifferential2At_of_mem_riDom
    {Y : Type*} [HasPairing V Y 𝕜]
    {K : U → V → WithTopBot 𝕜} {u : U} (hKu_convex : (K u).IsConvex 𝕜)
    (hKu_proper : (K u).IsProper) {v : V} (hv : v ∈ riDom[𝕜](K u)) :
    directionalDerivativeAt (K u) v =
      (δᵛ(· | ∂₂[Y]K(u, v)) : V → WithTopBot 𝕜) := by
  have hdirRoot :
      directionalDerivativeAt (K u) v =
        (δᵛ(· | _root_.subdifferentialAt (Y := Y) (K u) v) : V → WithTopBot 𝕜) :=
    _root_.directionalDerivativeAt_eq_supportFunction_subdifferentialAt_of_mem_riDom
      (f := K u) (x := v) (Y := Y) hKu_convex hKu_proper hv
  simpa [Bifunction.subdifferential2At_eq_subdifferentialAt] using hdirRoot

/-- Text 35.6.7 (2): if the second-variable slice `K u` is convex proper and
`v ∈ riDom[𝕜](K u)`, then the lower-semicontinuous hull of the second partial directional
derivative profile equals the support function of the second partial subdifferential
`∂₂[Y] K(u, v)`. -/
theorem lowerSemicontinuousHull_directionalDerivativeAt_second_eq_supportFunction_subdifferential2At
    {Y : Type*} [HasPairing V Y 𝕜]
    {K : U → V → WithTopBot 𝕜} {u : U} (hKu_convex : (K u).IsConvex 𝕜)
    (hKu_proper : (K u).IsProper) {v : V} (hv : v ∈ riDom[𝕜](K u)) :
    cl(directionalDerivativeAt (K u) v) =
      (δᵛ(· | ∂₂[Y]K(u, v))) := by
  have hclosed :
      Function.IsClosedProperConvex (𝕜 := 𝕜) (directionalDerivativeAt (K u) v) :=
    _root_.isClosedProperConvex_directionalDerivativeAt_of_mem_riDom
      (f := K u) (x := v) hKu_convex hKu_proper hv
  have hdir :
      directionalDerivativeAt (K u) v =
        (δᵛ(· | ∂₂[Y]K(u, v)) : V → WithTopBot 𝕜) :=
    directionalDerivativeAt_second_eq_supportFunction_subdifferential2At_of_mem_riDom
      (Y := Y) hKu_convex hKu_proper hv
  calc
    cl(directionalDerivativeAt (K u) v) = directionalDerivativeAt (K u) v := by
      simpa using
        lowerSemicontinuousHull_eq_self (f := directionalDerivativeAt (K u) v) hclosed.closed
    _ = (δᵛ(· | ∂₂[Y]K(u, v)) : V → WithTopBot 𝕜) := hdir

/-- Strong-dual specialization of Text 35.6.7 support-owner bridge: with the canonical dual
surface `∂₂ K(u, v)`, the second partial directional-derivative profile equals the
support function of the second partial subdifferential. -/
theorem directionalDerivativeAt_second_eq_supportFunction_subdifferential2AtDual_of_mem_riDom
    {K : U → V → WithTopBot 𝕜} {u : U} (hKu_convex : (K u).IsConvex 𝕜)
    (hKu_proper : (K u).IsProper) {v : V} (hv : v ∈ riDom[𝕜](K u)) :
    directionalDerivativeAt (K u) v =
      (δᵛ(· | ∂₂ K(u, v)) : V → WithTopBot 𝕜) := by
  simpa using
    directionalDerivativeAt_second_eq_supportFunction_subdifferential2At_of_mem_riDom
      (Y := StrongDual 𝕜 V) hKu_convex hKu_proper hv

/-- Strong-dual specialization of Text 35.6.7 (2): with the canonical dual surface
`∂₂ K(u, v)`, the lower-semicontinuous hull of the second partial directional
derivative profile equals the support function of the second partial subdifferential. -/
theorem
    lowerSemicontinuousHull_directionalDerivativeAt_second_eq_supportFunction_subdifferential2AtDual
    {K : U → V → WithTopBot 𝕜} {u : U} (hKu_convex : (K u).IsConvex 𝕜)
    (hKu_proper : (K u).IsProper) {v : V} (hv : v ∈ riDom[𝕜](K u)) :
    cl(directionalDerivativeAt (K u) v) =
      (δᵛ(· | ∂₂ K(u, v))) := by
  simpa using
    lowerSemicontinuousHull_directionalDerivativeAt_second_eq_supportFunction_subdifferential2At
      (Y := StrongDual 𝕜 V) hKu_convex hKu_proper hv

end

end Bifunction
