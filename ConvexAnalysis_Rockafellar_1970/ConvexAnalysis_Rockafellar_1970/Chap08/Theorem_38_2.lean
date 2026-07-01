import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_29_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_0_1

noncomputable section

open scoped Rockafellar

namespace Bifunction

section

universe u v

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]

local notation "ri(" C ")" => intrinsicInterior ℝ C

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 38.2 is the adjoint-duality identity for the bifunction infimal
  convolution `F₁ D F₂`.
- `core/canonical`: the stable owners already present upstream are `D`, `adjoint`, the
  bifunction-domain owner `dom F`, and the graph-properness owner `(Function.uncurry F).IsProper`.
- `bridge/view`: Proposition 6.29.3 already gives the exact bridge
  `dom_eq_setOf_slice_isProper_of_isProper`, identifying `dom F` with the source set
  `{u | (F u).IsProper}` under the graphwise properness hypothesis. The theorem should therefore
  use the established owner `dom F` on its public surface rather than restating that set.

Domain-style sampling used here:
- `Bifunction.dom` from `Chap06.Definition_6_29_8`;
- `Bifunction.dom_eq_setOf_slice_isProper_of_isProper` from `Chap06.Proposition_6_29_3`;
- `Bifunction.adjoint` from `Chap06.Definition_6_30_14`;
- `Bifunction.infimalConvolution`, notation `D`, from `Chap08.Definition_38_0_1`.

Primitive data vs derived API:
- primitive source data: bifunctions `F₁` and `F₂`;
- primitive owner hypotheses: convexity and graphwise properness of `Function.uncurry F₁` and
  `Function.uncurry F₂`, together with the chapter qualification owner
  `ri(dom F₁) ∩ ri(dom F₂)`;
- derived bridge data: the source qualification set `{u | (F u).IsProper}` is recovered from
  `dom F` via `dom_eq_setOf_slice_isProper_of_isProper`.

Layer target: `source-facing`.
-/

-- Proof sketch: combine the Chapter 38 infimal-convolution owner `D` with the Chapter 6 adjoint
-- owner `adjoint` under the common-relative-interior qualification on `dom F₁` and
-- `dom F₂`. The source wording in terms of proper slices is recovered owner-theoretically by
-- `dom_eq_setOf_slice_isProper_of_isProper`, while the exact adjoint identity keeps the graphwise
-- properness hypotheses on `Function.uncurry F₁` and `Function.uncurry F₂`.
/- Bridge/view form of the source qualification: under graphwise properness, the textbook sets
`{u | (F₁ u).IsProper}` and `{u | (F₂ u).IsProper}` may be replaced by the chapter owner
`dom F₁` and `dom F₂`. -/
omit [FiniteDimensional ℝ U] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
  [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ] in
theorem common_riDom_of_common_ri_setOf_slice_isProper
    {F₁ F₂ : U → X → EReal}
    (hF₁_graphProper : (Function.uncurry F₁).IsProper)
    (hF₂_graphProper : (Function.uncurry F₂).IsProper)
    (hri :
      (ri({u : U | (F₁ u).IsProper}) ∩ ri({u : U | (F₂ u).IsProper})).Nonempty) :
    (ri(dom F₁) ∩ ri(dom F₂)).Nonempty := by
  have hdom₁ : dom F₁ = {u : U | (F₁ u).IsProper} :=
    dom_eq_setOf_slice_isProper_of_isProper hF₁_graphProper
  have hdom₂ : dom F₂ = {u : U | (F₂ u).IsProper} :=
    dom_eq_setOf_slice_isProper_of_isProper hF₂_graphProper
  simpa [hdom₁, hdom₂] using hri

/-- Theorem 38.2: if convex bifunctions `F₁` and `F₂` are graphwise proper and have a common
point in `ri (dom F₁) ∩ ri (dom F₂)`, then the adjoint of their infimal convolution is the
infimal convolution of their adjoints, i.e. `(F₁ D F₂)^* = F₁^* D F₂^*`, rendered by the owners
`dom`, `D`, and `adjoint`. The convexity, graph-properness, and common-`ri(dom)`
qualification hypotheses are part of the public owner surface; the preceding bridge theorem only
recovers the source wording in terms of `{u | (F u).IsProper}`. -/
theorem
    adjointFunction_infimalConvolution_eq_infimalConvolution_adjointFunction_of_common_riDom
    {F₁ F₂ : U → X → EReal}
    (hF₁_convex : Function.IsConvex ℝ (Function.uncurry F₁))
    (hF₁_graphProper : (Function.uncurry F₁).IsProper)
    (hF₂_convex : Function.IsConvex ℝ (Function.uncurry F₂))
    (hF₂_graphProper : (Function.uncurry F₂).IsProper)
    (hri : (ri(dom F₁) ∩ ri(dom F₂)).Nonempty) :
    adjoint X U (F₁ D F₂) =
      (adjoint X U F₁) D (adjoint X U F₂) := sorry

end

end Bifunction
