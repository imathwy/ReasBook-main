import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem exists_mem_riDom_indicator_of_exists_mem_intrinsicInterior
    (A : E →ₗ[ℝ] F) {D : Set F}
    (hri : ∃ x : E, A x ∈ intrinsicInterior ℝ D) :
    ∃ x : E, A x ∈ intrinsicInterior ℝ dom(indicatorFunction D) := by
  simpa [effectiveDomain_indicatorFunction] using hri

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.3.1.3 removes the closure from Corollary 16.3.1.2 for inverse
  images of a convex set `D` under a linear map `A`, assuming some point of the range of `A`
  meets `ri D`, and then records the fiberwise infimum formula together with attainment.
- `core/canonical`: the owner declarations are the chapter support-function notation `δᵛ(· | D)`,
  the linear-image notation `◁`, `LinearMap.adjoint`, and the relative-interior notation
  `riDom(·)`.
- `bridge/view`: Rockafellar's `δ*(· | D)` is rendered by `δᵛ(· | D)`, the inverse image `A⁻¹ D`
  by the set preimage `A ⁻¹' D`, and the adjoint-side fiber infimum by
  `Function.linearImage_eq_sInf_image`.

Domain-style sampling used here:
- `supportFunction_preimage_closure_eq_lowerSemicontinuousHull_linearImage_adjoint`
  from Corollary 16.3.1.2;
- `convexConjugate_comp_linearMap_eq_linearImage_adjoint_of_exists_mem_intrinsicInterior_dom`,
  `convexConjugate_comp_linearMap_apply_eq_sInf_image_conjugate_of_exists_mem_intrinsicInterior_dom`,
  and
  `convexConjugate_comp_linearMap_apply_eq_top_or_exists_adjoint_eq_and_eq_conjugate_of_exists_mem_intrinsicInterior_dom`
  from Theorem 16.3.3;
- the support-function/indicator bridge
  `convexConjugate_indicatorFunction_eq_supportFunction`.

Primitive data vs derived API:
- primitive inputs: a linear map `A : E → F`, a convex set `D ⊆ F`, and a witness
  `∃ x, A x ∈ ri D`;
- derived API: the closure-free support-function identity, its pointwise infimum formula, and the
  attained-or-vacuous alternative.

Layer target: `source-facing`, stated directly in the canonical chapter notation.

Ambient note: the owner theorems sampled above already live on arbitrary finite-dimensional real
inner-product spaces, so this corollary is refined to that same canonical ambient level instead of
reintroducing the coordinate model `EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)`.
-/

-- Proof sketch: specialize Theorem 16.3.3 to the indicator function `indicatorFunction D`.
-- Convexity of `D` gives the needed convexity of that indicator, and the effective domain of the
-- indicator is exactly `D`, so the hypothesis is already the relative-interior condition required
-- there. The support-function/indicator bridge then rewrites the conjugate identities into the
-- displayed support-function identity, which is exactly Corollary 16.3.1.2 with the closure
-- operation removed.
/-- Corollary 16.3.1.3, in canonical ambient form: for a real linear map `A : E → F` between
finite-dimensional inner-product spaces and a convex set `D ⊆ F`, if some `A x` lies in `ri D`,
then the closure in Corollary 16.3.1.2 is unnecessary, so
`δ*(· | A⁻¹ D) = A* δ*(· | D)`, rendered here as `(δᵛ(· | A ⁻¹' D)) = A.adjoint ◁ (δᵛ(· | D))`.
The textbook Euclidean statement is recovered by specializing `E = R^n` and `F = R^m`. -/
theorem supportFunction_preimage_eq_linearImage_adjoint_supportFunction_of_exists_mem_intrinsicInterior
    (A : E →ₗ[ℝ] F) (D : Set F) (hD : Convex ℝ D)
    (hri : ∃ x : E, A x ∈ intrinsicInterior ℝ D) :
    (δᵛ(· | A ⁻¹' D)) = A.adjoint ◁ (δᵛ(· | D)) := by
  simpa [show indicatorFunction D ∘ A = indicatorFunction (A ⁻¹' D) by rfl,
    convexConjugate_indicatorFunction_eq_supportFunction] using
    (convexConjugate_comp_linearMap_eq_linearImage_adjoint_of_exists_mem_intrinsicInterior_dom
      A (indicatorFunction D) ((indicatorFunction_isConvex_iff D).2 hD)
      (exists_mem_riDom_indicator_of_exists_mem_intrinsicInterior A hri))

-- Proof sketch: evaluate the closure-free support-function identity at `xStar`, then rewrite the
-- value of `Function.linearImage A.adjoint (supportFunction D)` by the owner formula
-- `Function.linearImage_eq_sInf_image`.
/-- Evaluating the closure-free support-function identity at `xStar` gives the infimum of
`δ*(· | D)` over the adjoint fiber `A* y* = xStar`. -/
theorem supportFunction_preimage_apply_eq_sInf_image_of_exists_mem_intrinsicInterior
    (A : E →ₗ[ℝ] F) (D : Set F) (hD : Convex ℝ D)
    (hri : ∃ x : E, A x ∈ intrinsicInterior ℝ D) (xStar : E) :
    δᵛ(xStar | A ⁻¹' D) =
      sInf ((δᵛ(· | D)) '' {yStar : F | A.adjoint yStar = xStar}) := by
  simpa [show indicatorFunction D ∘ A = indicatorFunction (A ⁻¹' D) by rfl,
    convexConjugate_indicatorFunction_eq_supportFunction] using
    (convexConjugate_comp_linearMap_apply_eq_sInf_image_conjugate_of_exists_mem_intrinsicInterior_dom
      A (indicatorFunction D) ((indicatorFunction_isConvex_iff D).2 hD)
      (exists_mem_riDom_indicator_of_exists_mem_intrinsicInterior A hri) xStar)

-- Proof sketch: specialize the attained-or-vacuous clause of Theorem 16.3.3 to the indicator
-- function of `D`, then translate the resulting conjugate terms back into support functions. If
-- the adjoint fiber is empty, the infimum is vacuous and the value is `⊤`; otherwise a minimizing
-- `yStar` exists.
/-- Under the same relative-interior hypothesis, the fiberwise infimum formula for
`δ*(· | A⁻¹ D)` is either vacuous, giving `⊤`, or is attained at some `yStar` with
`A.adjoint yStar = xStar`. -/
theorem supportFunction_preimage_apply_eq_top_or_exists_adjoint_eq_and_eq_supportFunction_of_exists_mem_intrinsicInterior
    (A : E →ₗ[ℝ] F) (D : Set F) (hD : Convex ℝ D)
    (hri : ∃ x : E, A x ∈ intrinsicInterior ℝ D) (xStar : E) :
    δᵛ(xStar | A ⁻¹' D) = ⊤ ∨
      ∃ yStar : F, A.adjoint yStar = xStar ∧
        δᵛ(xStar | A ⁻¹' D) = δᵛ(yStar | D) := by
  simpa [show indicatorFunction D ∘ A = indicatorFunction (A ⁻¹' D) by rfl,
    convexConjugate_indicatorFunction_eq_supportFunction] using
    (convexConjugate_comp_linearMap_apply_eq_top_or_exists_adjoint_eq_and_eq_conjugate_of_exists_mem_intrinsicInterior_dom
      A (indicatorFunction D) ((indicatorFunction_isConvex_iff D).2 hD)
      (exists_mem_riDom_indicator_of_exists_mem_intrinsicInterior A hri) xStar)

end
