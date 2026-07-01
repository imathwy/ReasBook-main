import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_25
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_15_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped GaugePolar ProfileConjugate RealInnerProductSpace Rockafellar

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.28 specializes Theorem 15.3 to the quadratic gauge
  `matrixQuadraticGauge Q = (fun x ↦ ⟨x, Qx⟩^(1 / 2))` attached to a positive definite matrix `Q`.
- `core/canonical`: the owner abstractions already present in the chapter are
  `IsClosedGauge`, `kᵒ`, `Function.IsClosedProperConvex`, `f⋆`, and the
  profile-side owners `rayProfileConjugate` and `rayProfileExtension` together with the theorem
  `convexConjugate_eq_rayProfileConjugate_comp_gauge_polar_of_eq_comp_closedGauge_profile`.
- `bridge/view`: `powerGaugeTransform 2 (matrixQuadratic Q)` is only the Chapter 15 bridge
  to the source-facing owner `matrixQuadraticGauge Q`, together with the bridge theorem
  `powerGaugeTransform_two_matrixQuadratic_eq_matrixQuadraticGauge`, the closed-gauge
  theorem `matrixQuadraticGauge_isClosedGauge`, and the polar theorem
  `gauge_polar_matrixQuadraticGauge_eq_inverse` from `Text_15_0_25`, so this file should keep
  only the resulting specialization theorem instead of parallel local wrappers.

Domain-style sampling used here:
- `matrixQuadraticGauge_isClosedGauge`;
- `gauge_polar_matrixQuadraticGauge_eq_inverse`;
- `convexConjugate_eq_rayProfileConjugate_comp_gauge_polar_of_eq_comp_closedGauge_profile`.

Primitive data vs derived API:
- primitive inputs: the positive definite matrix `Q` and the scalar profile `g`;
- derived quadratic data: the source-facing owner `matrixQuadraticGauge Q` and its inverse-matrix
  polar, both already provided upstream;
- derived output here: the closed-proper-convex and conjugate formula for the specialized
  composite `x ↦ g (⟨x, Qx⟩^(1 / 2))`.

Layer target: `source-facing`; the file records only the quadratic specialization of the Chapter
15 owner theorem, but its theorem surface is stated directly with `matrixQuadraticGauge Q` and
uses `powerGaugeTransform` only through upstream bridge theorems.
-/

-- Proof sketch: apply Theorem 15.3 to the closed gauge `matrixQuadraticGauge Q`. The closed-gauge
-- hypothesis is supplied by `matrixQuadraticGauge_isClosedGauge`, and its polar is rewritten by
-- `gauge_polar_matrixQuadraticGauge_eq_inverse`.
/-- Text 15.0.28: if `Q` is positive definite and `g` satisfies the scalar-profile hypotheses of
Theorem 15.3, then the function `f(x) = g(⟨x, Qx⟩^(1 / 2))` is closed proper convex and its
conjugate is `g⁺(⟨x⋆, Q⁻¹ x⋆⟩^(1 / 2))`, formalized through the source-facing owner
`matrixQuadraticGauge Q`. -/
theorem comp_matrixQuadraticGauge_isClosedProperConvex_and_convexConjugate_eq
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) {g : NNReal → EReal}
    (hg_ray : g.IsMonotoneClosedConvexOnNonnegativeRay)
    (hg_finite_pos : ∃ ζ : NNReal, 0 < ζ.1 ∧ g ζ < ⊤)
    (hg_nonconstant : ∃ s t : NNReal, g s ≠ g t) :
    (rayProfileExtension g ∘ matrixQuadraticGauge Q).IsClosedProperConvex ∧
      (rayProfileExtension g ∘ matrixQuadraticGauge Q)⋆ =
        rayProfileExtension (g⁺) ∘ matrixQuadraticGauge Q⁻¹ := by
  let k : E → EReal := matrixQuadraticGauge Q
  let f : E → EReal := rayProfileExtension g ∘ k
  have hk : IsClosedGauge k := by
    simpa [k] using matrixQuadraticGauge_isClosedGauge hQ.posSemidef
  have hf : IsGaugeLike[ℝ] f ∧ f.IsClosedProperConvex :=
    (isGaugeLike_and_isClosedProperConvex_iff_exists_closedGauge_profile f).2
      ⟨k, hk, g, hg_ray, hg_finite_pos, hg_nonconstant, rfl⟩
  have hf_conj : f⋆ = rayProfileExtension (g⁺) ∘ kᵒ :=
    convexConjugate_eq_rayProfileConjugate_comp_gauge_polar_of_eq_comp_closedGauge_profile
      hk hg_ray rfl
  constructor
  · simpa [f, k] using hf.2
  · simpa [f, k, gauge_polar_matrixQuadraticGauge_eq_inverse hQ] using hf_conj

end
