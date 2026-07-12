import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_1_5
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

local notation "R2" => (ℝ × ℝ)

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.8 states that the Section 27 example
  `f(ξ₁, ξ₂) = f₀(ξ₁, ξ₂) - ξ₁` is a finite convex function on `R²`.
- `core/canonical`: the source owner is the real-valued `ConvexOn ℝ Set.univ` surface for
  `parabolicObjective`.
- `bridge/view`: the source-facing function itself is already the chapter owner
  `parabolicObjective` from Definition 6.27.8, so this item keeps `ConvexOn` on the theorem
  surface and exposes `toWithTopBot.IsConvex` only as a finite-height bridge.

Domain-style sampling used here:
- `Function.IsConvex` from `Chap01.Theorem_4_2`;
- `Function.isConvex_coe_of_convexOn_univ` from the same file;
- `distanceToSet_isConvex` from `Chap01.Text_5_4_1_5`;
- `Function.isConvexOn_iff_convex_epigraph` and `convexOn_iff_convex_epigraph` as the
  codomain-bridge conversion between `WithTopBot` and finite real branches;
- `LinearMap.convexOn` / `ConvexOn.add` from mathlib's convex-function owner layer;
- the source-facing functions `parabolicF0` and `parabolicObjective` from
  `Definition_6_27_8`.

Primitive data vs derived API:
- primitive source data: the real-valued functions `parabolicF0` and `parabolicObjective`;
- derived API: the finite-height bridge theorem via
  `Function.isConvex_coe_of_convexOn_univ`.

Layer target: `source-facing` `ConvexOn ℝ Set.univ` statement, with
`toWithTopBot.IsConvex` as a bridge/view companion.

Real-scalar justification: this item's source owner `parabolicObjective` is intrinsically the
real-valued perturbation `f₀(ξ) - ξ.1` on `R2 = ℝ × ℝ`; both the codomain and the ambient space
are fixed by that source datum, not by proof convenience.
-/

-- Proof sketch for `parabolicF0_convexOn_univ`: `distanceToSet_isConvex` gives convexity of
-- `d(·, P)` in the chapter codomain `WithTopBot ℝ`. Because `P` is nonempty,
-- `d(·, P) = infDist · P` in `WithTopBot ℝ`; the finite-height epigraph bridge converts this to
-- convexity of the real branch `infDist · P`. Squaring by `ConvexOn.pow` gives convexity of `f₀`.
/-- Convexity of the source branch `f₀` from Definition 6.27.8 on `R²`. -/
theorem parabolicF0_convexOn_univ :
    ConvexOn ℝ Set.univ parabolicF0 := by
  let P : Set R2 := (paraboloidEpigraph : Set R2)
  have hP_nonempty : P.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp [P, paraboloidEpigraph]
  have hdist_isConvex :
      Function.IsConvex ℝ (fun ξ : R2 ↦ (d(ξ, P) : WithTopBot ℝ)) := by
    simpa [P] using
      (distanceToSet_isConvex P (by simpa [P] using (paraboloidEpigraph_convex (𝕜 := ℝ))))
  have hdist_on :
      Function.IsConvexOn ℝ Set.univ (fun ξ : R2 ↦ (d(ξ, P) : WithTopBot ℝ)) := by
    simpa [Function.IsConvex] using hdist_isConvex
  have hdist_eq_infDist :
      (fun ξ : R2 ↦ (d(ξ, P) : WithTopBot ℝ)) =
        fun ξ : R2 ↦ ((Metric.infDist ξ P : ℝ) : WithTopBot ℝ) := by
    funext ξ
    simpa [P] using (distanceToSet_eq_infDist (E := R2) (C := P) hP_nonempty ξ)
  have hInfDist_coe_on :
      Function.IsConvexOn ℝ Set.univ (fun ξ : R2 ↦ ((Metric.infDist ξ P : ℝ) : WithTopBot ℝ)) := by
    simpa [hdist_eq_infDist] using hdist_on
  have hInfDist : ConvexOn ℝ Set.univ (fun ξ : R2 ↦ Metric.infDist ξ P) := by
    rw [convexOn_iff_convex_epigraph]
    simpa [Function.IsConvexOn, epi_eq_setOf_mem_and_le] using hInfDist_coe_on
  simpa [parabolicF0, P] using
    (hInfDist.pow (by intro ξ _; exact Metric.infDist_nonneg) 2)

/-- Owner-level convexity bridge for `f₀`: finite-valued convexity on `R²` lifted to
`WithTopBot ℝ`. -/
theorem parabolicF0_isConvex :
    parabolicF0.toWithTopBot.IsConvex ℝ := by
  simpa [Function.toWithTopBot] using
    Function.isConvex_coe_of_convexOn_univ parabolicF0_convexOn_univ

-- Proof sketch for `parabolicObjective_convexOn_univ`: combine convexity of `f₀` with convexity
-- of the affine branch `ξ ↦ -ξ.1`.
/-- Proposition 6.27.8, source-facing canonical form:
the Section 27 objective `f(ξ₁, ξ₂) = f₀(ξ₁, ξ₂) - ξ₁` is convex on `R²`. -/
theorem parabolicObjective_convexOn_univ :
    ConvexOn ℝ Set.univ parabolicObjective := by
  have hF0 : ConvexOn ℝ Set.univ parabolicF0 := parabolicF0_convexOn_univ
  have hlin : ConvexOn ℝ Set.univ (fun ξ : R2 ↦ -ξ.1) := by
    have hlin' : ConvexOn ℝ Set.univ (-(fun ξ : R2 ↦ ξ.1)) :=
      ConcaveOn.neg <|
        LinearMap.concaveOn (LinearMap.fst ℝ ℝ ℝ) (s := (Set.univ : Set R2)) convex_univ
    change ConvexOn ℝ Set.univ (-(fun ξ : R2 ↦ ξ.1))
    exact hlin'
  simpa [parabolicObjective, sub_eq_add_neg] using hF0.add hlin

/-- Proposition 6.27.8, finite-height bridge form:
the Section 27 objective `f(ξ₁, ξ₂) = f₀(ξ₁, ξ₂) - ξ₁` is a finite convex function on `R²`. -/
theorem parabolicObjective_isConvex :
    parabolicObjective.toWithTopBot.IsConvex ℝ := by
  simpa [Function.toWithTopBot] using
    Function.isConvex_coe_of_convexOn_univ parabolicObjective_convexOn_univ
