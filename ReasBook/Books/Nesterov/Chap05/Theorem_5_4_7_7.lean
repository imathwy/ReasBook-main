import Mathlib
import Nesterov.Chap01.Definition_1_10_18
import Nesterov.Chap05.Definition_5_4_7_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter Set Topology
open scoped BigOperators

universe v

variable {ι : Type v} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "LPoint" => E × E × ℝ × ℝ

/- Theorem 5.4.7.7 lies in the finite-family lifted log-sum-exp / barrier-function domain.

Sampled owner declarations:
* `liftedConeLogSumExp` from `Definition_5_4_7_12`, the source-facing lifted cone owner `hat Q`;
* `exponentialConeBarrier` from `Definition_5_4_7_10`, the scalar logarithmic barrier summed
  coordinatewise in the lifted construction;
* `AffineSubspace`, the canonical ambient owner for the normalization hyperplane;
* `IsBarrierFunctionOn` from `Chap01/Definition_1_10_18`, the project's canonical barrier owner
  on the intrinsic interior of a closed feasible set.

Source/core/bridge triage:
* source-facing: the hyperplane restriction of the lifted finite-family barrier `Ψ_L`;
* core/canonical: the normalization affine subspace together with `IsBarrierFunctionOn` on the
  closed normalized feasible region in that relative ambient space;
* bridge/view: the carrier inclusion of the normalization hyperplane and the resulting restricted
  barrier maps.

Primitive data:
* the finite-family lifted cone `liftedConeLogSumExp`;
* the scalar barrier owner `exponentialConeBarrier`;
* the normalization equation `∑ i, y i = τ`.

Derived API:
* `liftedConeLogSumExpBarrier`;
* `liftedConeLogSumExpNormalizationHyperplane`;
* `liftedConeLogSumExpRelativeDomain`;
* `liftedConeLogSumExpHyperplaneBarrier`;
* `liftedConeLogSumExpRelativeBarrierMap`.

The owner layer stays at an arbitrary finite index type `ι`, matching
`Definition_5_4_7_11` and `Definition_5_4_7_12`; the textbook `Fin n` presentation is only a
specialization bridge. -/

/-- The ambient logarithmic barrier `Ψ_L(x, y, t, τ)` is the finite sum of the canonical scalar
exponential-cone barriers on the coordinate triples `((x^(i) - t, y^(i)), τ)`. -/
def liftedConeLogSumExpBarrier : LPoint → ℝ :=
  fun p ↦ ∑ i : ι, exponentialConeBarrier ((p.1 i - p.2.2.1, p.2.1 i), p.2.2.2)

-- Proof sketch: unfold `liftedConeLogSumExpBarrier`; evaluating at `(x, y, t, τ)` is a direct
-- substitution into the coordinatewise scalar barrier sum.
/-- Evaluating `liftedConeLogSumExpBarrier` at `(x, y, t, τ)` gives the finite sum of the scalar
exponential-cone barriers on the coordinates `((x^(i) - t, y^(i)), τ)`. -/
@[simp]
theorem liftedConeLogSumExpBarrier_apply
    (x y : E) (t τ : ℝ) :
    liftedConeLogSumExpBarrier (x, y, t, τ) =
      ∑ i : ι, exponentialConeBarrier ((x i - t, y i), τ) :=
  rfl

-- Proof sketch: rewrite each summand with `exponentialConeBarrier_apply`, use positivity to
-- expand `log (y^(i) / τ) = log y^(i) - log τ`, and then rearrange the logarithmic slack term.
/-- On the positive branch `τ > 0` and `y^(i) > 0`, the lifted barrier expands to the textbook
formula for `Ψ_L(x, y, t, τ)`. -/
theorem liftedConeLogSumExpBarrier_apply_formula
    (x y : E) (t τ : ℝ) (hτ : 0 < τ) (hy : ∀ i : ι, 0 < y i) :
    liftedConeLogSumExpBarrier (x, y, t, τ) =
      -∑ i : ι,
        (Real.log (t + τ * Real.log (y i) - x i - τ * Real.log τ) +
          Real.log (y i) + Real.log τ) := by
  rw [liftedConeLogSumExpBarrier, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [exponentialConeBarrier_apply]
  have harg :
      τ * Real.log (y i / τ) - (x i - t) =
        t + τ * Real.log (y i) - x i - τ * Real.log τ := by
    rw [Real.log_div (hy i).ne' hτ.ne']
    ring
  rw [harg]
  ring

/-- The linear normalization functional whose kernel cuts out the hyperplane `∑ i, y i = τ`. -/
private def liftedConeLogSumExpNormalizationLinearMap : LPoint →ₗ[ℝ] ℝ where
  toFun := fun p ↦ ∑ i : ι, p.2.1 i - p.2.2.2
  map_add' p q := by
    simp [Finset.sum_add_distrib, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  map_smul' c p := by
    simp only [Prod.smul_snd, Prod.smul_fst, PiLp.smul_apply, smul_eq_mul, Real.ringHom_apply,
      sub_eq_add_neg]
    rw [← Finset.mul_sum]
    ring_nf

/-- The normalization hyperplane `∑ i, y i = τ` on which the relative geometry of `hat Q` is
considered. -/
def liftedConeLogSumExpNormalizationHyperplane : AffineSubspace ℝ LPoint :=
  liftedConeLogSumExpNormalizationLinearMap.ker.toAffineSubspace

local notation "H" => (liftedConeLogSumExpNormalizationHyperplane : AffineSubspace ℝ LPoint)

-- Proof sketch: unfold `liftedConeLogSumExpNormalizationHyperplane`; the defining equation is
-- exactly the displayed normalization identity.
/-- A quadruple `(x, y, t, τ)` belongs to the normalization hyperplane exactly when
`∑ i, y i = τ`. -/
theorem mem_liftedConeLogSumExpNormalizationHyperplane_iff
    {x y : E} {t τ : ℝ} :
    (x, y, t, τ) ∈ liftedConeLogSumExpNormalizationHyperplane ↔ ∑ i, y i = τ := by
  simp [liftedConeLogSumExpNormalizationHyperplane,
    liftedConeLogSumExpNormalizationLinearMap, sub_eq_zero]

/-- The open relative-domain model of `hat Q`, viewed on the carrier of the normalization affine
hyperplane, is the pullback of the ambient lifted cone along the hyperplane inclusion. -/
abbrev liftedConeLogSumExpRelativeDomain : Set H :=
  Subtype.val ⁻¹' liftedConeLogSumExp

local notation "D" => (liftedConeLogSumExpRelativeDomain : Set H)

/-- A point of the normalization affine subspace belongs to `liftedConeLogSumExpRelativeDomain`
exactly when its underlying quadruple belongs to the lifted cone `liftedConeLogSumExp`. -/
theorem mem_liftedConeLogSumExpRelativeDomain_iff
    (p : H) :
    p ∈ liftedConeLogSumExpRelativeDomain ↔ p.1 ∈ liftedConeLogSumExp :=
  Iff.rfl

/-- The restriction of `Ψ_L` to the normalization hyperplane `∑ i, y i = τ`. -/
abbrev liftedConeLogSumExpHyperplaneBarrier : H → ℝ :=
  liftedConeLogSumExpBarrier ∘ Subtype.val

-- Proof sketch: unfold `liftedConeLogSumExpHyperplaneBarrier`; it is defined by evaluating the
-- ambient barrier `liftedConeLogSumExpBarrier` on the underlying quadruple.
/-- Evaluating the restricted barrier on the normalization hyperplane agrees with the ambient
formula `liftedConeLogSumExpBarrier`. -/
theorem liftedConeLogSumExpHyperplaneBarrier_apply
    (p : H) :
    liftedConeLogSumExpHyperplaneBarrier p = liftedConeLogSumExpBarrier p.1 :=
  rfl

/-- The canonical bundled barrier map on the intrinsic interior of the closed normalized lifted
region `closure liftedConeLogSumExpRelativeDomain`, obtained by restricting the hyperplane bridge
once more to the intrinsic interior. -/
abbrev liftedConeLogSumExpRelativeBarrierMap :
    C(interior (closure D), ℝ) where
  toFun := (interior (closure D)).restrict
    liftedConeLogSumExpHyperplaneBarrier
  continuous_toFun := sorry

/-- Evaluating the canonical bundled barrier map agrees with the ambient hyperplane restriction. -/
theorem liftedConeLogSumExpRelativeBarrierMap_apply
    (p : interior (closure D)) :
    liftedConeLogSumExpRelativeBarrierMap p = liftedConeLogSumExpHyperplaneBarrier p.1 :=
  rfl

-- Proof sketch: work in the subtype ambient space cut out by `∑ i, y i = τ`, and take the closed
-- feasible set `closure liftedConeLogSumExpRelativeDomain` so Chapter 1's barrier owner applies
-- in the correct ambient space. Its interior is the relative interior of `hat Q`. The coordinate
-- functions `y i`, `τ`, and
-- `t + τ * log (y i) - x i - τ * log τ = (t - x i) + τ * log (y i / τ)` are positive on the
-- relative interior, making the logarithmic sum continuous there. If a sequence in the relative
-- interior approaches the frontier of the closed normalized region, then either some `y i`, `τ`,
-- or one of the logarithmic slack terms tends to `0`, forcing the corresponding term of `Ψ_L` to
-- diverge to `+∞`.
/-- Theorem 5.4.7.7: restricting `Ψ_L(x, y, t, τ)` to the hyperplane `∑ i, y^(i) = τ` yields a
barrier function on the closed normalized lifted log-sum-exp region
`closure liftedConeLogSumExpRelativeDomain`, viewed in its intrinsic relative ambient space. -/
theorem liftedConeLogSumExpBarrier_restriction_isBarrierFunctionOn :
    IsBarrierFunctionOn
      (closure D)
      liftedConeLogSumExpRelativeBarrierMap := sorry
