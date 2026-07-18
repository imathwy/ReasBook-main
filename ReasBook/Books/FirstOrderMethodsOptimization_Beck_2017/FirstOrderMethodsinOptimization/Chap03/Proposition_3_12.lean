import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 3.12 is `source-facing`: it identifies the gradient of the half squared distance to
a nonempty complete convex set. The canonical `core/canonical` owner results in this domain are the
mathlib Hilbert projection theorems `exists_norm_eq_iInf_of_complete_convex` and
`norm_eq_iInf_iff_real_inner_le_zero`, together with the metric owner formula
`Metric.infDist_eq_iInf`. The only primitive data here are the set `C` together with its
nonempty/complete/convex hypotheses; the chosen metric projection and its basic properties are
derived `bridge/view` API built from those owner theorems. -/

-- Proof sketch: existence comes from `exists_norm_eq_iInf_of_complete_convex` applied to the
-- complete convex set `C`; uniqueness follows from `norm_eq_iInf_iff_real_inner_le_zero` by
-- applying the characterization to two minimizers `p` and `q`, testing once with `w = q` and once
-- with `w = p`, and then combining the two inequalities to force `‖p - q‖ = 0`.
private theorem existsUnique_metricProjection
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_complete : IsComplete C)
    (hC_convex : Convex ℝ C) (x : E) :
    ∃! p : C, ‖x - p‖ = ⨅ w : C, ‖x - w‖ := sorry

/-- The metric projection onto a nonempty complete convex subset of a real inner product space,
valued in the set itself. -/
noncomputable def metricProjection (C : Set E) (hC_nonempty : C.Nonempty)
    (hC_complete : IsComplete C)
    (hC_convex : Convex ℝ C) : E → C :=
  fun x ↦
    Classical.choose <|
      (existsUnique_metricProjection C hC_nonempty hC_complete hC_convex x).exists

section PointProjection

variable [CompleteSpace E]

/-- The ambient-space point projection `x ↦ P_C(x)` associated to the metric projection onto a
nonempty closed convex set. This is the canonical chapter-level point-valued bridge from
`metricProjection`; the closedness hypothesis supplies the derived completeness input. -/
noncomputable abbrev closedConvexProjectionPoint (C : Set E) (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) : E → E :=
  fun x ↦ (metricProjection C hC_nonempty hC_closed.isComplete hC_convex x : E)

syntax:max "Pp[" term ", " term ", " term ", " term "]" : term

macro_rules
  | `(Pp[$C, $hC_nonempty, $hC_closed, $hC_convex]) =>
      `(closedConvexProjectionPoint $C $hC_nonempty $hC_closed $hC_convex)

end PointProjection

section Projection

variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_complete : IsComplete C)
    (hC_convex : Convex ℝ C)

local notation "P" => metricProjection C hC_nonempty hC_complete hC_convex

private theorem metricProjection_spec (x : E) :
    ‖x - P x‖ = ⨅ w : C, ‖x - w‖ :=
  Classical.choose_spec <|
    (existsUnique_metricProjection C hC_nonempty hC_complete hC_convex x).exists

-- Proof sketch: unfold `metricProjection` as the chosen witness from
-- `existsUnique_metricProjection`; the chosen point satisfies the defining minimization property.
/-- The metric projection realizes the minimum distance to the set. -/
theorem norm_sub_metricProjection_eq_iInf (x : E) :
    ‖x - P x‖ = ⨅ w : C, ‖x - w‖ :=
  metricProjection_spec C hC_nonempty hC_complete hC_convex x

-- Proof sketch: combine the minimizing property of `P_C x` from
-- `norm_sub_metricProjection_eq_iInf` with mathlib's Hilbert-space characterization
-- `norm_eq_iInf_iff_real_inner_le_zero`.
/-- The metric projection satisfies the Hilbert-space variational inequality. -/
theorem inner_sub_metricProjection_le_zero (x : E) :
    ∀ w ∈ C, inner ℝ (x - P x) (w - P x) ≤ 0 := by
  have hproj : ‖x - P x‖ = ⨅ z : C, ‖x - z‖ := by
    simpa using norm_sub_metricProjection_eq_iInf C hC_nonempty hC_complete hC_convex x
  exact (norm_eq_iInf_iff_real_inner_le_zero hC_convex (P x).2).1 hproj

-- Proof sketch: rewrite `Metric.infDist` as the infimum of `dist x y` over `y ∈ C`, then apply
-- `norm_sub_metricProjection_eq_iInf` and `dist_eq_norm`.
/-- The distance from `x` to a nonempty closed convex set is realized by the metric projection. -/
theorem infDist_eq_dist_metricProjection (x : E) :
    infDist x C = dist x (P x) := sorry

-- Proof sketch: let `p = metricProjection C hC_nonempty hC_complete hC_convex x`. Use the
-- minimizing property of `p` together with convexity of `C` to get the first-order optimality
-- condition from `norm_eq_iInf_iff_real_inner_le_zero`. Rewrite
-- `y ↦ (Metric.infDist y C)^2 / 2` near `x` through the projection inequality, compare it with the
-- affine approximation `d ↦ ⟪x - p, d⟫ + (Metric.infDist x C)^2 / 2`, and conclude via
-- `hasGradientAt_iff_isLittleO`.
section Gradient

variable [CompleteSpace E]

/-- Proposition 3.12: for a nonempty complete convex set `C` in a real inner product space,
the function `x ↦ (Metric.infDist x C)^2 / 2` has gradient `x - P_C(x)` at `x`, where `P_C` is the
metric projection onto `C`. -/
theorem hasGradientAt_half_sq_infDist (x : E) :
    HasGradientAt (fun y ↦ (infDist y C) ^ 2 / 2) (x - P x) x := sorry

-- Proof sketch: apply `HasGradientAt.gradient` to `hasGradientAt_half_sq_infDist`.
/-- The totalized gradient of `x ↦ (Metric.infDist x C)^2 / 2` agrees with `x - P_C(x)` at points
where Proposition 3.12 provides differentiability. -/
theorem gradient_half_sq_infDist_eq_sub_metricProjection (x : E) :
    gradient (fun y ↦ (infDist y C) ^ 2 / 2) x = x - P x :=
  (hasGradientAt_half_sq_infDist C hC_nonempty hC_complete hC_convex x).gradient

end Gradient

end Projection

section PointProjectionFacts

variable [CompleteSpace E]
variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C)

local notation "Pₛ" => metricProjection C hC_nonempty hC_closed.isComplete hC_convex
local notation "P" => closedConvexProjectionPoint C hC_nonempty hC_closed hC_convex

-- Proof sketch: `closedConvexProjectionPoint` is the ambient-space coercion of `metricProjection`, whose
-- values lie in `C` by construction.
/-- The point projection onto a nonempty closed convex set belongs to that set. -/
theorem closedConvexProjectionPoint_mem (x : E) :
    P x ∈ C :=
  (Pₛ x).2

private theorem eq_projectionPoint_of_mem_of_norm_eq (x : E) {y : E} (hy : y ∈ C)
    (hnorm : ‖y - x‖ = ‖P x - x‖) :
    y = P x := by
  let yC : C := ⟨y, hy⟩
  have hyC_spec : ‖x - yC‖ = ⨅ w : C, ‖x - w‖ := by
    calc
      ‖x - yC‖ = ‖x - y‖ := rfl
      _ = ‖y - x‖ := norm_sub_rev _ _
      _ = ‖P x - x‖ := hnorm
      _ = ‖x - P x‖ := norm_sub_rev _ _
      _ = ⨅ w : C, ‖x - w‖ := by
        simpa [closedConvexProjectionPoint] using
          norm_sub_metricProjection_eq_iInf C hC_nonempty hC_closed.isComplete hC_convex x
  rcases existsUnique_metricProjection C hC_nonempty hC_closed.isComplete hC_convex x with
    ⟨p, hp, hp_unique⟩
  have hyC_eq : yC = p := hp_unique yC hyC_spec
  have hproj_eq : Pₛ x = p := by
    apply hp_unique
    simpa using
      norm_sub_metricProjection_eq_iInf C hC_nonempty hC_closed.isComplete hC_convex x
  calc
    y = yC := rfl
    _ = p := by exact congrArg ((↑) : C → E) hyC_eq
    _ = Pₛ x := by exact (congrArg ((↑) : C → E) hproj_eq).symm
    _ = P x := rfl

-- Proof sketch: the norm-minimizing property of `metricProjection` immediately yields the
-- pointwise comparison `‖P_C(x) - x‖ ≤ ‖y - x‖` for every `y ∈ C`; monotonicity of squaring on
-- nonnegative reals then gives the half squared-distance minimizer formulation.
/-- The point projection onto a nonempty closed convex set minimizes the half squared-distance
objective over that set. -/
theorem closedConvexProjectionPoint_isMinOn (x : E) :
    IsMinOn (fun y ↦ ‖y - x‖ ^ (2 : ℕ) / 2) C (P x) := by
  rw [isMinOn_iff]
  intro y hy
  have hnorm : ‖P x - x‖ ≤ ‖y - x‖ := by
    calc
      ‖P x - x‖ = ‖x - P x‖ := norm_sub_rev _ _
      _ = ⨅ w : C, ‖x - w‖ := by
        simpa [closedConvexProjectionPoint] using
          norm_sub_metricProjection_eq_iInf C hC_nonempty hC_closed.isComplete hC_convex x
      _ ≤ ‖x - (⟨y, hy⟩ : C)‖ := by
        let f : C → ℝ := fun w ↦ ‖x - w‖
        have hbound : BddBelow (Set.range f) := ⟨0, Set.forall_mem_range.2 fun _ ↦ norm_nonneg _⟩
        simpa [f] using ciInf_le hbound ⟨y, hy⟩
      _ = ‖y - x‖ := by rw [norm_sub_rev]
  have hsq : ‖P x - x‖ ^ (2 : ℕ) ≤ ‖y - x‖ ^ (2 : ℕ) := by
    nlinarith [hnorm, norm_nonneg (P x - x), norm_nonneg (y - x)]
  exact div_le_div_of_nonneg_right hsq (by positivity)

-- Proof sketch: the owner minimizer theorem gives one minimizing point, so any other feasible
-- minimizer has the same half squared-distance value. Since norms are nonnegative, equal squared
-- distances imply equal distances; uniqueness of the metric projection then identifies the point.
/-- Any feasible minimizer of the half squared-distance objective over a nonempty closed convex set
is the point projection onto that set. -/
theorem eq_closedConvexProjectionPoint_of_mem_isMinOn (x : E) {y : E} (hy : y ∈ C)
    (hmin : IsMinOn (fun z ↦ ‖z - x‖ ^ (2 : ℕ) / 2) C y) :
    y = P x := by
  have hy_le : ‖y - x‖ ^ (2 : ℕ) / 2 ≤ ‖P x - x‖ ^ (2 : ℕ) / 2 :=
    (isMinOn_iff.mp hmin) (P x) (closedConvexProjectionPoint_mem C hC_nonempty hC_closed hC_convex x)
  have hproj_le : ‖P x - x‖ ^ (2 : ℕ) / 2 ≤ ‖y - x‖ ^ (2 : ℕ) / 2 :=
    (isMinOn_iff.mp (closedConvexProjectionPoint_isMinOn C hC_nonempty hC_closed hC_convex x)) y hy
  have hsq : ‖y - x‖ ^ (2 : ℕ) = ‖P x - x‖ ^ (2 : ℕ) := by
    linarith [hy_le, hproj_le]
  have hnorm : ‖y - x‖ = ‖P x - x‖ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hnorm | hnorm
    · exact hnorm
    · nlinarith [norm_nonneg (y - x), norm_nonneg (P x - x), hnorm]
  exact eq_projectionPoint_of_mem_of_norm_eq C hC_nonempty hC_closed hC_convex x hy hnorm

end PointProjectionFacts

end
