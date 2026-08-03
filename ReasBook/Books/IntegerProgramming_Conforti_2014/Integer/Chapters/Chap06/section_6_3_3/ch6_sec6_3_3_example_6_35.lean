import Mathlib.Analysis.Convex.Gauge
import Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_definition_6_3_2_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this runner, so this file keeps the source-facing one-dimensional `R_f` formulas
-- on `ℝ` while reusing the chapter's canonical `q = 1` continuous-relaxation owners.

noncomputable section

section Example635

open scoped IntegerVectorNotation

local notation "R1" => Fin 1 → ℝ
local notation "ContAssignment" => ℝ →₀ NNReal

private def realAsR1 : ℝ ≃ R1 where
  toFun r := fun _ ↦ r
  invFun r := r 0
  left_inv r := rfl
  right_inv r := by
    ext i
    fin_cases i
    rfl

private abbrev scalarContAssignmentEquiv : ContAssignment ≃ (R1 →₀ NNReal) :=
  Finsupp.equivCongrLeft realAsR1

private theorem scalarContAssignmentEquiv_sum_apply_zero
    (y : ContAssignment) :
    (scalarContAssignmentEquiv y).sum (fun r a ↦ (a : ℝ) * r 0) =
      y.sum (fun r a ↦ (a : ℝ) * r) := by
  rw [scalarContAssignmentEquiv, Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain]
  rw [Finsupp.sum_mapDomain_index]
  · simp [realAsR1]
  · intro r
    simp
  · intro r a₁ a₂
    rw [NNReal.coe_add, add_mul]

private theorem scalarContAssignmentEquiv_weighted_sum_apply_zero
    (ψ : ℝ → ℝ) (y : ContAssignment) :
    (scalarContAssignmentEquiv y).sum (fun r a ↦ ψ (r 0) * (a : ℝ)) =
      y.sum (fun r a ↦ ψ r * (a : ℝ)) := by
  rw [scalarContAssignmentEquiv, Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain]
  rw [Finsupp.sum_mapDomain_index]
  · simp [realAsR1]
  · intro r
    simp
  · intro r a₁ a₂
    rw [NNReal.coe_add, left_distrib]

private theorem continuousInfiniteBalance_scalarContAssignmentEquiv_apply_zero
    (f : ℝ) (y : ContAssignment) :
    continuous_infinite_balance (fun _ : Fin 1 ↦ f) (scalarContAssignmentEquiv y) 0 =
      f + y.sum (fun r a ↦ (a : ℝ) * r) := by
  rw [continuous_infinite_balance_apply, scalarContAssignmentEquiv_sum_apply_zero]

/-- The one-dimensional continuous infinite relaxation `R_f`, consisting of finitely supported
nonnegative coefficient families whose weighted sum with `f` is integral. This is the `q = 1`
specialization of the chapter's canonical feasible-set owner. -/
abbrev continuous_infinite_relaxation_feasible_set_on_R (f : ℝ) : Set ContAssignment :=
  scalarContAssignmentEquiv ⁻¹' continuous_infinite_relaxation_feasible_set (fun _ : Fin 1 ↦ f)

/-- Membership in `continuous_infinite_relaxation_feasible_set_on_R f` is exactly the
one-dimensional integrality condition from `R_f`. -/
theorem mem_continuous_infinite_relaxation_feasible_set_on_R_iff
    {f : ℝ} {y : ContAssignment} :
    y ∈ continuous_infinite_relaxation_feasible_set_on_R f ↔
      ∃ z : ℤ, f + y.sum (fun r a ↦ (a : ℝ) * r) = (z : ℝ) := by
  change scalarContAssignmentEquiv y ∈ continuous_infinite_relaxation_feasible_set
      (fun _ : Fin 1 ↦ f) ↔ _
  rw [mem_continuous_infinite_relaxation_feasible_set_iff, mem_integerVectors_iff_forall]
  constructor
  · intro hy
    rcases (show ∃ z : ℤ,
      (z : ℝ) =
        continuous_infinite_balance (fun _ : Fin 1 ↦ f) (scalarContAssignmentEquiv y) 0 from
      hy 0) with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa [continuousInfiniteBalance_scalarContAssignmentEquiv_apply_zero] using hz.symm
  · rintro ⟨z, hz⟩ i
    fin_cases i
    refine ⟨z, ?_⟩
    simpa [continuousInfiniteBalance_scalarContAssignmentEquiv_apply_zero] using hz.symm

/-- A function `ψ : ℝ → ℝ` is valid for the one-dimensional continuous infinite relaxation when
its cut inequality holds on every feasible point of `R_f`. This is the `q = 1` specialization of
the chapter's canonical continuous-valid-function owner. -/
abbrev IsValidFunctionForContinuousInfiniteRelaxationOnR
    (f : ℝ) (ψ : ℝ → ℝ) : Prop :=
  IsValidFunctionForContinuousInfiniteRelaxation (fun _ : Fin 1 ↦ f) (fun r : R1 ↦ ψ (r 0))

/-- Unfolding the one-dimensional valid-function owner recovers the canonical `q = 1` chapter
owner. -/
theorem isValidFunctionForContinuousInfiniteRelaxationOnR_iff
    {f : ℝ} {ψ : ℝ → ℝ} :
    IsValidFunctionForContinuousInfiniteRelaxationOnR f ψ ↔
      IsValidFunctionForContinuousInfiniteRelaxation
        (fun _ : Fin 1 ↦ f) (fun r : R1 ↦ ψ (r 0)) :=
  Iff.rfl

/-- A one-dimensional valid function satisfies the defining inequality on every feasible point of
`R_f`. -/
theorem continuous_infinite_valid_function_on_R_one_le
    {f : ℝ} {ψ : ℝ → ℝ}
    (hψ : IsValidFunctionForContinuousInfiniteRelaxationOnR f ψ)
    {y : ContAssignment}
    (hy : y ∈ continuous_infinite_relaxation_feasible_set_on_R f) :
    1 ≤ y.sum (fun r a ↦ ψ r * (a : ℝ)) := by
  change scalarContAssignmentEquiv y ∈ continuous_infinite_relaxation_feasible_set
      (fun _ : Fin 1 ↦ f) at hy
  simpa [scalarContAssignmentEquiv_weighted_sum_apply_zero] using
    continuous_infinite_valid_function_one_le hψ hy

/-- A valid function for the one-dimensional continuous infinite relaxation is minimal when every
valid function lying pointwise below it is equal to it. This is the `q = 1` specialization of the
chapter's canonical minimal-valid-function owner. -/
abbrev IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR
    (f : ℝ) (ψ : ℝ → ℝ) : Prop :=
  IsMinimalValidFunctionForContinuousInfiniteRelaxation
    (fun _ : Fin 1 ↦ f) (fun r : R1 ↦ ψ (r 0))

/-- Unfolding the one-dimensional minimal-valid-function owner recovers the canonical `q = 1`
chapter owner. -/
theorem isMinimalValidFunctionForContinuousInfiniteRelaxationOnR_iff
    {f : ℝ} {ψ : ℝ → ℝ} :
    IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ ↔
      IsMinimalValidFunctionForContinuousInfiniteRelaxation
        (fun _ : Fin 1 ↦ f) (fun r : R1 ↦ ψ (r 0)) :=
  Iff.rfl

/-- A minimal valid function on `ℝ` is valid. -/
instance instIsValidFunctionForContinuousInfiniteRelaxationOnROfMinimal
    {f : ℝ} {ψ : ℝ → ℝ}
    [hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ] :
    IsValidFunctionForContinuousInfiniteRelaxationOnR f ψ :=
  hψ.toIsValidFunctionForContinuousInfiniteRelaxation

/-- Minimality on `R_f` can be used through pointwise domination by another valid function. -/
theorem isMinimalValidFunctionForContinuousInfiniteRelaxationOnR_eq_of_le
    {f : ℝ} {ψ ψ' : ℝ → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ)
    (hψ' : IsValidFunctionForContinuousInfiniteRelaxationOnR f ψ')
    (hle : ∀ r : ℝ, ψ' r ≤ ψ r) :
    ψ' = ψ := by
  have hle' : ∀ r : R1, ψ' (r 0) ≤ ψ (r 0) := fun r ↦ hle (r 0)
  have hEq : (fun r : R1 ↦ ψ' (r 0)) = fun r : R1 ↦ ψ (r 0) :=
    continuous_infinite_minimal_valid_function_eq_of_le hψ hψ' hle'
  ext r
  exact congrFun hEq (fun _ ↦ r)

/-- A function strictly above a minimal valid function at some point cannot itself be minimal for
the one-dimensional continuous infinite relaxation. -/
theorem not_minimal_of_strictly_dominated_by_minimal_on_R
    {f : ℝ} {ψ₀ ψ : ℝ → ℝ}
    (hψ₀ : IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ₀)
    (hle : ∀ r : ℝ, ψ₀ r ≤ ψ r)
    (hstrict : ∃ r : ℝ, ψ₀ r < ψ r) :
    ¬ IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ := by
  intro hψ
  have hvalid₀ : IsValidFunctionForContinuousInfiniteRelaxationOnR f ψ₀ :=
    hψ₀.toIsValidFunctionForContinuousInfiniteRelaxation
  have hEq := isMinimalValidFunctionForContinuousInfiniteRelaxationOnR_eq_of_le hψ hvalid₀ hle
  rcases hstrict with ⟨r, hr⟩
  have hEval : ψ₀ r = ψ r := congrArg (fun φ : ℝ → ℝ ↦ φ r) hEq
  have hnot : ¬ ψ₀ r < ψ r := by
    simp [hEval]
  exact hnot hr

/-- The translated interval `B - f = [-f, 1 - f]` from Example 6.35, where `B = [0,1]`. -/
def example_6_35_shifted_unit_interval (f : ℝ) : Set ℝ :=
  Set.Icc (-f) (1 - f)

/-- The function `ψ₀` from Example 6.35, written as the piecewise-linear function attached to the
slopes of the interval gauge. -/
def example_6_35_psi_zero (f : ℝ) : ℝ → ℝ :=
  fun r ↦
    if 0 ≤ r then
      r / (1 - f)
    else
      -r / f

/-- Expanding `example_6_35_psi_zero f` recovers its displayed piecewise formula. -/
@[simp] theorem example_6_35_psi_zero_apply
    (f r : ℝ) :
    example_6_35_psi_zero f r =
      if 0 ≤ r then
        r / (1 - f)
      else
        -r / f :=
  rfl

/-- Example 6.35 (1). Under the effective interval hypothesis `0 < f < 1` implied by the
source assumptions `0 < t` and `t + 1/2 < f < 1`, the function `ψ₀` is the gauge of the
translated interval `B - f = [-f, 1 - f]`, where `B = [0,1]`. -/
theorem example_6_35_psi_zero_eq_gauge
    {f : ℝ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    example_6_35_psi_zero f = gauge (example_6_35_shifted_unit_interval f) := sorry

/-- Example 6.35 (2). Under the effective interval hypothesis `0 < f < 1` implied by the source
assumptions of Example 6.35, `ψ₀` is a minimal valid function for the one-dimensional continuous
infinite relaxation `R_f`. -/
theorem example_6_35_psi_zero_is_minimal_for_Rf
    {f : ℝ}
    (hf0 : 0 < f)
    (hf1 : f < 1) :
    IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f (example_6_35_psi_zero f) := sorry

/-- Under the source hypotheses of Example 6.35, `example_6_35_psi_zero f` is available through
the canonical one-dimensional continuous-relaxation minimal-valid-function instance. -/
instance instExample635PsiZeroMinimalForRf
    {f : ℝ} [Fact (0 < f)] [Fact (f < 1)] :
    IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f (example_6_35_psi_zero f) :=
  example_6_35_psi_zero_is_minimal_for_Rf
    ‹Fact (0 < f)›.out ‹Fact (f < 1)›.out

/-- Example 6.35 (3). Under the effective interval hypothesis `0 < f < 1` implied by the source
assumptions of Example 6.35, any two functions `ψ₁` and `ψ₂` lying pointwise above `ψ₀` and
strictly above it somewhere are not minimal valid functions for `R_f`; this captures the source
conclusion for the liftings attached to `π₁` and `π₂`. -/
theorem example_6_35_psi_one_two_not_minimal_for_Rf
    {f : ℝ}
    (hf0 : 0 < f)
    (hf1 : f < 1)
    {ψ₁ ψ₂ : ℝ → ℝ}
    (hψ₁_ge : ∀ r : ℝ, example_6_35_psi_zero f r ≤ ψ₁ r)
    (hψ₂_ge : ∀ r : ℝ, example_6_35_psi_zero f r ≤ ψ₂ r)
    (hψ₁_strict : ∃ r : ℝ, example_6_35_psi_zero f r < ψ₁ r)
    (hψ₂_strict : ∃ r : ℝ, example_6_35_psi_zero f r < ψ₂ r) :
    ¬ IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ₁ ∧
      ¬ IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f ψ₂ := by
  have hψ₀ :
      IsMinimalValidFunctionForContinuousInfiniteRelaxationOnR f (example_6_35_psi_zero f) := by
    letI : Fact (0 < f) := ⟨hf0⟩
    letI : Fact (f < 1) := ⟨hf1⟩
    infer_instance
  constructor
  · exact not_minimal_of_strictly_dominated_by_minimal_on_R hψ₀ hψ₁_ge hψ₁_strict
  · exact not_minimal_of_strictly_dominated_by_minimal_on_R hψ₀ hψ₂_ge hψ₂_strict

end Example635
