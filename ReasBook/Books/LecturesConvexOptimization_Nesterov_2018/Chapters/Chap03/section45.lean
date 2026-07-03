import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_45 (from Chap03) -/
noncomputable section

open scoped BigOperators EuclideanOrthant

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

namespace ApproximateLagrangeMultiplierSwitchingMethod

variable {problem : ProjectedMultipleConstraintFirstOrderProblem E m}

/- Primary domain: approximate Lagrange multipliers attached to a run of the switching method in
Algorithm 3.4.

Relevant owner-style declarations sampled before refining:
- `ProjectedMultipleConstraintFirstOrderProblem.switchingActiveSet`
- `ApproximateLagrangeMultiplierSwitchingMethod.selectedIndexAt`
- `FirstOrderOracle.correctionStepsize`
- `EuclideanSpace.nonnegativeOrthant`
- `EuclideanSpace.mem_nonnegativeOrthant_iff`

Best owner abstraction:
- `source-facing`: the textbook objects `A₀(t)`, `Aⱼ(t)`, `N(t)`, `S_t`, `σ_t`, and `λ_t`
- `core/canonical`: a run `method : ApproximateLagrangeMultiplierSwitchingMethod problem`
  together with the chapter's canonical multiplier carrier `EuclideanSpace ℝ (Fin m)`
- `bridge/view`: coordinate and orthant lemmas for `λ_t`

Primitive data:
- the switching-method run `method`

Derived API:
- the iterate sequence `x_k`, active sets `𝒥_k`, chosen indices `j_k`, and selected branch
  scalars `h_k` already exposed by Algorithm 3.4 through `selectedIndexAt` and the owner
  correction scalar `(problem.constraintOracle j).correctionStepsize (method k)` on each selected
  branch
- the finite index sets `A₀(t)` and `Aⱼ(t)`, stored intrinsically as `Finset`s in
  `Fin (t + 1)`
- the direct finite sums over `A₀(t)` and `Aⱼ(t)` for `S_t` and `λ_t`, using the chapter owner
  reciprocal and correction scalars without a parallel wrapper API, but only under the explicit
  denominator regime that makes those ratios genuine textbook ratios rather than totalized values;
  the later normalized primal average is delegated downstream to the canonical `Finset.centerMass`
  owner on `A₀(t)` with those same weights
- the count `N(t)`
- the normalization sum `S_t`, defined under the explicit objective-denominator regime by the
  textbook finite reciprocal formula
- the scalar `σ_t = h S_t`, kept in its source-facing real form under that same regime
- positivity consequences such as `N(t) > 0 → S_t > 0`, recorded only as downstream lemmas with
  explicit nonvanishing hypotheses on the sampled objective subgradients
- the canonical multiplier vector `approximateDualMultiplier t : EuclideanSpace ℝ (Fin m)`,
  whose coordinates are the textbook real ratios `σ_t⁻¹ ∑_{k ∈ A_j(t)} h_k` under the full
  denominator regime for Definition 3.45
- its coordinate formula and positivity / orthant bridge lemmas under the textbook positivity
  regime

Accordingly this file keeps the source-facing objects of Definition 3.45, but derives them
directly from the switching-method owner data, uses the finite interval `Fin (t + 1)` and its
canonical finite-set API instead of a filtered `range` subset of `ℕ`, reuses the chapter owner
`FirstOrderOracle.correctionStepsize` rather than a parallel local stepsize wrapper, and makes
the denominator regime explicit in the public semantics of `S_t`, `σ_t`, and `λ_t` instead of
silently totalizing undefined textbook ratios to zero.
-/

/-- The index set `A₀(t) = {k ∈ {0, ..., t} : 𝒥_k = ∅}`. -/
def inactiveConstraintIndices
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) :
    Finset (Fin (t + 1)) :=
  Finset.univ.filter fun k ↦ method.activeSet k = ∅

/-- The index set `A_j(t) = {k ∈ {0, ..., t} : j_k = j}` for a fixed constraint coordinate `j`.
The chosen indices `j_k` are the ones produced by Algorithm 3.4 itself. -/
def selectedConstraintIndices
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) (j : Fin m) :
    Finset (Fin (t + 1)) :=
  Finset.univ.filter fun k ↦ method.selectedIndexAt k = some j

/- Source-facing Lean notation for the textbook index sets `A₀(t)` and `A_j(t)`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "A₀[" method:arg "](" t:arg ")" =>
  inactiveConstraintIndices method t

scoped notation:max "A[" method:arg "](" t:arg ", " j:arg ")" =>
  selectedConstraintIndices method t j

end ApproximateLagrangeMultiplierSwitchingNotation

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/-- Membership in `A₀(t)` is exactly the source condition `𝒥_k = ∅`. -/
@[simp]
theorem mem_inactiveConstraintIndices_iff
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    {k : Fin (t + 1)} :
    k ∈ A₀[method](t) ↔ method.activeSet k = ∅ := by
  simp [inactiveConstraintIndices]

/-- Membership in `A_j(t)` is exactly the source condition `j_k = j`. -/
@[simp]
theorem mem_selectedConstraintIndices_iff
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) (j : Fin m)
    {k : Fin (t + 1)} :
    k ∈ A[method](t, j) ↔ method.selectedIndexAt k = some j := by
  simp [selectedConstraintIndices]

/-- The counting function `N(t) = |A₀(t)|`. -/
def inactiveConstraintCount
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) : ℕ :=
  (A₀[method](t)).card

/- Source-facing Lean notation for the textbook count `N(t)`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "N[" method:arg "](" t:arg ")" =>
  inactiveConstraintCount method t

end ApproximateLagrangeMultiplierSwitchingNotation

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/-- The textbook denominator regime on `A₀(t)`: every sampled objective subgradient is nonzero,
so the reciprocal norms in `S_t` are genuine reciprocals rather than totalized values. -/
def HasObjectiveDenominators
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) : Prop :=
  ∀ ⦃k : Fin (t + 1)⦄, k ∈ A₀[method](t) → method.objectiveSubgradient k ≠ 0

/-- The textbook denominator regime on the selected-constraint side: every sampled selected
constraint subgradient is nonzero, so each correction scalar `h_k` is the genuine textbook ratio
`f_j(x_k) / ‖g_j(x_k)‖²`. -/
def HasSelectedConstraintDenominators
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) : Prop :=
  ∀ ⦃j : Fin m⦄ ⦃k : Fin (t + 1)⦄, k ∈ A[method](t, j) →
    (problem.constraintOracle j).subgradient (method k) ≠ 0

/-- The full denominator regime needed for the textbook multiplier `λ_t`: the reciprocal weights
on `A₀(t)` and the correction scalars on the selected-constraint indices are genuine ratios,
`h > 0`, and `N(t) > 0` so the normalizing factor `σ_t = h S_t` is nonzero. -/
def HasApproximateDualMultiplierDenominators
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) : Prop :=
  method.HasObjectiveDenominators t ∧
    method.HasSelectedConstraintDenominators t ∧
    0 < method.h ∧
    0 < N[method](t)

theorem HasApproximateDualMultiplierDenominators.objective
    {method : ApproximateLagrangeMultiplierSwitchingMethod problem} {t : ℕ}
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    method.HasObjectiveDenominators t :=
  hdenom.1

theorem HasApproximateDualMultiplierDenominators.selected
    {method : ApproximateLagrangeMultiplierSwitchingMethod problem} {t : ℕ}
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    method.HasSelectedConstraintDenominators t := by
  rcases hdenom with ⟨_, hselected, _, _⟩
  exact hselected

theorem HasApproximateDualMultiplierDenominators.h_pos
    {method : ApproximateLagrangeMultiplierSwitchingMethod problem} {t : ℕ}
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    0 < method.h := by
  rcases hdenom with ⟨_, _, hh, _⟩
  exact hh

theorem HasApproximateDualMultiplierDenominators.inactiveConstraintCount_pos
    {method : ApproximateLagrangeMultiplierSwitchingMethod problem} {t : ℕ}
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    0 < N[method](t) := by
  rcases hdenom with ⟨_, _, _, hN⟩
  exact hN

private def objectiveReciprocalWeight
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t)
    (k : {k : Fin (t + 1) // k ∈ A₀[method](t)}) : ℝ :=
  ↑((Units.mk0 ‖method.objectiveSubgradient k.1‖
      (norm_ne_zero_iff.mpr (hobjective k.2)))⁻¹ : ℝˣ)

private theorem objectiveReciprocalWeight_eq_inv_norm
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t)
    (k : {k : Fin (t + 1) // k ∈ A₀[method](t)}) :
    objectiveReciprocalWeight method t hobjective k = ‖method.objectiveSubgradient k.1‖⁻¹ := by
  simp [objectiveReciprocalWeight, Units.val_mk0]

/-- The normalization sum `S_t = ∑_{k ∈ A₀(t)} 1 / ‖g(x_k)‖`, defined under the textbook
nonvanishing regime `hobjective` so that each reciprocal is a genuine reciprocal norm. -/
def inverseSubgradientNormSum
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t) : ℝ :=
  Finset.sum (A₀[method](t)).attach (objectiveReciprocalWeight method t hobjective)

/-- A nonzero objective subgradient gives a strictly positive reciprocal norm weight. -/
theorem inv_norm_objectiveSubgradient_pos
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (k : ℕ)
    (hgrad_ne : method.objectiveSubgradient k ≠ 0) :
    0 < ‖method.objectiveSubgradient k‖⁻¹ := by
  simp [inv_pos, norm_pos_iff, hgrad_ne]

/- Source-facing Lean notation for the textbook normalization sum `S_t`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "S[" method:arg "](" t:arg "; " hobjective:arg ")" =>
  inverseSubgradientNormSum method t hobjective

end ApproximateLagrangeMultiplierSwitchingNotation

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/-- If no objective-step index occurs up to time `t`, then the reciprocal-norm sum `S_t`
vanishes. -/
theorem inverseSubgradientNormSum_eq_zero_of_inactiveConstraintCount_eq_zero
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t)
    (hN : N[method](t) = 0) :
    S[method](t; hobjective) = 0 := by
  have hcard : (A₀[method](t)).card = 0 := by
    simpa [inactiveConstraintCount] using hN
  have hattach : (A₀[method](t)).attach = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [Finset.card_attach] using hcard
  rw [inverseSubgradientNormSum, hattach]
  simp

/-- If `N(t) > 0`, then the reciprocal-norm sum `S_t` is strictly positive. -/
theorem inverseSubgradientNormSum_pos_of_inactiveConstraintCount_pos
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t)
    (hN : 0 < N[method](t)) :
    0 < S[method](t; hobjective) := by
  have hcard : 0 < (A₀[method](t)).card := by
    simpa [inactiveConstraintCount] using hN
  rw [inverseSubgradientNormSum]
  refine Finset.sum_pos' ?_ ?_
  · intro k hk
    exact le_of_lt <| by
      simpa [objectiveReciprocalWeight_eq_inv_norm] using
        method.inv_norm_objectiveSubgradient_pos k.1 (hobjective k.2)
  · rcases Finset.card_pos.mp hcard with ⟨k, hk⟩
    refine ⟨⟨k, hk⟩, by simp, ?_⟩
    simpa [objectiveReciprocalWeight_eq_inv_norm] using
      method.inv_norm_objectiveSubgradient_pos k (hobjective hk)

/-- The reciprocal-norm sum `S_t` is always nonnegative. -/
theorem inverseSubgradientNormSum_nonneg
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t) :
    0 ≤ S[method](t; hobjective) := by
  rw [inverseSubgradientNormSum]
  refine Finset.sum_nonneg fun k _ ↦ ?_
  exact le_of_lt <| by
    simpa [objectiveReciprocalWeight_eq_inv_norm] using
      method.inv_norm_objectiveSubgradient_pos k.1 (hobjective k.2)

/-- For Definition 3.45, the textbook gates `N(t) > 0` and `S_t > 0` are equivalent once the
objective-step denominators are known to be nonzero. -/
theorem inactiveConstraintCount_pos_iff_inverseSubgradientNormSum_pos
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t) :
    0 < N[method](t) ↔ 0 < S[method](t; hobjective) := by
  constructor
  · exact method.inverseSubgradientNormSum_pos_of_inactiveConstraintCount_pos t hobjective
  · intro hS
    by_contra hN
    have hN0 : method.inactiveConstraintCount t = 0 := Nat.eq_zero_of_not_pos hN
    have hS0 := method.inverseSubgradientNormSum_eq_zero_of_inactiveConstraintCount_eq_zero
      t hobjective hN0
    rw [hS0] at hS
    exact (lt_irrefl (0 : ℝ)) hS

/-- On a selected-constraint index, the chapter owner correction scalar is strictly positive. -/
theorem correctionStepsize_pos_of_selectedIndexAt_eq_some
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) {k : ℕ} {j : Fin m}
    (hh : 0 < method.h)
    (hsel : method.selectedIndexAt k = some j)
    (hgrad_ne : (problem.constraintOracle j).subgradient (method k) ≠ 0) :
    0 < (problem.constraintOracle j).correctionStepsize (method k) := by
  have hj : j ∈ method.activeSet k := by
    simpa [hsel] using method.selectedIndexAt_spec k
  have hnorm_pos : 0 < ‖(problem.constraintOracle j).subgradient (method k)‖ :=
    norm_pos_iff.mpr hgrad_ne
  have hthreshold :
      method.h * ‖(problem.constraintOracle j).subgradient (method k)‖ <
        problem.constraints j (method k) := by
    simpa [activeSet, ProjectedMultipleConstraintFirstOrderProblem.switchingActiveSet] using hj
  have hconstraint_pos : 0 < problem.constraints j (method k) :=
    lt_trans (mul_pos hh hnorm_pos) hthreshold
  simpa [FirstOrderOracle.correctionStepsize] using
    div_pos hconstraint_pos (pow_pos hnorm_pos _)

/-- The scalar `σ_t = h S_t`, kept in the textbook real-valued form under the objective
denominator regime `hobjective`. -/
def normalizingFactor
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t) : ℝ :=
  method.h * S[method](t; hobjective)

/- Source-facing Lean notation for the textbook normalizing factor `σ_t`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "σ[" method:arg "](" t:arg "; " hobjective:arg ")" =>
  normalizingFactor method t hobjective

end ApproximateLagrangeMultiplierSwitchingNotation

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/-- Positive `N(t)` forces the normalizing factor `σ_t = h S_t` to be positive. -/
theorem normalizingFactor_pos_of_inactiveConstraintCount_pos
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t)
    (hh : 0 < method.h)
    (hN : 0 < N[method](t)) :
    0 < σ[method](t; hobjective) := by
  rw [normalizingFactor]
  have hS : 0 < S[method](t; hobjective) :=
    method.inverseSubgradientNormSum_pos_of_inactiveConstraintCount_pos t hobjective hN
  exact mul_pos hh hS

/-- If `h > 0`, then the normalizing factor `σ_t = h S_t` is nonnegative. -/
theorem normalizingFactor_nonneg
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t)
    (hh : 0 < method.h) :
    0 ≤ σ[method](t; hobjective) := by
  rw [normalizingFactor]
  exact mul_nonneg hh.le (method.inverseSubgradientNormSum_nonneg t hobjective)

/-- Under the full denominator regime for Definition 3.45, the normalizing factor `σ_t` is
strictly positive. -/
theorem HasApproximateDualMultiplierDenominators.normalizingFactor_pos
    {method : ApproximateLagrangeMultiplierSwitchingMethod problem} {t : ℕ}
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    0 < σ[method](t; hdenom.objective) :=
  method.normalizingFactor_pos_of_inactiveConstraintCount_pos t hdenom.objective
    hdenom.h_pos hdenom.inactiveConstraintCount_pos

theorem HasApproximateDualMultiplierDenominators.normalizingFactor_ne_zero
    {method : ApproximateLagrangeMultiplierSwitchingMethod problem} {t : ℕ}
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    σ[method](t; hdenom.objective) ≠ 0 :=
  ne_of_gt hdenom.normalizingFactor_pos

private def selectedCorrectionWeight
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hselected : method.HasSelectedConstraintDenominators t) (j : Fin m)
    (k : {k : Fin (t + 1) // k ∈ A[method](t, j)}) : ℝ :=
  problem.constraints j (method k.1) /
    ↑(Units.mk0 (‖(problem.constraintOracle j).subgradient (method k.1)‖ ^ (2 : ℕ))
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (hselected k.2))) : ℝˣ)

private theorem selectedCorrectionWeight_eq_correctionStepsize
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hselected : method.HasSelectedConstraintDenominators t) (j : Fin m)
    (k : {k : Fin (t + 1) // k ∈ A[method](t, j)}) :
    selectedCorrectionWeight method t hselected j k =
      (problem.constraintOracle j).correctionStepsize (method k.1) := by
  simp [selectedCorrectionWeight, FirstOrderOracle.correctionStepsize, Units.val_mk0]

/-- Definition 3.45: for a run of Algorithm 3.4, the approximate dual multiplier vector
`λ_t` is the canonical multiplier vector in `EuclideanSpace ℝ (Fin m)` whose `j`th
coordinate is the textbook real ratio `λ_t^{(j)} = σ_t⁻¹ ∑_{k ∈ A_j(t)} h_k`, where
`A₀(t) = {k ≤ t : 𝒥_k = ∅}`,
`A_j(t) = {k ≤ t : j_k = j}`, `N(t) = |A₀(t)|`, `S_t = ∑_{k ∈ A₀(t)} 1 / ‖g(x_k)‖`, and
`σ_t = h S_t`. On `A_j(t)`, the chapter owner scalar
`(problem.constraintOracle j).correctionStepsize (method k)` is exactly the textbook `h_k`.
The owner is defined only under the full denominator regime `hdenom`, so all ratios are genuine
textbook ratios rather than totalized zero-division artifacts. Orthant membership and positivity
consequences belong to separate companion theorems. -/
def approximateDualMultiplier
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun j ↦
    (Finset.sum (A[method](t, j)).attach
      (selectedCorrectionWeight method t hdenom.selected j)) /
      ↑(Units.mk0 (σ[method](t; hdenom.objective))
        hdenom.normalizingFactor_ne_zero : ℝˣ)

/- Source-facing Lean notation for the textbook approximate multiplier `λ_t`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "λ[" method:arg "](" t:arg "; " hdenom:arg ")" =>
  approximateDualMultiplier method t hdenom

end ApproximateLagrangeMultiplierSwitchingNotation

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/-- Evaluating `λ[method](t; hdenom)` at coordinate `j` recovers the normalized finite sum over
`A_j(t)`. -/
@[simp]
theorem approximateDualMultiplier_apply
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t)
    (j : Fin m) :
    λ[method](t; hdenom) j =
      (Finset.sum (A[method](t, j)).attach fun k ↦
        (problem.constraintOracle j).correctionStepsize (method k.1)) /
        σ[method](t; hdenom.objective) :=
  by
    simp [approximateDualMultiplier, selectedCorrectionWeight_eq_correctionStepsize, Units.val_mk0]

/-- On a selected-constraint index, the chapter owner correction scalar `h_k` is nonnegative. -/
theorem correctionStepsize_nonneg_of_selectedIndexAt_eq_some
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) {k : ℕ} {j : Fin m}
    (hh : 0 < method.h)
    (hsel : method.selectedIndexAt k = some j) :
    0 ≤ (problem.constraintOracle j).correctionStepsize (method k) := by
  have hj : j ∈ method.activeSet k := by
    simpa [hsel] using method.selectedIndexAt_spec k
  have hthreshold :
      method.h * ‖(problem.constraintOracle j).subgradient (method k)‖ <
        problem.constraints j (method k) := by
    simpa [activeSet, ProjectedMultipleConstraintFirstOrderProblem.switchingActiveSet] using hj
  have hconstraint_pos : 0 < problem.constraints j (method k) := by
    have hmul_nonneg :
        0 ≤ method.h * ‖(problem.constraintOracle j).subgradient (method k)‖ := by
      positivity
    exact lt_of_le_of_lt hmul_nonneg hthreshold
  have hdenom_nonneg :
      0 ≤ ‖(problem.constraintOracle j).subgradient (method k)‖ ^ (2 : ℕ) := by
    positivity
  simpa [FirstOrderOracle.correctionStepsize] using
    div_nonneg (le_of_lt hconstraint_pos) hdenom_nonneg

/-- On a selected-constraint index, the chapter owner correction scalar `h_k` is nonnegative. -/
theorem correctionStepsize_nonneg_of_mem_selectedConstraintIndices
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    {j : Fin m} {k : Fin (t + 1)} (hk : k ∈ A[method](t, j)) (hh : 0 < method.h) :
    0 ≤ (problem.constraintOracle j).correctionStepsize (method k) := by
  exact method.correctionStepsize_nonneg_of_selectedIndexAt_eq_some hh
    ((mem_selectedConstraintIndices_iff method t j).1 hk)

/-- If `h > 0`, then every coordinate of `λ_t` is nonnegative. -/
theorem approximateDualMultiplier_nonneg
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t)
    (j : Fin m) :
    0 ≤ λ[method](t; hdenom) j := by
  rw [approximateDualMultiplier_apply]
  change 0 ≤
    (Finset.sum (A[method](t, j)).attach fun k ↦
      (problem.constraintOracle j).correctionStepsize (method k.1)) /
        σ[method](t; hdenom.objective)
  refine div_nonneg ?_ (le_of_lt hdenom.normalizingFactor_pos)
  refine Finset.sum_nonneg fun k hk ↦ ?_
  exact method.correctionStepsize_nonneg_of_mem_selectedConstraintIndices t k.2 hdenom.h_pos

/-- Under the full denominator regime for Definition 3.45, the approximate multiplier vector
`λ_t` lies in the nonnegative orthant `ℝ₊^m`. -/
theorem approximateDualMultiplier_mem_nonnegativeOrthant
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    (λ[method](t; hdenom)) ∈ ℝ₊^m := by
  simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using
    fun j ↦ method.approximateDualMultiplier_nonneg t hdenom j

end ApproximateLagrangeMultiplierSwitchingMethod

/-! ### Proposition_3_45 (from Chap03) -/
noncomputable section

universe u

open MeasureTheory

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "μ" => (Measure.addHaar : Measure E)
local notation "finDim" => Module.finrank ℝ E
local notation "δ" => 1 - 1 / (((finDim : ℝ) + 1) ^ (2 : ℕ))

attribute [local instance] Classical.decPred

/- Proposition 3.45 lies in the intrinsic finite-dimensional real normed-space
selected-feasible-index / interior-ball volume-decay domain.

Sampled owner-style declarations in the same domain:
- `Nat.count` and `feasibleSubsequence` from `Definition_3_53`, the chapter owners for the
  textbook selected feasible index `i(k)`;
- `selected_index_pos_of_volume_drop` from `Theorem_3_52`, the canonical bridge from strict
  comparison-set volume drop to positivity of that selected feasible index;
- `volume_ratio_rpow_decay_under_interior_ball_condition` from `Proposition_3_44`, the chapter's
  intrinsic bridge from interior-ball geometry and ellipsoid-style volume decay to the explicit
  exponential ratio bound;
- `Module.finrank`, the canonical owner of ambient dimension data replacing the coordinate
  parameter `n`;
- `Real.exp_lt_one_iff` and `Real.rpow_lt_one_iff'`, the canonical scalar owners that turn the
  logarithmic threshold into strict volume drop.

Best owner abstraction:
- source-facing: positivity of the canonical selected feasible index
  `Nat.count (fun j ↦ querySeq j ∈ Q) k`;
- core/canonical: `selected_index_pos_of_volume_drop` together with
  `volume_ratio_rpow_decay_under_interior_ball_condition`;
- bridge/view: the scalar threshold implication
  `(R / ρ) * exp (-k / (2 (finDim + 1)^2)) < 1`.

Primitive data:
- the finite-dimensional real normed ambient space `E` with `0 < Module.finrank ℝ E`;
- the feasible set `Q`, its radius-`ρ` interior-ball condition, and its containment in the outer
  ball `B₂(x0, R)`;
- the raw query sequence `querySeq`, the localization map `g`, the comparison set `E_k`, and the
  selected-stage Haar/Lebesgue-volume comparison with `E_k`;
- the standard ellipsoid-style ENNReal Haar/Lebesgue-volume decay bound for `E_k`;
- the logarithmic budget inequality
  `2 (Module.finrank ℝ E + 1)^2 log (R / ρ) < k`.

Derived API:
- the scalar inequality `(R / ρ) * exp (-k / (2 (finDim + 1)^2)) < 1`;
- strict Haar/Lebesgue-volume drop `μ (E_k) < μ Q`;
- positivity of the textbook selected feasible index via the canonical owner theorem
  `selected_index_pos_of_volume_drop`.

Source/core/bridge triage:
- source-facing: the positivity conclusion for `Nat.count (fun j ↦ querySeq j ∈ Q) k`;
- core/canonical: `Nat.count`, `selected_index_pos_of_volume_drop`, and
  `volume_ratio_rpow_decay_under_interior_ball_condition`;
- bridge/view: the scalar exponential-threshold lemma below.

The previous version kept this bridge pinned to the coordinate model
`E = EuclideanSpace ℝ (Fin n)` and exposed a separate finiteness binder for `volume (E_k)`. The
ambient owner from `Proposition_3_44` is already intrinsic, and the stagewise decay hypothesis is
more naturally primitive as a direct ENNReal Haar/Lebesgue-volume bound than as a real-volume
inequality plus a bookkeeping finiteness witness. This refinement separates the intrinsic
volume-drop core from the source-facing selected-index bridge: the strict-volume comparison lives
at the finite-dimensional real normed-space owner level, while the final positivity theorem
reintroduces the chapter localization family only where its inner-product-space API is genuinely
needed.
-/

/-- If `k` exceeds the logarithmic threshold `2 (d + 1)^2 log (R / ρ)`, then the scalar
exponential factor `(R / ρ) * exp (-k / (2 (d + 1)^2))` is strictly smaller than `1`. -/
theorem radiusRatio_exp_neg_lt_one_of_log_threshold
    {d k : ℕ} {ρ R : ℝ}
    (hk :
      (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log (R / ρ) < (k : ℝ)) :
    (R / ρ) * Real.exp (-((k : ℝ) / (2 * (((d : ℝ) + 1) ^ (2 : ℕ))))) < 1 := by
  by_cases hratio_pos : 0 < R / ρ
  · have hbound : Real.log (R / ρ) < (k : ℝ) / (2 * (((d : ℝ) + 1) ^ (2 : ℕ))) := by
      have hdenom_pos : 0 < 2 * (((d : ℝ) + 1) ^ (2 : ℕ)) := by
        positivity
      refine (lt_div_iff₀ hdenom_pos).2 ?_
      simpa [mul_assoc, mul_comm, mul_left_comm] using hk
    rw [← Real.exp_log hratio_pos, ← Real.exp_add]
    have hsum :
        Real.log (R / ρ) + -((k : ℝ) / (2 * (((d : ℝ) + 1) ^ (2 : ℕ)))) < 0 := by
      linarith
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
      mul_left_comm] using
      (Real.exp_lt_one_iff.mpr hsum)
  · have hratio_nonpos : R / ρ ≤ 0 := le_of_not_gt hratio_pos
    have hexp_pos : 0 < Real.exp (-((k : ℝ) / (2 * (((d : ℝ) + 1) ^ (2 : ℕ))))) :=
      Real.exp_pos _
    have hmul_nonpos :
        (R / ρ) * Real.exp (-((k : ℝ) / (2 * (((d : ℝ) + 1) ^ (2 : ℕ))))) ≤ 0 := by
      nlinarith
    exact lt_of_le_of_lt hmul_nonpos zero_lt_one

/-- The intrinsic volume-drop core of Proposition 3.45: in a finite-dimensional real normed space,
if `Q` satisfies the radius-`ρ` interior-ball condition, if `Q` lies in the outer ball
`B₂(x0, R)`, if `E_k` satisfies the standard ellipsoid-style stagewise volume decay, and if
`k > 2 (Module.finrank ℝ E + 1)^2 log (R / ρ)`, then `μ E_k < μ Q`. -/
theorem volume_drop_of_log_threshold_under_interior_ball_condition
    (hdim : 0 < finDim)
    {Q : Set E} {ρ : ℝ} (hQ : Q.SatisfiesInteriorBallCondition ρ)
    {Ek : Set E} {x0 : E} {R : ℝ} (k : ℕ)
    (hQ_subset : Q ⊆ Metric.closedBall x0 R)
    (hvol_decay :
      μ Ek ≤ ENNReal.ofReal (Real.rpow δ (((k * finDim : ℕ) : ℝ) / 2)) *
        μ (Metric.closedBall x0 R))
    (hk :
      (2 : ℝ) * (((finDim + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log (R / ρ) < (k : ℝ)) :
    μ Ek < μ Q := by
  rcases hQ with ⟨hρ, xBar, hball⟩
  have hQ : Q.SatisfiesInteriorBallCondition ρ := ⟨hρ, xBar, hball⟩
  have hxBar : xBar ∈ Q := hball (Metric.mem_ball_self hρ)
  have hR : 0 ≤ R := by
    have hxBar_ball : xBar ∈ Metric.closedBall x0 R := hQ_subset hxBar
    exact le_trans dist_nonneg (by simpa [Metric.mem_closedBall] using hxBar_ball)
  have hclosedBall_lt_top : μ (Metric.closedBall x0 R) < ⊤ := by
    simpa using (measure_closedBall_lt_top : μ (Metric.closedBall x0 R) < ⊤)
  have hQ_finite : μ Q ≠ ⊤ := by
    exact
      measure_ne_top_of_subset hQ_subset hclosedBall_lt_top.ne
  have hdecay_finite :
      ENNReal.ofReal (Real.rpow δ (((k * finDim : ℕ) : ℝ) / 2)) *
          μ (Metric.closedBall x0 R) ≠
        ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hclosedBall_lt_top.ne
  have hEk_finite : μ Ek ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hvol_decay hdecay_finite.lt_top)
  have hratio_decay_and_exp :=
    volume_ratio_rpow_decay_under_interior_ball_condition
      hdim hQ hR k hvol_decay
  have hratio_exp :
      Real.rpow (Measure.real μ Ek / Measure.real μ Q) (1 / (finDim : ℝ)) <
        1 := by
    refine lt_of_le_of_lt hratio_decay_and_exp.1 ?_
    exact lt_of_le_of_lt hratio_decay_and_exp.2
      (radiusRatio_exp_neg_lt_one_of_log_threshold hk)
  have hball_real_pos : 0 < Measure.real μ (Metric.ball xBar ρ) := by
    have hball_pos : 0 < μ (Metric.ball xBar ρ) :=
      Metric.measure_ball_pos μ xBar hρ
    have hball_lt_top : μ (Metric.ball xBar ρ) < ⊤ := by
      simpa using (measure_ball_lt_top : μ (Metric.ball xBar ρ) < ⊤)
    simpa [Measure.real] using
      ENNReal.toReal_pos hball_pos.ne' hball_lt_top.ne
  have hQ_pos : 0 < Measure.real μ Q := by
    exact
      lt_of_lt_of_le hball_real_pos
        (measureReal_mono hball hQ_finite)
  have hratio_lt_one : Measure.real μ Ek / Measure.real μ Q < 1 := by
    exact (Real.rpow_lt_one_iff' (by positivity) (by positivity)).1 hratio_exp
  have hEk_real_lt : Measure.real μ Ek < Measure.real μ Q := by
    exact (div_lt_one hQ_pos).1 hratio_lt_one
  exact
    (ENNReal.toReal_lt_toReal hEk_finite hQ_finite).1
      (by simpa [Measure.real] using hEk_real_lt)

section SourceFacing

variable [InnerProductSpace ℝ E]

/-- Proposition 3.45 as the source-facing selected-index bridge: let
`i(k) = Nat.count (fun j ↦ querySeq j ∈ Q) k` be the canonical selected feasible index attached to
the query sequence `querySeq`. If `Q` satisfies the radius-`ρ` interior-ball condition in a
finite-dimensional real inner-product space `E`, if `0 < Module.finrank ℝ E`, if `Q` lies in the
outer ball `B₂(x0, R)`, if the selected localization stage has volume at most `vol(E_k)`, if
`E_k` satisfies the standard ellipsoid-style stagewise volume decay, and if
`k > 2 (Module.finrank ℝ E + 1)^2 log (R / ρ)`, then `i(k) > 0`. The intrinsic normed-space core
is `volume_drop_of_log_threshold_under_interior_ball_condition`; the extra inner-product-space
assumption here comes only from the chapter owner `localizationSets`. -/
theorem selected_index_pos_of_log_threshold_under_interior_ball_condition
    (hdim : 0 < finDim)
    {Q : Set E} {ρ : ℝ} (hQ : Q.SatisfiesInteriorBallCondition ρ)
    {querySeq : ℕ → E} {g : E → E} {Ek : Set E} {x0 : E} {R : ℝ} (k : ℕ)
    (hQ_subset : Q ⊆ Metric.closedBall x0 R)
    (hstage :
      μ
          (localizationSets
            Q
            (feasibleSubsequence Q querySeq)
            (g ∘ feasibleSubsequence Q querySeq)
            (Nat.count (fun j ↦ querySeq j ∈ Q) k)) ≤
        μ Ek)
    (hvol_decay :
      μ Ek ≤ ENNReal.ofReal (Real.rpow δ (((k * finDim : ℕ) : ℝ) / 2)) *
        μ (Metric.closedBall x0 R))
    (hk :
      (2 : ℝ) * (((finDim + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * Real.log (R / ρ) < (k : ℝ)) :
    0 < Nat.count (fun j ↦ querySeq j ∈ Q) k := by
  let Ell : ℕ → Set E := fun _ ↦ Ek
  have hstage' :
      μ
          (localizationSets
            Q
            (feasibleSubsequence Q querySeq)
            (g ∘ feasibleSubsequence Q querySeq)
            (Nat.count (fun j ↦ querySeq j ∈ Q) k)) ≤
        μ (Ell k) := hstage
  have hEll_lt_Q : μ (Ell k) < μ Q := by
    simpa [Ell] using
      volume_drop_of_log_threshold_under_interior_ball_condition
        hdim hQ k hQ_subset hvol_decay hk
  exact selected_index_pos_of_volume_drop hstage' hEll_lt_Q

end SourceFacing

end

/-! ### Theorem_3_45 (from Chap03) -/
noncomputable section

universe u

open scoped WithTopConvexAnalysis

/- Theorem 3.45 lies in the constrained strong-convexity / bounded-sublevel / minimizer-existence
domain.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- mathlib `StrictConvexOn.eq_of_isMinOn`
- mathlib `LowerSemicontinuousOn.exists_isMinOn`
- mathlib `isCompact_of_isClosed_isBounded`
- project `constrainedSublevelSet` in `Definition_3_3`

Best owner abstraction:
- source-facing: bounded constrained sublevel sets and unique feasible minimizers for a positive
  strongly convex objective
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: the coercion of a real-valued objective `f : E → ℝ` to its canonical
  `WithTop ℝ`-valued view `((↑) : ℝ → WithTop ℝ) ∘ f` so that sublevel sets use the chapter owner
  `constrainedSublevelSet`

Primitive data:
- a feasible set `Q`, a real-valued objective `f`, and a strong-convexity modulus `μ`
- for attainment, the genuine extra data `IsClosed Q` and `LowerSemicontinuousOn f Q`
- for the source-facing bridge theorem, continuity of `f` on the closed feasible set

Derived API:
- boundedness of the constrained sublevel sets
- existence and uniqueness of a feasible minimizer
- the continuity-on-closed-set bridge to the lower-semicontinuous owner theorem

This file owns these consequences for `StrongConvexOn`. The only duplicate wheel in the previous
version was the raw set `Q ∩ {x | f x ≤ α}`, which is canonically the chapter owner
`constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α`. For attainment, the real extra input
after boundedness is only closedness of the feasible set together with lower semicontinuity of the
objective, so the main existence theorem is stated directly at that primitive layer. The textbook
continuous-on-closed-set formulation survives only as a thin bridge. -/

namespace StrongConvexOn

section BoundedSublevel

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Theorem 3.45: every constrained level set of a positive strongly convex real-valued objective
is bounded. -/
theorem isBounded_constrainedSublevelSet
    {Q : Set E} {f : E → ℝ} {μ α : ℝ}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ) :
    Bornology.IsBounded
      (constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) α) := sorry

end BoundedSublevel

section Existence

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- A positive strongly convex real-valued objective on a nonempty closed feasible set has a
unique feasible minimizer once the objective is lower semicontinuous on that feasible set. -/
theorem existsUnique_isMinOn_of_isClosed_lowerSemicontinuousOn
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hf_lower : LowerSemicontinuousOn f Q)
    (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) :
    ∃! x : E, x ∈ Q ∧ IsMinOn f Q x := by
  rcases hQ_nonempty with ⟨x₀, hx₀Q⟩
  let fTop : E → WithTop ℝ := ((↑) : ℝ → WithTop ℝ) ∘ f
  let S := constrainedSublevelSet Q fTop (f x₀)
  have hx₀S : x₀ ∈ S := by
    exact mem_constrainedSublevelSet_iff.2 ⟨hx₀Q, le_rfl⟩
  have hSQ : S ⊆ Q := by
    intro x hx
    exact (mem_constrainedSublevelSet_iff.mp hx).1
  have hS_closed : IsClosed S := by
    rw [show S = Q ∩ f ⁻¹' Set.Iic (f x₀) by
      ext x
      simp [S, fTop, Set.mem_Iic]]
    rw [lowerSemicontinuousOn_iff_preimage_Iic] at hf_lower
    obtain ⟨v, hv_closed, hv_eq⟩ := hf_lower (f x₀)
    rw [hv_eq]
    exact hQ_closed.inter hv_closed
  have hS_bounded : Bornology.IsBounded S := by
    simpa [S, fTop] using
      (hf.isBounded_constrainedSublevelSet hμ :
        Bornology.IsBounded
          (constrainedSublevelSet Q (((↑) : ℝ → WithTop ℝ) ∘ f) (f x₀)))
  have hS_compact : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  obtain ⟨x, hxS, hxMinS⟩ :=
    (hf_lower.mono hSQ).exists_isMinOn ⟨x₀, hx₀S⟩ hS_compact
  have hxQ : x ∈ Q :=
    hSQ hxS
  have hx_le_x₀ : f x ≤ f x₀ :=
    hxMinS hx₀S
  have hxMinQ : IsMinOn f Q x := by
    intro y hyQ
    by_cases hyS : y ∈ S
    · exact hxMinS hyS
    · have hy_gt : f x₀ < f y := by
        refine lt_of_not_ge ?_
        intro hy_le
        apply hyS
        refine mem_constrainedSublevelSet_iff.2 ⟨hyQ, ?_⟩
        simpa [fTop] using hy_le
      exact (le_trans hx_le_x₀ hy_gt.le)
  refine ⟨x, ⟨hxQ, hxMinQ⟩, ?_⟩
  intro y hy
  exact (hf.strictConvexOn hμ).eq_of_isMinOn hy.2 hxMinQ hy.1 hxQ

/-- A positive strongly convex real-valued objective that is continuous on a nonempty closed
feasible set has a unique feasible minimizer. -/
theorem existsUnique_isMinOn_of_isClosed
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hf_cont : ContinuousOn f Q)
    (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) :
    ∃! x : E, x ∈ Q ∧ IsMinOn f Q x := by
  exact hf.existsUnique_isMinOn_of_isClosed_lowerSemicontinuousOn hμ
    hf_cont.lowerSemicontinuousOn hQ_nonempty hQ_closed

end Existence

section Uniqueness

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive strongly convex real-valued objective on a feasible set has at most one feasible
minimizer. -/
theorem eq_of_isMinOn
    {Q : Set E} {μ : ℝ} {f : E → ℝ} (hf : StrongConvexOn Q μ f) (hμ : 0 < μ)
    {xStar₁ xStar₂ : E}
    (hxStar₁ : xStar₁ ∈ Q) (hmin₁ : IsMinOn f Q xStar₁)
    (hxStar₂ : xStar₂ ∈ Q) (hmin₂ : IsMinOn f Q xStar₂) :
    xStar₁ = xStar₂ :=
  (hf.strictConvexOn hμ).eq_of_isMinOn hmin₁ hmin₂ hxStar₁ hxStar₂

end Uniqueness

end StrongConvexOn

end
