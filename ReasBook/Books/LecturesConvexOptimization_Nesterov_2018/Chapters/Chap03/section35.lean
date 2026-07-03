import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_35 (from Chap03) -/
noncomputable section

/-
Definition 3.35 lies in the finite-dimensional Euclidean Nemirovski hard-instance domain.

Primary domain:
- the nonsmooth strongly-convex hard-instance objective on `ℝⁿ` and the chapter's finite-family
  pointwise-supremum owner for its prefix-coordinate term.

Sampled owner-style declarations:
- `pointwiseSupremumOn` in `Chap03/PointwiseSupremumOn`, the chapter owner for subset-indexed
  pointwise suprema;
- `activePointwiseSupremumOnIndices` in `Chap03/Lemma_3_1_14`, the matching active-index owner
  used later for the prefix-coordinate view;
- `subdifferential_coordinatewiseMaximum_eq_convexHull_activeBasis` in `Chap03/Proposition_3_15`,
  the coordinate-maximum specialization that later feeds the Nemirovski subdifferential formula;
- the hard-instance minimizer API in `Chap03/Proposition_3_30`, which should depend on the owner
  objective rather than define it.

Best owner abstraction:
- source-facing: `f_k`
- core/canonical support: `pointwiseSupremumOn` and `activePointwiseSupremumOnIndices`

Primitive data:
- the ambient dimension `n`
- the active-coordinate length `k`
- the hard-instance parameters `μ` and `γ`

Derived API:
- the prefix-index type `FirstKIndex`
- the restricted coordinate family `firstKCoordinateFamily`
- the real-valued bridge `first_k_coordinate_max`
- the active-index and active-basis descriptions obtained from the generic pointwise-supremum
  owner and used in later Chapter 3 oracle files
- the minimizer and optimal-value API in `Proposition_3_30`

Source/core/bridge triage:
- source-facing: the textbook hard-instance objective `f_k`
- core/canonical: `pointwiseSupremumOn` and `activePointwiseSupremumOnIndices` for the
  prefix-coordinate family
- bridge/view: the real-valued prefix maximum `first_k_coordinate_max`

The earlier refinement put the source-facing owner `f_k` in the later proposition file
`Proposition_3_30` and left this definition file as a recall. That owner direction was wrong:
Definition 3.35 is the place where the hard objective itself is introduced, while
`Proposition_3_30` should only add the explicit minimizer and optimal-value API. This file
therefore owns the source-facing objective `f_k`, but its prefix-coordinate term is now a thin
bridge of the chapter pointwise-supremum owner rather than a separate set-theoretic supremum.
-/

section PrefixCoordinates

variable {n k : ℕ}

/-- The indices of the first `k` coordinates inside `Fin n`. -/
abbrev FirstKIndex (n k : ℕ) := {i : Fin n // i.1 < k}

/-- The coordinate family restricted to the first `k` coordinates of `ℝ^n`. -/
def firstKCoordinateFamily (n k : ℕ) :
    EuclideanSpace ℝ (Fin n) → FirstKIndex n k → WithTop ℝ :=
  fun x i ↦ (x i.1 : WithTop ℝ)

/-- The type of first-`k` coordinate indices is nonempty whenever `0 < k ≤ n`. -/
theorem firstKIndex_nonempty (hk : 0 < k) (hkn : k ≤ n) :
    Nonempty (FirstKIndex n k) := by
  exact ⟨⟨⟨0, lt_of_lt_of_le hk hkn⟩, hk⟩⟩

attribute [local instance] Classical.propDecidable

/-- The maximum among the first `k` coordinates of a vector in `ℝ^n`, viewed as the real-valued
bridge of the chapter `Set.univ` pointwise-supremum specialization on the restricted coordinate
family. -/
def first_k_coordinate_max (n k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if h : Nonempty (FirstKIndex n k) then
    let _ : Nonempty (FirstKIndex n k) := h
    (pointwiseSupremumOn (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x).untopD 0
  else
    0

/-- Helper for Definition 3.35: in the nonempty prefix case, the chapter pointwise-supremum owner
for the restricted coordinate family is finite. -/
lemma pointwiseSupremumOn_univ_firstKCoordinateFamily_lt_top
    [Nonempty (FirstKIndex n k)] (x : EuclideanSpace ℝ (Fin n)) :
    pointwiseSupremumOn (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x <
      (⊤ : WithTop ℝ) := by
  -- Rewrite the owner supremum as the usual finite supremum over the prefix coordinates.
  rw [pointwiseSupremumOn_univ_eq_sup']
  -- Every restricted coordinate slice is a coerced real number, hence strictly below `⊤`.
  have hlt :
      Finset.univ.sup' Finset.univ_nonempty (firstKCoordinateFamily n k x) < (⊤ : WithTop ℝ) ↔
        ∀ i ∈ Finset.univ, firstKCoordinateFamily n k x i < ⊤ := by
    rw [Finset.sup'_lt_iff]
  exact hlt.mpr fun i hi ↦ by
    simp [firstKCoordinateFamily]

/-- When `FirstKIndex n k` is nonempty, the `Set.univ` specialization of the chapter pointwise
supremum owner for the restricted coordinate family is the coercion of
`first_k_coordinate_max`. -/
theorem coe_first_k_coordinate_max_eq_pointwiseSupremumOn_univ
    [Nonempty (FirstKIndex n k)] (x : EuclideanSpace ℝ (Fin n)) :
    ((first_k_coordinate_max n k x : ℝ) : WithTop ℝ) =
      pointwiseSupremumOn (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x := by
  -- Rewrite `first_k_coordinate_max` into its nonempty branch.
  let h : Nonempty (FirstKIndex n k) := inferInstance
  rw [first_k_coordinate_max, dif_pos h]
  simp only
  let s : WithTop ℝ :=
    pointwiseSupremumOn (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x
  have hfinite :
      s < (⊤ : WithTop ℝ) := by
    simpa [s] using pointwiseSupremumOn_univ_firstKCoordinateFamily_lt_top (n := n) (k := k) x
  have hne : s ≠ (⊤ : WithTop ℝ) :=
    ne_of_lt hfinite
  -- Finiteness lets `untopD` recover the original `WithTop` value.
  change ↑(s.untopD 0) = s
  cases hs : s
  · exact (hne hs).elim
  · simp

/-- When `FirstKIndex n k` is nonempty, a prefix index is active exactly when its coordinate
attains `first_k_coordinate_max n k x`. -/
@[simp] theorem mem_activePointwiseSupremumOnIndices_firstKCoordinateFamily_iff
    [Nonempty (FirstKIndex n k)] {x : EuclideanSpace ℝ (Fin n)} {i : FirstKIndex n k} :
    i ∈ activePointwiseSupremumOnIndices
      (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x ↔
      x i.1 = first_k_coordinate_max n k x := by
  -- Activity on `Set.univ` means that the slice attains the owner supremum value.
  rw [mem_activePointwiseSupremumOnIndices_univ_iff]
  constructor
  · intro hi
    -- Unfold the restricted-coordinate family to return to the textbook coordinate equality.
    rw [← coe_first_k_coordinate_max_eq_pointwiseSupremumOn_univ (n := n) (k := k) (x := x)] at hi
    simpa [firstKCoordinateFamily] using hi
  · intro hi
    rw [← coe_first_k_coordinate_max_eq_pointwiseSupremumOn_univ (n := n) (k := k) (x := x)]
    -- The converse is the same rewrite in the opposite direction.
    simpa [firstKCoordinateFamily] using hi

end PrefixCoordinates

/-- Definition 3.35: the Nemirovski hard-instance objective
`f_k(x) = (μ / 2) ‖x‖^2 + γ max{x^(1), …, x^(k)}` on `ℝ^n`. -/
def f_k (n k : ℕ) (μ γ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (μ / 2) * ‖x‖ ^ 2 + γ * first_k_coordinate_max n k x

/-- Unfolding `f_k` gives its quadratic-plus-prefix-maximum formula. -/
-- Proof sketch: this is the defining equation of `f_k`, so the claim is by unfolding the
-- definition.
@[simp] theorem f_k_def
    (n k : ℕ) (μ γ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    f_k n k μ γ x =
      (μ / 2) * ‖x‖ ^ 2 + γ * first_k_coordinate_max n k x :=
  rfl

/-! ### Lemma_3_35 (from Chap03) -/
section

open scoped LevelMethodNotation

/- Lemma 3.35 lies in the chapter's level-method scalar-history domain.

Sampled owner declarations:
- `LevelMethodHistory` in `Lemma_3_3_1`, the owner bundle for `(\hat f_k^*, f_k^*)`
- `LevelMethodHistory.gap` in `Lemma_3_3_1`, the canonical gap `δ_k`
- the notation `δ[history](k)` in `Lemma_3_3_1`, the source-facing surface for those gaps
- `LevelMethodHistory.levelValue_eq_optimal_sub_one_sub_alpha_mul_gap` in `Lemma_3_3_1`, the
  nearby owner-level scalar rewrite using the same `1 - α` gap factor

Best owner abstraction:
- `LevelMethodHistory` with derived gap sequence `δ[history](k)`

Primitive data:
- `history.approximateOptimalValue`
- `history.optimalValue`

Derived API:
- `history.gap`
- the notation `δ[history](k)`

Source/core/bridge triage:
- source-facing: the scalar bound on the drop from `δ_k` to `δ_p`
- core/canonical: the gap owner `LevelMethodHistory.gap`
- bridge/view: this file's one-line inequality consequence on the owner-derived gap values

The previous declaration exposed a raw sequence `δ : ℕ → ℝ`, duplicating the chapter owner for
these scalar quantities. This file now states the same inequality directly for the canonical gap
API, with no change in mathematical content.
-/

namespace LevelMethodHistory

/-- Lemma 3.35: if the later gap satisfies `δ_p ≥ (1 - α) δ_k`, then the gap drop
`δ_k - δ_p` is bounded above by `α δ_k`. -/
-- Proof sketch: rearrange the target inequality
-- `δ_k - δ_p ≤ α δ_k` to `(1 - α) δ_k ≤ δ_p`, which is exactly the hypothesis.
lemma gap_drop_le_alpha_mul_gap_of_gap_ge_one_sub_alpha_mul_gap
    (history : LevelMethodHistory) {k p : ℕ} {α : ℝ}
    (hgap : δ[history](p) ≥ (1 - α) * δ[history](k)) :
    δ[history](k) - δ[history](p) ≤ α * δ[history](k) := by
  linarith

end LevelMethodHistory

end

/-! ### Proposition_3_35 (from Chap03) -/
noncomputable section

open scoped BigOperators EuclideanOrthant

local notation "E" N => EuclideanSpace ℝ (Fin (N + 1))

/-
Primary domain: finite-dimensional Euclidean stepsize optimization on the strict orthant.

Sampled owner-style declarations:
- `EuclideanSpace.nonnegativeOrthant` in `Chap01/Definition_1_10_2`, the chapter owner for the
  coordinatewise orthant domain in `EuclideanSpace ℝ (Fin m)`
- `EuclideanSpace.mem_nonnegativeOrthant_iff`, the corresponding coordinatewise membership bridge
- `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` in
  `Chap01/Definition_1_10_2`, the dimension-based strict orthant owner and membership bridge
- `orthantLogarithmicBarrierDomain` and `mem_orthantLogarithmicBarrierDomain_iff` in
  `Chap07/Definition_7_76`, a later strict-orthant owner with the same coordinatewise positivity
  surface

Best owner abstraction:
- `source-facing`: the scalar functional `deltaN` from Proposition 3.35 and its constant stepsize
  minimizer
- `core/canonical`: the strict orthant owner `EuclideanSpace.positiveOrthant`
- `bridge/view`: the coordinatewise membership and evaluation lemmas

Primitive data:
- the horizon `N`
- the radius `R`
- the stepsize vector `h : E N`

Derived API:
- coordinatewise positivity of the orthant domain
- the defining quotient formula for `deltaN`
- the constant-choice vector and its coordinate formula
- the minimization statement on the strict orthant
-/

/-- The function `Δ_N(h₀, …, h_N) = (R² + ∑ hᵢ²) / (2 ∑ hᵢ)` from Proposition 3.35. -/
def deltaN (N : ℕ) (R : ℝ) (h : E N) : ℝ :=
  (R ^ (2 : ℕ) + ∑ i : Fin (N + 1), h i ^ (2 : ℕ)) /
    (2 * ∑ i : Fin (N + 1), h i)

namespace DeltaN

/- Source-facing Lean notation for the textbook finite-horizon stepsize scalar `Δ_N(h₀, …, h_N)`,
with the ambient radius parameter displayed as `Δ[N; R] h`. -/
scoped notation:max "Δ[" N:arg "; " R:arg "]" => deltaN N R

end DeltaN

open scoped DeltaN

/-- Evaluating `deltaN` gives the defining quotient
`(R² + ∑ hᵢ²) / (2 ∑ hᵢ)`. -/
@[simp] theorem deltaN_apply (N : ℕ) (R : ℝ) (h : E N) :
    Δ[N; R] h =
      (R ^ (2 : ℕ) + ∑ i : Fin (N + 1), h i ^ (2 : ℕ)) /
        (2 * ∑ i : Fin (N + 1), h i) :=
  rfl

/-- The constant point with every coordinate equal to `R / √(N + 1)`. -/
def deltaNConstantChoice (N : ℕ) (R : ℝ) : E N :=
  (EuclideanSpace.equiv (Fin (N + 1)) ℝ).symm
    (Function.const _ (R / Real.sqrt (N + 1 : ℝ)))

/-- Every coordinate of `deltaNConstantChoice N R` is `R / √(N + 1)`. -/
@[simp] theorem deltaNConstantChoice_apply (N : ℕ) (R : ℝ) (i : Fin (N + 1)) :
    deltaNConstantChoice N R i = R / Real.sqrt (N + 1 : ℝ) := by
  simp [deltaNConstantChoice]

/-- Evaluating `deltaN` at the canonical constant choice gives `R / √(N + 1)`. -/
@[simp] theorem deltaN_constantChoice (N : ℕ) (R : ℝ) :
    Δ[N; R] (deltaNConstantChoice N R) = R / Real.sqrt (N + 1 : ℝ) := by
  have hs : Real.sqrt (N + 1 : ℝ) ≠ 0 := by
    positivity
  have hsq : Real.sqrt (N + 1 : ℝ) ^ (2 : ℕ) = N + 1 := by
    rw [Real.sq_sqrt]
    positivity
  simp [deltaN, Finset.sum_const, pow_two]
  field_simp [hs]
  rw [hsq]
  ring_nf

/-- The constant choice belongs to the positive orthant whenever `R > 0`. -/
-- Proof sketch: use `deltaNConstantChoice_apply` to identify each coordinate with
-- `R / √(N + 1)`, and note that `√(N + 1)` is positive.
theorem deltaNConstantChoice_mem_positiveOrthant (N : ℕ) {R : ℝ} (hR : 0 < R) :
    deltaNConstantChoice N R ∈ ℝ₊₊^(N + 1) := by
  rw [EuclideanSpace.mem_positiveOrthant_iff]
  intro i
  simpa only [deltaNConstantChoice_apply] using
    div_pos hR <| Real.sqrt_pos.2 <| by positivity

/-- Helper for Proposition 3.35: a vector in the positive orthant has strictly positive coordinate
sum. -/
-- Proof sketch: every coordinate is positive, so the whole finite sum dominates the `0`th
-- coordinate and is therefore positive.
private theorem positiveOrthant_sum_pos {N : ℕ} {h : E N}
    (hh : h ∈ ℝ₊₊^(N + 1)) :
    0 < ∑ i : Fin (N + 1), h i := by
  rw [EuclideanSpace.mem_positiveOrthant_iff] at hh
  -- A positive summand gives a positive lower bound for the full sum.
  have hle : h 0 ≤ ∑ i : Fin (N + 1), h i := by
    exact Finset.single_le_sum (fun i _ ↦ le_of_lt (hh i)) (Finset.mem_univ 0)
  exact lt_of_lt_of_le (hh 0) hle

/-- Helper for Proposition 3.35: Cauchy--Schwarz lower-bounds the sum of squares by the square of
the sum divided by the dimension. -/
-- Proof sketch: apply `sq_sum_le_card_mul_sum_sq` on `Finset.univ` and divide by the positive
-- scalar `(N + 1 : ℝ)`.
private theorem sum_sq_lower_bound_by_sq_sum (N : ℕ) (h : E N) :
    ((∑ i : Fin (N + 1), h i) ^ (2 : ℕ)) / (N + 1 : ℝ) ≤
      ∑ i : Fin (N + 1), h i ^ (2 : ℕ) := by
  have hdim : 0 < (N + 1 : ℝ) := by
    positivity
  have hcs :
      (∑ i : Fin (N + 1), h i) ^ (2 : ℕ) ≤
        (N + 1 : ℝ) * ∑ i : Fin (N + 1), h i ^ (2 : ℕ) := by
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin (N + 1) ↦ h i))
  exact (div_le_iff₀ hdim).2 <| by
    simpa [mul_comm] using hcs

/-- Helper for Proposition 3.35: the Cauchy--Schwarz estimate yields the scalar relaxation that
depends only on `S = ∑ i, h i`. -/
-- Proof sketch: rewrite `Δ[N; R] h` by definition, replace `∑ hᵢ²` by the lower bound
-- `S² / (N + 1)`, and compare the two quotients over the positive denominator `2 * S`.
private theorem deltaN_lower_bound_by_scalar_relaxation (N : ℕ) {R : ℝ} {h : E N}
    (hh : h ∈ ℝ₊₊^(N + 1)) :
    R ^ (2 : ℕ) / (2 * ∑ i : Fin (N + 1), h i) +
      (∑ i : Fin (N + 1), h i) / (2 * (N + 1 : ℝ)) ≤
        Δ[N; R] h := by
  have hsum_pos : 0 < ∑ i : Fin (N + 1), h i := positiveOrthant_sum_pos hh
  have hdim : 0 < (N + 1 : ℝ) := by
    positivity
  have hnumer :
      R ^ (2 : ℕ) + ((∑ i : Fin (N + 1), h i) ^ (2 : ℕ)) / (N + 1 : ℝ) ≤
        R ^ (2 : ℕ) + ∑ i : Fin (N + 1), h i ^ (2 : ℕ) := by
    exact add_le_add le_rfl (sum_sq_lower_bound_by_sq_sum N h)
  have hrewrite :
      R ^ (2 : ℕ) / (2 * ∑ i : Fin (N + 1), h i) +
        (∑ i : Fin (N + 1), h i) / (2 * (N + 1 : ℝ)) =
          (R ^ (2 : ℕ) + ((∑ i : Fin (N + 1), h i) ^ (2 : ℕ)) / (N + 1 : ℝ)) /
            (2 * ∑ i : Fin (N + 1), h i) := by
    field_simp [hsum_pos.ne', hdim.ne']
  -- After rewriting both terms over the same denominator, only numerator monotonicity remains.
  rw [hrewrite, deltaN_apply]
  exact (div_le_div_iff_of_pos_right
    (show 0 < 2 * ∑ i : Fin (N + 1), h i by positivity)).2 hnumer

/-- Helper for Proposition 3.35: the scalar relaxation is minimized at
`S = R * √(N + 1)`, with minimum value `R / √(N + 1)`. -/
-- Proof sketch: rewrite the right-hand side as a single quotient and clear the positive
-- denominator `2 * S`; the remaining estimate is the AM-GM / square-completion inequality
-- `2ab ≤ a² + b²` with `a = R` and `b = S / √(N + 1)`.
private theorem stepsize_scalar_lower_bound (N : ℕ) {R S : ℝ} (hS : 0 < S) :
    R / Real.sqrt (N + 1 : ℝ) ≤ R ^ (2 : ℕ) / (2 * S) + S / (2 * (N + 1 : ℝ)) := by
  have hdim : 0 < (N + 1 : ℝ) := by
    positivity
  have hsqrt : 0 < Real.sqrt (N + 1 : ℝ) := Real.sqrt_pos.2 hdim
  have hsqrt_sq : Real.sqrt (N + 1 : ℝ) ^ (2 : ℕ) = N + 1 := by
    rw [Real.sq_sqrt]
    positivity
  have hrewrite :
      R ^ (2 : ℕ) / (2 * S) + S / (2 * (N + 1 : ℝ)) =
        (R ^ (2 : ℕ) + S ^ (2 : ℕ) / (N + 1 : ℝ)) / (2 * S) := by
    field_simp [hS.ne', hdim.ne']
  rw [hrewrite]
  apply (le_div_iff₀ (show 0 < 2 * S by positivity)).2
  have hamgm :
      2 * R * (S / Real.sqrt (N + 1 : ℝ)) ≤
        R ^ (2 : ℕ) + (S / Real.sqrt (N + 1 : ℝ)) ^ (2 : ℕ) := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      (two_mul_le_add_sq R (S / Real.sqrt (N + 1 : ℝ)))
  have hmul :
      (R / Real.sqrt (N + 1 : ℝ)) * (2 * S) =
        2 * R * (S / Real.sqrt (N + 1 : ℝ)) := by
    field_simp [hsqrt.ne']
  have hsquare :
      (S / Real.sqrt (N + 1 : ℝ)) ^ (2 : ℕ) = S ^ (2 : ℕ) / (N + 1 : ℝ) := by
    rw [div_pow, hsqrt_sq]
  -- This is the scalar one-variable minimum after clearing denominators.
  calc
    (R / Real.sqrt (N + 1 : ℝ)) * (2 * S)
      = 2 * R * (S / Real.sqrt (N + 1 : ℝ)) := hmul
    _ ≤ R ^ (2 : ℕ) + (S / Real.sqrt (N + 1 : ℝ)) ^ (2 : ℕ) := hamgm
    _ = R ^ (2 : ℕ) + S ^ (2 : ℕ) / (N + 1 : ℝ) := by rw [hsquare]

/-- Proposition 3.35: for `R > 0`, the function `Δ_N` attains its minimum on the
positive orthant at the constant choice `h_i = R / √(N + 1)`. The closed-form value is recorded
separately by `deltaN_constantChoice`. -/
-- Proof sketch: write `S = ∑ i, h i` and `Q = ∑ i, h i^2`; Cauchy--Schwarz gives
-- `Q ≥ S^2 / (N + 1)`, so `Δ[N; R] h` is bounded below by
-- `R^2 / (2 S) + S / (2 (N + 1))`. Minimize this one-variable expression at
-- `S = R * √(N + 1)`, and check that equality holds exactly for the constant choice.
theorem deltaN_constantChoice_minimizes_positiveOrthant
    (N : ℕ) {R : ℝ} (hR : 0 < R) :
    IsMinOn (Δ[N; R]) (ℝ₊₊^(N + 1)) (deltaNConstantChoice N R) := by
  -- The positivity assumption records that the constant candidate actually lies in the domain.
  have : deltaNConstantChoice N R ∈ ℝ₊₊^(N + 1) :=
    deltaNConstantChoice_mem_positiveOrthant N hR
  rw [isMinOn_iff]
  intro h hh
  have hsum_pos : 0 < ∑ i : Fin (N + 1), h i := positiveOrthant_sum_pos hh
  -- Compare `Δ[N; R] h` with the scalar relaxation and then with the constant-choice value.
  calc
    Δ[N; R] (deltaNConstantChoice N R)
      = R / Real.sqrt (N + 1 : ℝ) := deltaN_constantChoice N R
    _ ≤ R ^ (2 : ℕ) / (2 * ∑ i : Fin (N + 1), h i) +
        (∑ i : Fin (N + 1), h i) / (2 * (N + 1 : ℝ)) :=
      stepsize_scalar_lower_bound N hsum_pos
    _ ≤ Δ[N; R] h := deltaN_lower_bound_by_scalar_relaxation N hh

/-! ### Theorem_3_35 (from Chap03) -/
noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u v

/- Theorem 3.35 lies in the chapter's affine-fiber infimal-projection / relative-subdifferential
domain.

Sampled owner-style declarations:
- `partialInfProjection` and
  `extendedRealRealPart_partialInfProjection_eq_sInf` in `Theorem_3_1_2_3`, the canonical
  `EReal` owner and its finite-value bridge;
- `partialInfProjection_convexOn_of_convexWithTop` in `Theorem_3_8`, the convexity theorem on the
  same owner for `WithTop` objectives;
- `linearEqualityFeasibleSet` in `LinearEqualityFeasibleSet`, the affine-constraint feasible-set
  owner already used elsewhere in the chapter;
- `subdifferentialWithin` in `Theorem_3_44`, the chapter owner for the real-valued relative
  subgradient surface.

Best owner abstraction:
- core/canonical: the affine-fiber `EReal` infimal projection
  `partialInfProjection {p | p.2 ∈ Q ∧ A p.2 = p.1} (withTopToEReal ∘ (f ∘ Prod.snd))`;
- source-facing bridge: `linearEqualityFeasibleSet Q A u` and the finite real part of that
  infimal projection on its domain;
- derived API: the `sInf` formula on finite fibers, convexity of that finite real part, and the
  variational-inequality criterion for membership in its relative subdifferential.

Primitive data:
- an objective `f : E → WithTop ℝ`;
- a feasible set `Q : Set E`;
- a linear map `A : E →ₗ[ℝ] Λ`.

Derived API:
- the finite-value `sInf` bridge for the projected value function;
- convexity of the finite real part on its finite-value domain;
- the multiplier-candidate inclusion into the relative subdifferential.

Source/core/bridge triage:
- source-facing: the projected-value-function statements for affine fibers `A x = u`;
- core/canonical: `partialInfProjection`;
- bridge/view: `linearEqualityFeasibleSet` and `subdifferentialWithin`.

The previous version introduced a second public owner `projectedValueFunction` and a separate
candidate-set surface, duplicating the earlier linearly constrained vocabulary while also bypassing
the chapter's canonical `partialInfProjection` owner. This file now keeps only thin bridge
theorems on the canonical owner stack, writes the affine-fiber relation directly into
`partialInfProjection` on the public theorem surface, and introduces no new public value-function
definition. -/

section AffineProjection

variable {E : Type u} {Λ : Type v}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid Λ] [Module ℝ Λ]
variable {f : E → WithTop ℝ} {Q : Set E} (A : E →ₗ[ℝ] Λ)

/-- Helper for Theorem 3.35: restricting affine fibers to the finite-value locus of `f` does not
change the canonical affine partial infimal projection. -/
-- Proof sketch: points where `f = ⊤` contribute only the top element to each fiber image, and
-- inserting `⊤` does not change the infimum.
theorem affinePartialInfProjection_eq_restricted_realProjection :
    partialInfProjection
        {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
        (withTopToEReal ∘ f ∘ Prod.snd) =
      partialInfProjection
        {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
        (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2) := by
  funext u
  let S : Set EReal :=
    (withTopToEReal ∘ f ∘ Prod.snd) '' {z : Λ × E |
      z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.1 = u}
  let T : Set EReal :=
    (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2) '' {z : Λ × E |
      (z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.2 ∈ dom f) ∧ z.1 = u}
  -- Every finite feasible point contributes the same value to the unrestricted and restricted
  -- fiber images.
  have hTS : T ⊆ S := by
    intro a ha
    rcases ha with ⟨z, hz, rfl⟩
    refine ⟨z, ⟨hz.1.1, hz.2⟩, ?_⟩
    simpa [Function.comp, withTopToEReal] using
      (congrArg withTopToEReal (coe_withTopRealPart (f := f) hz.1.2)).symm
  -- Unrestricted feasible points are either finite and already in `T`, or have value `⊤`.
  have hSinsert : S ⊆ insert ⊤ T := by
    intro a ha
    rcases ha with ⟨z, hz, rfl⟩
    by_cases hzDom : z.2 ∈ dom f
    · right
      refine ⟨z, ⟨⟨hz.1, hzDom⟩, hz.2⟩, ?_⟩
      simpa [Function.comp, withTopToEReal] using
        congrArg withTopToEReal (coe_withTopRealPart (f := f) hzDom)
    · left
      rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hzDom
      have hzTop : f z.2 = ⊤ := by
        simpa using hzDom
      change withTopToEReal (f z.2) = ⊤
      rw [hzTop, withTopToEReal]
      rfl
  rw [partialInfProjection_eq_sInf, partialInfProjection_eq_sInf]
  simpa [S, T] using
    (show sInf S = sInf T from
      le_antisymm (sInf_le_sInf hTS)
        (by simpa using (sInf_le_sInf hSinsert : sInf (insert ⊤ T) ≤ sInf S)))

/-- At any base point where the canonical affine-fiber infimal projection is finite, its finite
real part agrees with the textbook infimum of the feasible fiber values. -/
-- Proof sketch: unfold the affine fiber as `linearEqualityFeasibleSet Q A u`, then apply the
-- finite-value bridge for `partialInfProjection` on the corresponding subset of `Λ × E`.
theorem extendedRealRealPart_affinePartialInfProjection_eq_sInf_image
    {u : Λ}
    (hu :
      u ∈ dom
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd))) :
    extendedRealRealPart
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd))
        u =
      sInf {t : ℝ | ∃ x : E, x ∈ linearEqualityFeasibleSet Q A u ∧ f x = t} := by
  have hu' :
      u ∈ dom
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
          (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2)) := by
    rw [affinePartialInfProjection_eq_restricted_realProjection (A := A) (f := f) (Q := Q)] at hu
    exact hu
  -- The restricted owner matches the textbook fiber-value set exactly.
  have himage :
      (fun p : Λ × E ↦ withTopRealPart f p.2) '' {z : Λ × E |
          (z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.2 ∈ dom f) ∧ z.1 = u} =
        {t : ℝ | ∃ x : E, x ∈ linearEqualityFeasibleSet Q A u ∧ f x = t} := by
    ext t
    constructor
    · rintro ⟨z, hz, ht⟩
      have hzFeas : z.2 ∈ linearEqualityFeasibleSet Q A u := by
        simpa [hz.2] using hz.1.1
      refine ⟨z.2, hzFeas, ?_⟩
      calc
        f z.2 = ((withTopRealPart f z.2 : ℝ) : WithTop ℝ) := by
          symm
          exact coe_withTopRealPart (f := f) hz.1.2
        _ = t := by
          exact congrArg (fun s : ℝ ↦ ((s : ℝ) : WithTop ℝ)) ht
    · rintro ⟨x, hx, hfx⟩
      have hxDom : x ∈ dom f := by
        rw [mem_withTopEffectiveDomain_iff, hfx, lt_top_iff_ne_top]
        simp
      refine ⟨(u, x), ⟨⟨hx, hxDom⟩, rfl⟩, ?_⟩
      apply WithTop.coe_injective
      simpa [hfx] using coe_withTopRealPart (f := f) hxDom
  -- Read the finite-value bridge on the restricted real-valued owner.
  rw [affinePartialInfProjection_eq_restricted_realProjection (A := A) (f := f) (Q := Q)]
  have hbridge :
      extendedRealRealPart
          (partialInfProjection
            {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
            (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2))
          u =
        sInf ((fun p : Λ × E ↦ withTopRealPart f p.2) '' {z : Λ × E |
          (z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.2 ∈ dom f) ∧ z.1 = u}) := by
    simpa using
      (extendedRealRealPart_partialInfProjection_eq_sInf
        (Q := {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f})
        (φ := fun p : Λ × E ↦ withTopRealPart f p.2)
        hu')
  calc
    extendedRealRealPart
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
          (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2))
        u =
      sInf ((fun p : Λ × E ↦ withTopRealPart f p.2) '' {z : Λ × E |
        (z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.2 ∈ dom f) ∧ z.1 = u}) := hbridge
    _ = sInf {t : ℝ | ∃ x : E, x ∈ linearEqualityFeasibleSet Q A u ∧ f x = t} := by
          rw [himage]

/-- Theorem 3.35 (1): under convexity of `f` on its effective domain plus convexity of `Q`, the
finite real part of the canonical affine-fiber infimal projection is convex on its finite-value
domain. -/
-- Proof sketch: specialize the chapter convexity theorem for `partialInfProjection` to
-- `{p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}` together with the `WithTop` objective
-- `f ∘ Prod.snd`.
theorem affinePartialInfProjection_realPart_convexOn
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hQ_convex : Convex ℝ Q) :
    ConvexOn ℝ
      (dom
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd)))
      (extendedRealRealPart
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd))) := by
  let Q' : Set (Λ × E) :=
    {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
  -- The affine-fiber finite locus is convex because both `Q` and `dom f` are convex and the
  -- equality constraint is preserved by affine combinations.
  have hQ' : Convex ℝ Q' := by
    intro p hp q hq a b ha hb hab
    rcases hp with ⟨hpFeas, hpDom⟩
    rcases hq with ⟨hqFeas, hqDom⟩
    rcases hpFeas with ⟨hpQ, hpA⟩
    rcases hqFeas with ⟨hqQ, hqA⟩
    refine ⟨?_, hf.1 hpDom hqDom ha hb hab⟩
    refine ⟨hQ_convex hpQ hqQ ha hb hab, ?_⟩
    simp [linearEqualityFeasibleSet, hpA, hqA, map_add, map_smul]
  -- The objective on the product space is just the second-coordinate pullback of `withTopRealPart f`.
  have hφ' : ConvexOn ℝ Q' (fun p : Λ × E ↦ withTopRealPart f p.2) := by
    refine ⟨hQ', ?_⟩
    intro p hp q hq a b ha hb hab
    exact hf.2 hp.2 hq.2 ha hb hab
  -- Apply the real-valued owner theorem on the restricted fiber set and transport back.
  rw [affinePartialInfProjection_eq_restricted_realProjection (A := A) (f := f) (Q := Q)]
  simpa [Q']
    using
      (partialInfProjection_convexOn
        (Q := Q')
        (φ := fun p : Λ × E ↦ withTopRealPart f p.2)
        hQ' hφ')

end AffineProjection

section Subgradient

variable {E : Type u} {Λ : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ Λ]
variable {f : E → WithTop ℝ} {Q : Set E} (A : E →ₗ[ℝ] Λ)

/-- Helper for Theorem 3.35: a finite affine partial-infimal-projection value comes from a
feasible point where `f` is finite. -/
-- Proof sketch: after restricting to the finite-value locus from
-- `affinePartialInfProjection_eq_restricted_realProjection`, an empty fiber would force the
-- partial infimum to be `⊤`, contradicting membership in the effective domain.
lemma exists_feasible_point_of_mem_dom_affinePartialInfProjection
    {v : Λ}
    (hv :
      v ∈ dom
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd))) :
    ∃ x : E, x ∈ linearEqualityFeasibleSet Q A v ∧ x ∈ dom f := by
  let Q' : Set (Λ × E) :=
    {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
  have hv' :
      v ∈ dom
        (partialInfProjection
          Q'
          (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2)) := by
    rw [affinePartialInfProjection_eq_restricted_realProjection (A := A) (f := f) (Q := Q)] at hv
    exact hv
  let S : Set (Λ × E) := {z : Λ × E | z ∈ Q' ∧ z.1 = v}
  -- The restricted fiber cannot be empty because an empty fiber has infimum `⊤`.
  have hS_nonempty : S.Nonempty := by
    by_contra hS
    have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have htop :
        partialInfProjection Q' (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2) v = ⊤ := by
      rw [partialInfProjection_eq_sInf]
      simp [S, hS_empty]
    exact (mem_extendedRealEffectiveDomain_iff.mp hv').1 htop
  rcases hS_nonempty with ⟨z, hz⟩
  have hzFeas : z.2 ∈ linearEqualityFeasibleSet Q A v := by
    simpa [Q', hz.2] using hz.1.1
  exact ⟨z.2, hzFeas, hz.1.2⟩

/-- Helper for Theorem 3.35: the ambient subgradient inequality together with the affine
variational inequality yields the fiberwise lower bound used in the projected subgradient proof.
-/
-- Proof sketch: the subgradient inequality controls `f` by `gStar`, the variational inequality
-- replaces `gStar` by `Aᵀ yStar` on `Q`, and the adjoint identity turns that into the base-space
-- pairing `⟪yStar, v - u⟫`.
lemma affine_fiber_lower_bound_of_variational_inequality
    {u v : Λ} {xStar gStar x : E} {yStar : Λ}
    (hxStar : xStar ∈ linearEqualityFeasibleSet Q A u)
    (hgStar : gStar ∈ ∂ f(xStar))
    (hvar :
      ∀ z : E, z ∈ Q →
        0 ≤ inner ℝ (gStar - A.adjoint yStar) (z - xStar))
    (hx : x ∈ linearEqualityFeasibleSet Q A v)
    (hxDom : x ∈ dom f) :
    withTopRealPart f xStar + inner ℝ yStar (v - u) ≤ withTopRealPart f x := by
  have hxStarDom : xStar ∈ dom f := (mem_subdifferential_iff.mp hgStar).mem_dom
  rcases hxStar with ⟨hxStarQ, hxStarA⟩
  rcases hx with ⟨hxQ, hxA⟩
  -- Translate the ambient subgradient inequality to the finite real part on `dom f`.
  have hsupport :
      withTopRealPart f x ≥ withTopRealPart f xStar + inner ℝ gStar (x - xStar) := by
    have hsub := (mem_subdifferential_iff.mp hgStar).2 hxDom
    rw [← coe_withTopRealPart (f := f) hxDom, ← coe_withTopRealPart (f := f) hxStarDom] at hsub
    exact_mod_cast hsub
  -- The variational inequality removes the normal component from `gStar`.
  have hnormal :
      inner ℝ (A.adjoint yStar) (x - xStar) ≤ inner ℝ gStar (x - xStar) := by
    have hvarx := hvar x hxQ
    rw [inner_sub_left] at hvarx
    linarith
  have hbase :
      inner ℝ yStar (v - u) = inner ℝ (A.adjoint yStar) (x - xStar) := by
    calc
      inner ℝ yStar (v - u)
          = inner ℝ yStar (A x - A xStar) := by simpa [hxA, hxStarA]
      _ = inner ℝ yStar (A (x - xStar)) := by simp [map_sub]
      _ = inner ℝ (A.adjoint yStar) (x - xStar) := by
            rw [A.adjoint_inner_left]
  have hreal :
      withTopRealPart f xStar + inner ℝ (A.adjoint yStar) (x - xStar) ≤ withTopRealPart f x := by
    linarith
  simpa [hbase] using hreal

/-- A feasible primal point `xStar` on the fiber `A x = u` with a primal
subgradient `gStar ∈ ∂ f(xStar)` whose affine-constraint variational inequality holds on `Q`, then
the multiplier `yStar` is a relative subgradient of the finite real part of the canonical
affine-fiber infimal projection on its finite-value domain. -/
-- Proof sketch: convert the affine-fiber value function to the chapter `partialInfProjection`
-- owner and check that the displayed inequality is exactly the lower-support condition defining
-- membership in the relative subdifferential of the specialized `partialInfProjection`.
theorem mem_subdifferentialWithin_affinePartialInfProjection_of_variational_inequality
    {u : Λ}
    {xStar gStar : E} {yStar : Λ}
    (hxStar : xStar ∈ linearEqualityFeasibleSet Q A u)
    (hgStar : gStar ∈ ∂ f(xStar))
    (hvar :
      ∀ x : E, x ∈ Q →
        0 ≤ inner ℝ (gStar - A.adjoint yStar) (x - xStar)) :
    yStar ∈
      ∂[dom
          (partialInfProjection
            {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
            (withTopToEReal ∘ f ∘ Prod.snd))]
        (extendedRealRealPart
          (partialInfProjection
            {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
            (withTopToEReal ∘ f ∘ Prod.snd)))
        (u) :=
      by
  let ψ : Λ → EReal :=
    partialInfProjection
      {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
      (withTopToEReal ∘ f ∘ Prod.snd)
  change yStar ∈ ∂[dom ψ] (extendedRealRealPart ψ) (u)
  have hxStarDom : xStar ∈ dom f := (mem_subdifferential_iff.mp hgStar).mem_dom
  have hxStarValue : ((withTopRealPart f xStar : ℝ) : EReal) = withTopToEReal (f xStar) := by
    simpa [withTopToEReal] using congrArg withTopToEReal (coe_withTopRealPart (f := f) hxStarDom)
  let Su : Set EReal :=
    (withTopToEReal ∘ f ∘ Prod.snd) '' {z : Λ × E |
      z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.1 = u}
  -- Every point on the `u`-fiber lies above `f xStar`, so the projected value at `u` is finite
  -- and equal to the finite value achieved by `xStar`.
  have hSu_nonempty : Su.Nonempty := by
    refine ⟨withTopToEReal (f xStar), ⟨(u, xStar), ?_, rfl⟩⟩
    exact ⟨hxStar, rfl⟩
  have hSu_lower :
      ∀ b ∈ Su, (((withTopRealPart f xStar : ℝ) : EReal)) ≤ b := by
    intro b hb
    rcases hb with ⟨z, hz, rfl⟩
    by_cases hzDom : z.2 ∈ dom f
    · have hzFeas : z.2 ∈ linearEqualityFeasibleSet Q A u := by
        simpa [hz.2] using hz.1
      have hreal :
          withTopRealPart f xStar ≤ withTopRealPart f z.2 := by
        simpa using
          (affine_fiber_lower_bound_of_variational_inequality
            (A := A) (Q := Q) (f := f)
            (hxStar := hxStar) (hgStar := hgStar) (hvar := hvar)
            (hx := hzFeas) (hxDom := hzDom) (u := u) (v := u) (yStar := yStar))
      have hzValue : ((withTopRealPart f z.2 : ℝ) : EReal) = withTopToEReal (f z.2) := by
        simpa [withTopToEReal] using
          congrArg withTopToEReal (coe_withTopRealPart (f := f) hzDom)
      change ((withTopRealPart f xStar : ℝ) : EReal) ≤ withTopToEReal (f z.2)
      rw [← hzValue]
      exact_mod_cast hreal
    · rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hzDom
      have hzTop : f z.2 = ⊤ := by
        simpa using hzDom
      change ((withTopRealPart f xStar : ℝ) : EReal) ≤ withTopToEReal (f z.2)
      rw [hzTop, withTopToEReal]
      exact le_top
  have hSu_bddBelow : BddBelow Su := ⟨((withTopRealPart f xStar : ℝ) : EReal), hSu_lower⟩
  have hψu_lower : ((withTopRealPart f xStar : ℝ) : EReal) ≤ ψ u := by
    simpa [ψ, Su, partialInfProjection_eq_sInf] using le_csInf hSu_nonempty hSu_lower
  have hψu_upper : ψ u ≤ ((withTopRealPart f xStar : ℝ) : EReal) := by
    have hxStar_mem : withTopToEReal (f xStar) ∈ Su := by
      refine ⟨(u, xStar), ?_, rfl⟩
      exact ⟨hxStar, rfl⟩
    have htmp : ψ u ≤ withTopToEReal (f xStar) := by
      simpa [ψ, Su, partialInfProjection_eq_sInf] using csInf_le hSu_bddBelow hxStar_mem
    rw [← hxStarValue] at htmp
    exact htmp
  have hψu : ψ u = ((withTopRealPart f xStar : ℝ) : EReal) := le_antisymm hψu_upper hψu_lower
  have huDom : u ∈ dom ψ := by
    rw [mem_extendedRealEffectiveDomain_iff, hψu]
    constructor <;> simp
  have hψuReal : extendedRealRealPart ψ u = withTopRealPart f xStar := by
    apply EReal.coe_injective
    rw [coe_extendedRealRealPart huDom, hψu]
  rw [mem_subdifferentialWithin_iff]
  refine ⟨huDom, ?_⟩
  intro v hv
  rcases exists_feasible_point_of_mem_dom_affinePartialInfProjection
      (A := A) (Q := Q) (f := f) hv with ⟨xv, hxv, hxvDom⟩
  let Sv : Set EReal :=
    (withTopToEReal ∘ f ∘ Prod.snd) '' {z : Λ × E |
      z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.1 = v}
  -- The same fiberwise lower-bound argument gives the projected support inequality at every
  -- finite base point `v`.
  have hSv_nonempty : Sv.Nonempty := by
    refine ⟨withTopToEReal (f xv), ⟨(v, xv), ?_, rfl⟩⟩
    exact ⟨hxv, rfl⟩
  have hSv_lower :
      ∀ b ∈ Sv, (((withTopRealPart f xStar + inner ℝ yStar (v - u) : ℝ) : EReal)) ≤ b := by
    intro b hb
    rcases hb with ⟨z, hz, rfl⟩
    by_cases hzDom : z.2 ∈ dom f
    · have hzFeas : z.2 ∈ linearEqualityFeasibleSet Q A v := by
        simpa [hz.2] using hz.1
      have hreal :=
        affine_fiber_lower_bound_of_variational_inequality
          (A := A) (Q := Q) (f := f)
          (hxStar := hxStar) (hgStar := hgStar) (hvar := hvar)
          (hx := hzFeas) (hxDom := hzDom) (u := u) (v := v) (yStar := yStar)
      have hzValue : ((withTopRealPart f z.2 : ℝ) : EReal) = withTopToEReal (f z.2) := by
        simpa [withTopToEReal] using
          congrArg withTopToEReal (coe_withTopRealPart (f := f) hzDom)
      change ((withTopRealPart f xStar + inner ℝ yStar (v - u) : ℝ) : EReal) ≤ withTopToEReal (f z.2)
      rw [← hzValue]
      exact_mod_cast hreal
    · rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hzDom
      have hzTop : f z.2 = ⊤ := by
        simpa using hzDom
      change ((withTopRealPart f xStar + inner ℝ yStar (v - u) : ℝ) : EReal) ≤ withTopToEReal (f z.2)
      rw [hzTop, withTopToEReal]
      exact le_top
  have hψvLower :
      (((withTopRealPart f xStar + inner ℝ yStar (v - u) : ℝ) : EReal)) ≤ ψ v := by
    simpa [ψ, Sv, partialInfProjection_eq_sInf] using le_csInf hSv_nonempty hSv_lower
  have hsupport :
      withTopRealPart f xStar + inner ℝ yStar (v - u) ≤ extendedRealRealPart ψ v := by
    have hE :
        (((withTopRealPart f xStar + inner ℝ yStar (v - u) : ℝ) : EReal)) ≤
          ((extendedRealRealPart ψ v : ℝ) : EReal) := by
      calc
        (((withTopRealPart f xStar + inner ℝ yStar (v - u) : ℝ) : EReal)) ≤ ψ v := hψvLower
        _ = ((extendedRealRealPart ψ v : ℝ) : EReal) := by
            symm
            exact coe_extendedRealRealPart hv
    exact_mod_cast hE
  rw [hψuReal]
  simpa [add_comm, add_left_comm, add_assoc] using hsupport

/-- The multiplier candidates arising from feasible primal points, primal subgradients, and the
affine-constraint variational inequality on `Q` lie in the relative subdifferential of the
projected value function on its finite-value domain. The candidate set is kept inline because it
is only a source-facing bridge to the canonical owner surface given by the specialized
`partialInfProjection`, not an independent owner of its own. -/
-- Proof sketch: unpack a candidate multiplier into a feasible primal point and subgradient, then
-- apply `mem_subdifferentialWithin_affinePartialInfProjection_of_variational_inequality`.
theorem affineMultiplierCandidates_subset_subdifferentialWithin_affinePartialInfProjection
    (u : Λ) :
    {yStar : Λ | ∃ xStar : E, xStar ∈ linearEqualityFeasibleSet Q A u ∧
        ∃ gStar : E, gStar ∈ ∂ f(xStar) ∧
          ∀ x : E, x ∈ Q →
            0 ≤ inner ℝ (gStar - A.adjoint yStar) (x - xStar)} ⊆
      ∂[dom
          (partialInfProjection
            {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
            (withTopToEReal ∘ f ∘ Prod.snd))]
        (extendedRealRealPart
          (partialInfProjection
            {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
            (withTopToEReal ∘ f ∘ Prod.snd)))
        (u) := by
  intro yStar hyStar
  rcases hyStar with ⟨xStar, hxStar, gStar, hgStar, hvar⟩
  -- Unpack the candidate data and invoke the affine-fiber multiplier criterion proved above.
  exact mem_subdifferentialWithin_affinePartialInfProjection_of_variational_inequality
    (A := A) (Q := Q) (f := f) (u := u)
    (hxStar := hxStar) (hgStar := hgStar) (hvar := hvar)

end Subgradient

end
