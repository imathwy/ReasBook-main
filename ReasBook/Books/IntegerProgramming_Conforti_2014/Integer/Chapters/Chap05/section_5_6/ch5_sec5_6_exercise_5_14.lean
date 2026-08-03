import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Rat
import Integer.Chapters.Chap05.section_5_2_5.ch5_sec5_2_5_theorem_5_19

open IsLocalization
open scoped BigOperators

-- Domain-style sampling for this refine pass:
-- * primary domain: support cuts from rational tableau rows and Chapter 5 lexicographic
--   cutting-plane runs
-- * source-facing declarations kept here: `nonintegralCoefficientSupport`,
--   `exercise514SolutionSet`, `nonintegralCoefficientSupportCut`,
--   `NonintegralCoefficientSupportLexicographicCuttingPlaneMethod`,
--   and the Exercise 5.14 termination theorem
-- * nearby declarations inspected:
--   `GomoryLexicographicCuttingPlaneMethod`,
--   `periodic_gomory_fractional_cutting_plane_method_terminates`,
--   `mixed_integer_gomory_lexicographic_cutting_plane_method_terminates`

-- Semantic recall note: this exercise uses mathlib's canonical rational-integrality predicate
-- `IsLocalization.IsInteger ℤ` for the support cut. For Exercise 5.14(2), the local owner is a
-- source-facing variant parallel to the Chapter 5 lexicographic method owner, with the
-- nonterminal cut-adjoining clause replaced by the support cut from part (1) and with the
-- selected-row right-hand side data retained explicitly. The termination statement is routed
-- through an explicit bridge back to `GomoryLexicographicCuttingPlaneMethod` so the support-cut
-- run is not treated as an arbitrary unrelated abstract process.
-- Semantic search note: `lean_leansearch` did not surface a more specific owner, so this repair
-- follows the verified local Chapter 5 owner/API shape around
-- `GomoryLexicographicCuttingPlaneMethod`.

section Exercise514

variable {n : ℕ}

/-- A rational number is an integer exactly when its reduced denominator is `1`. -/
theorem rat_isInteger_iff_den_eq_one (q : ℚ) : IsInteger ℤ q ↔ q.den = 1 := by
  rw [Rat.isLocalizationIsInteger_iff, Rat.den_eq_one_iff]
  constructor
  · rintro ⟨z, rfl⟩
    simp
  · intro hq
    exact ⟨q.num, hq⟩

/-- The index set of nonintegral coefficients of the rational vector `a`. -/
def nonintegralCoefficientSupport (a : Fin n → ℚ) : Finset (Fin n) :=
  let _ : DecidablePred (fun j : Fin n ↦ ¬ IsInteger ℤ (a j)) := fun j ↦ by
      simpa [rat_isInteger_iff_den_eq_one] using
        (inferInstance : Decidable ((a j).den ≠ 1))
  Finset.univ.filter (fun j ↦ ¬ IsInteger ℤ (a j))

/-- Membership in `nonintegralCoefficientSupport a` is exactly nonintegrality of the coefficient
`a j`. -/
@[simp] theorem mem_nonintegralCoefficientSupport_iff
    (a : Fin n → ℚ)
    (j : Fin n) :
    j ∈ nonintegralCoefficientSupport a ↔ ¬ IsInteger ℤ (a j) := by
  simp [nonintegralCoefficientSupport]

/-- The set `S = {x ∈ ℤ_+^n : ∑ a_j x_j = b}` from Exercise 5.14. -/
def exercise514SolutionSet (a : Fin n → ℚ) (b : ℚ) : Set (Fin n → ℤ) :=
  {x | (∀ j : Fin n, 0 ≤ x j) ∧ ∑ j, a j * (x j : ℚ) = b}

/-- The cut `∑_{j ∈ J} x_j ≥ 1` attached to the nonintegral coefficient support `J`. -/
def nonintegralCoefficientSupportCut (a : Fin n → ℚ) : Set (Fin n → ℝ) :=
  {x | 1 ≤ Finset.sum (nonintegralCoefficientSupport a) fun j ↦ x j}

/-- Membership in `nonintegralCoefficientSupportCut a` is exactly the inequality
`∑_{j ∈ J} x_j ≥ 1`. -/
theorem mem_nonintegralCoefficientSupportCut_iff
    (a : Fin n → ℚ)
    (x : Fin n → ℝ) :
    x ∈ nonintegralCoefficientSupportCut a ↔
      1 ≤ Finset.sum (nonintegralCoefficientSupport a) fun j ↦ x j :=
  Iff.rfl

/-- Exercise 5.14 (1). If `b` is positive and nonintegral, then every point of
`S = {x ∈ ℤ_+^n : ∑ a_j x_j = b}` satisfies the valid inequality
`∑_{j ∈ J} x_j ≥ 1`, where `J = {j : a_j ∉ ℤ}`. -/
theorem exercise_5_14_nonintegral_support_cut_valid
    (a : Fin n → ℚ)
    {b : ℚ}
    (hb_pos : 0 < b)
    (hb_nonintegral : ¬ IsInteger ℤ b) :
    ∀ ⦃x : Fin n → ℤ⦄, x ∈ exercise514SolutionSet a b →
      (fun j ↦ (x j : ℝ)) ∈ nonintegralCoefficientSupportCut a := sorry

/-- A stage-indexed lexicographic cutting-plane run for a bounded pure integer program whose
nonterminal step adjoins the support cut from Exercise 5.14 (1) coming from the selected tableau
row. The row right-hand side is retained explicitly because the support cut is source-faithful
only for positive nonintegral right-hand sides. -/
structure NonintegralCoefficientSupportLexicographicCuttingPlaneMethod (n : ℕ) where
  feasibleRegion : Set (Fin (n + 1) → ℝ)
  bounded_feasibleRegion : Bornology.IsBounded feasibleRegion
  relaxation : ℕ → Set (Fin n → ℝ)
  iterates : ℕ → Fin (n + 1) → ℝ
  iterates_mem_feasibleRegion : ∀ t : ℕ, iterates t ∈ feasibleRegion
  iterates_mem_relaxation : ∀ t : ℕ, (fun j ↦ iterates t j.succ) ∈ relaxation t
  selectedRow : ℕ → Option (Fin (n + 1))
  selectedRow_none_iff :
    ∀ t : ℕ, selectedRow t = none ↔
      ∀ k : Fin (n + 1), iterates t k ∈ Set.range (Int.cast : ℤ → ℝ)
  cutCoeff : ℕ → Fin n → ℚ
  cutRhs : ℕ → ℚ
  selectedRow_cutRhs_pos :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k → 0 < cutRhs t
  selectedRow_cutRhs_nonintegral :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k → ¬ IsInteger ℤ (cutRhs t)
  relaxation_step :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k →
      relaxation (t + 1) =
        relaxation t ∩ nonintegralCoefficientSupportCut (cutCoeff t)
  lexicographically_nonincreasing :
    ∀ t : ℕ, toLex (iterates (t + 1)) ≤ toLex (iterates t)
  selectedRow_spec :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k →
      (∀ i : Fin (n + 1), i < k → iterates t i ∈ Set.range (Int.cast : ℤ → ℝ)) ∧
        iterates t k ∉ Set.range (Int.cast : ℤ → ℝ)
  strict_progress_on_fractional_step :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k →
      toLex (iterates (t + 1)) < toLex (iterates t)
  selectedRow_eventually_forces_floor :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄,
      selectedRow t = some k →
      ∀ {m : ℤ},
      iterates t k < (m : ℝ) + 1 →
      (∀ i : Fin (n + 1), i < k →
        ∃ z : ℤ, ∀ s ≥ t + 1, iterates s i = (z : ℝ)) →
      ∀ s ≥ t + 1, iterates s k ≤ (m : ℝ)

namespace NonintegralCoefficientSupportLexicographicCuttingPlaneMethod

/-- A support-cut lexicographic run stops at stage `t` when no tableau row is selected for the
next support cut. -/
def StopsAt
    {n : ℕ} (A : NonintegralCoefficientSupportLexicographicCuttingPlaneMethod n) (t : ℕ) : Prop :=
  A.selectedRow t = none

/-- Equipping the same iterate/selected-row run with the auxiliary Gomory cut data from the
Chapter 5 lexicographic method yields the canonical owner used for the termination theorem. -/
def toGomoryLexicographicCuttingPlaneMethod
    {n : ℕ} (A : NonintegralCoefficientSupportLexicographicCuttingPlaneMethod n)
    (cutColumns : ℕ → Finset (Fin n))
    (gomoryCutCoeff : ℕ → Fin n → ℚ)
    (gomoryCutRhs : ℕ → ℚ)
    (gomory_relaxation_step :
      ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, A.selectedRow t = some k →
        A.relaxation (t + 1) =
          A.relaxation t ∩ gomory_fractional_cut (cutColumns t) (gomoryCutCoeff t)
            (gomoryCutRhs t)) :
    GomoryLexicographicCuttingPlaneMethod n where
  feasibleRegion := A.feasibleRegion
  bounded_feasibleRegion := A.bounded_feasibleRegion
  relaxation := A.relaxation
  iterates := A.iterates
  iterates_mem_feasibleRegion := A.iterates_mem_feasibleRegion
  iterates_mem_relaxation := A.iterates_mem_relaxation
  selectedRow := A.selectedRow
  selectedRow_none_iff := A.selectedRow_none_iff
  cutColumns := cutColumns
  cutCoeff := gomoryCutCoeff
  cutRhs := gomoryCutRhs
  relaxation_step := gomory_relaxation_step
  lexicographically_nonincreasing := A.lexicographically_nonincreasing
  selectedRow_spec := A.selectedRow_spec
  strict_progress_on_fractional_step := A.strict_progress_on_fractional_step
  selectedRow_eventually_forces_floor := A.selectedRow_eventually_forces_floor

end NonintegralCoefficientSupportLexicographicCuttingPlaneMethod

/-- Exercise 5.14 (2). A lexicographic cutting-plane method for a pure integer program still
terminates in finitely many iterations when each nonterminal step adjoins the support cut from
part (1) instead of the Gomory fractional cut, provided the same iterate/selected-row run is
equipped with the auxiliary Gomory-cut step data needed to recover the canonical Chapter 5
lexicographic owner. -/
theorem nonintegral_coefficient_support_lexicographic_cutting_plane_method_terminates
    {n : ℕ} (A : NonintegralCoefficientSupportLexicographicCuttingPlaneMethod n)
    (cutColumns : ℕ → Finset (Fin n))
    (gomoryCutCoeff : ℕ → Fin n → ℚ)
    (gomoryCutRhs : ℕ → ℚ)
    (gomory_relaxation_step :
      ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, A.selectedRow t = some k →
        A.relaxation (t + 1) =
          A.relaxation t ∩ gomory_fractional_cut (cutColumns t) (gomoryCutCoeff t)
            (gomoryCutRhs t)) :
    ∃ T : ℕ, A.StopsAt T := sorry

end Exercise514
