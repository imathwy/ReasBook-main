import Mathlib
import cartan.II.section05.«0017_Definition_II_1_extra_10»
import cartan.II.section05.«0026_Definition_II_1_extra_16»
import cartan.II.section05.«0028_Proposition_8_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

noncomputable section

namespace Path

theorem not_mem_range_of_range_subset {z : ℂ} (γ : Path z z) {D : Set ℂ} {a : ℂ}
    (hγD : Set.range γ ⊆ D) (haD : a ∉ D) :
    a ∉ Set.range γ :=
  fun haγ ↦ haD (hγD haγ)

end Path

theorem not_mem_range_left_of_closedPathHomotopicIn_compl_singleton
    {z₀ z₁ a : ℂ} {γ₀ : Path z₀ z₀} {γ₁ : Path z₁ z₁}
    (hγ : ClosedPathHomotopicIn ({a} : Set ℂ)ᶜ γ₀ γ₁) :
    a ∉ Set.range γ₀ := by
  have hγ₀ : IsClosedPathIn ({a} : Set ℂ)ᶜ (γ₀ : C(I, ℂ)) := by
    simpa using hγ.some.prop 0
  rintro ⟨t, rfl⟩
  exact (isClosedPathIn_compl_iff.mp hγ₀).2 t (by simp)

theorem not_mem_range_right_of_closedPathHomotopicIn_compl_singleton
    {z₀ z₁ a : ℂ} {γ₀ : Path z₀ z₀} {γ₁ : Path z₁ z₁}
    (hγ : ClosedPathHomotopicIn ({a} : Set ℂ)ᶜ γ₀ γ₁) :
    a ∉ Set.range γ₁ := by
  have hγ₁ : IsClosedPathIn ({a} : Set ℂ)ᶜ (γ₁ : C(I, ℂ)) := by
    simpa using hγ.some.prop 1
  rintro ⟨t, rfl⟩
  exact (isClosedPathIn_compl_iff.mp hγ₁).2 t (by simp)

-- Proof sketch: apply Theorem `2'` to the closed logarithmic form `z ↦ dz / (z - a)` on
-- `ℂ \ {a}`; the homotopy keeps every intermediate closed path in the punctured plane, so the
-- normalized contour integral defining the index is unchanged.
/-- Remark II.1-extra-17 (1): for a fixed point `a`, the index of a closed path is invariant under
continuous deformation through closed paths that avoid `a`. -/
theorem closedPathIndex_eq_of_homotopic_avoiding_point
    {z₀ z₁ a : ℂ} {γ₀ : Path z₀ z₀} {γ₁ : Path z₁ z₁}
    (hγ : ClosedPathHomotopicIn ({a} : Set ℂ)ᶜ γ₀ γ₁) :
    γ₀.closedPathIndexAt a (not_mem_range_left_of_closedPathHomotopicIn_compl_singleton hγ) =
      γ₁.closedPathIndexAt a (not_mem_range_right_of_closedPathHomotopicIn_compl_singleton hγ) :=
  sorry

-- Proof sketch: for each puncture `a` off the image of `γ`, choose a small open disc disjoint from
-- `Set.range γ`; any other puncture in that disc is joined to `a` by a straight-line homotopy that
-- keeps the path away from the varying center, so clause (1) gives local constancy.
/-- Remark II.1-extra-17 (2): for a fixed closed path, the index is a locally constant function of
the puncture on the complement of the image. -/
theorem isLocallyConstant_closedPathIndex {z : ℂ} (γ : Path z z) :
    IsLocallyConstant (fun a : {w : ℂ // w ∉ Set.range γ} ↦ closedPathIndex γ a) := sorry

-- Proof sketch: apply the locally constant result from clause (2) to the connected component of
-- `a`; locally constant functions are constant on connected components.
/-- Remark II.1-extra-17 (3): for a fixed closed path, the index is constant on each connected
component of the complement of the image. -/
theorem closedPathIndex_eq_of_mem_connectedComponent {z : ℂ} (γ : Path z z)
    {a b : {w : ℂ // w ∉ Set.range γ}} (hb : b ∈ connectedComponent a) :
    closedPathIndex γ b = closedPathIndex γ a := sorry

-- Proof sketch: the simply connectedness of `D` makes `γ` null-homotopic within `D`; since
-- `a ∉ D`, that homotopy avoids `a`, so clause (1) reduces the index to the constant loop, whose
-- logarithmic integral is zero.
/-- Remark II.1-extra-17 (4): if the image of a closed path is contained in a simply connected set
avoiding `a`, then the index with respect to `a` is zero. -/
theorem closedPathIndex_eq_zero_of_range_subset_isSimplyConnected
    {z : ℂ} {γ : Path z z} {D : Set ℂ} (hD : IsSimplyConnected D)
    (hγD : Set.range γ ⊆ D) (a : ℂ) (haD : a ∉ D) :
    γ.closedPathIndexAt a (γ.not_mem_range_of_range_subset hγD haD) = 0 := sorry

-- Proof sketch: choose an open disc centered at the origin whose radius is strictly between `r`
-- and `‖a‖`; it is simply connected, contains the image of the standard circle, and avoids `a`, so
-- clause (4) gives index `0`.
/-- Remark II.1-extra-17 (5): the positively oriented standard circle has index `0` at every point
outside the closed disc that it bounds. -/
theorem closedPathIndex_standardCircle_eq_zero_of_not_mem_closedBall
    (r : NNReal)
    (a : ℂ) (ha : a ∉ Metric.closedBall (0 : ℂ) (r : ℝ)) :
    (standardCirclePath r).closedPathIndexAt a
      (standardCirclePath_not_mem_range_of_not_mem_closedBall r ha) = 0 :=
  sorry

-- Proof sketch: the open disc bounded by the standard circle is connected, and clause (2) makes
-- the index locally constant there; it therefore suffices to evaluate at the center `0`, where the
-- direct circle computation gives the value `1`.
/-- Remark II.1-extra-17 (6): the positively oriented standard circle has index `1` at every point
inside the open disc that it bounds. -/
theorem closedPathIndex_standardCircle_eq_one_of_mem_ball
    (r : NNReal)
    (a : ℂ) (ha : a ∈ Metric.ball (0 : ℂ) (r : ℝ)) :
    (standardCirclePath r).closedPathIndexAt a
      (standardCirclePath_not_mem_range_of_mem_ball r ha) = 1 :=
  sorry
