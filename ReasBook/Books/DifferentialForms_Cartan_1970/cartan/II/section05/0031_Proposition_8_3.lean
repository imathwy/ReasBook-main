import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0026_Definition_II_1_extra_16»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0027_Remark_II_1_extra_17»

open scoped unitInterval

-- Declarations for this item will be appended below by the statement pipeline.

namespace Path

variable {a b c d : ℂ} {γ : Path a b} {γ₁ : Path c d}

-- Proof sketch: if `γ t = 0`, then `‖γ₁ t‖ < ‖γ t‖ = 0`, impossible.
/-- A perturbation of strictly smaller modulus forces the original path to avoid the origin. -/
theorem ne_zero_of_abs_lt
    (hγ₁ : ∀ t : I, ‖γ₁ t‖ < ‖γ t‖) (t : I) :
    γ t ≠ 0 := by
  intro hγ
  have : ‖γ₁ t‖ < 0 := by simpa [hγ] using hγ₁ t
  exact (not_lt_of_ge (norm_nonneg _)) this

-- Proof sketch: apply `ne_zero_of_abs_lt` pointwise along the range of `γ`.
/-- A perturbation of strictly smaller modulus implies that the original path avoids the origin. -/
theorem zero_not_mem_range_of_abs_lt
    (hγ₁ : ∀ t : I, ‖γ₁ t‖ < ‖γ t‖) :
    0 ∉ Set.range γ := by
  intro h0
  rcases h0 with ⟨t, ht⟩
  exact ne_zero_of_abs_lt hγ₁ t ht

-- Proof sketch: if `γ t + γ₁ t = 0`, then `γ t = -γ₁ t`, hence
-- `‖γ t‖ = ‖γ₁ t‖`, contradicting the strict inequality hypothesis.
/-- A pointwise perturbation of strictly smaller modulus cannot cancel the original path. -/
theorem add_ne_zero_of_abs_lt
    (hγ₁ : ∀ t : I, ‖γ₁ t‖ < ‖γ t‖) (t : I) :
    γ.add γ₁ t ≠ 0 := by
  intro h_add
  have h_norm : ‖γ t‖ = ‖γ₁ t‖ := by
    calc
      ‖γ t‖ = ‖-γ₁ t‖ := by
        congr
        simpa using eq_neg_of_add_eq_zero_left h_add
      _ = ‖γ₁ t‖ := norm_neg _
  have : ‖γ t‖ < ‖γ t‖ := by
    simpa [h_norm] using hγ₁ t
  exact lt_irrefl _ this

-- Proof sketch: apply `add_ne_zero_of_abs_lt` pointwise along the range of `γ.add γ₁`.
/-- A perturbation of strictly smaller modulus keeps the perturbed path away from the origin. -/
theorem zero_not_mem_range_add_of_abs_lt
    (hγ₁ : ∀ t : I, ‖γ₁ t‖ < ‖γ t‖) :
    0 ∉ Set.range (γ.add γ₁) := by
  intro h0
  rcases h0 with ⟨t, ht⟩
  exact add_ne_zero_of_abs_lt hγ₁ t ht

variable {z z₁ : ℂ} {γ : Path z z} {γ₁ : Path z₁ z₁}

/-- Helper for Proposition 8.3: scaling the perturbation by a unit-interval parameter preserves the
strict norm domination hypothesis. -/
theorem smul_norm_lt_norm_of_abs_lt
    (hγ₁ : ∀ t : I, ‖γ₁ t‖ < ‖γ t‖) (s t : I) :
    ‖((s : ℂ) * γ₁ t)‖ < ‖γ t‖ := by
  -- The scalar factor from `I` has norm at most `1`, so it cannot enlarge the perturbation.
  have hs : ‖(s : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.2.1] using s.2.2
  have hmul : ‖(s : ℂ)‖ * ‖γ₁ t‖ ≤ ‖γ₁ t‖ := by
    nlinarith [norm_nonneg (γ₁ t), hs]
  calc
    ‖((s : ℂ) * γ₁ t)‖ = ‖(s : ℂ)‖ * ‖γ₁ t‖ := norm_mul _ _
    _ ≤ ‖γ₁ t‖ := hmul
    _ < ‖γ t‖ := hγ₁ t

/-- Helper for Proposition 8.3: every intermediate loop in the linear homotopy avoids the
origin. -/
theorem add_smul_ne_zero_of_abs_lt
    (hγ₁ : ∀ t : I, ‖γ₁ t‖ < ‖γ t‖) (s t : I) :
    γ t + (s : ℂ) * γ₁ t ≠ 0 := by
  intro h_add
  -- If the sum vanished, the original point would have the same norm as the scaled perturbation.
  have h_norm : ‖γ t‖ = ‖(s : ℂ) * γ₁ t‖ := by
    calc
      ‖γ t‖ = ‖-((s : ℂ) * γ₁ t)‖ := by
        congr
        simpa using eq_neg_of_add_eq_zero_left h_add
      _ = ‖(s : ℂ) * γ₁ t‖ := norm_neg _
  have : ‖(s : ℂ) * γ₁ t‖ < ‖(s : ℂ) * γ₁ t‖ := by
    simpa [h_norm] using smul_norm_lt_norm_of_abs_lt hγ₁ s t
  exact lt_irrefl _ this

/-- Helper for Proposition 8.3: the straight-line deformation from `γ` to `γ + γ₁` stays inside
`ℂ \ {0}` and consists of closed loops. -/
theorem closedPathHomotopicIn_add_of_abs_lt
    (hγ₁ : ∀ t : I, ‖γ₁ t‖ < ‖γ t‖) :
    ClosedPathHomotopicIn ({0} : Set ℂ)ᶜ γ (γ.add γ₁) := by
  -- Build the linear homotopy `H(s,t) = γ(t) + s • γ₁(t)` and verify each slice is a closed loop
  -- in the punctured plane.
  refine ⟨{ toHomotopy := ?_, prop' := ?_ }⟩
  · refine
      { toFun := fun p ↦ γ p.2 + (p.1 : ℂ) * γ₁ p.2
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_ }
    · continuity
    · intro t
      simp
    · intro t
      simp
  · intro s
    rw [isClosedPathIn_compl_iff]
    constructor
    · -- The endpoints remain fixed because both `γ` and `γ₁` are loops.
      change γ 0 + (s : ℂ) * γ₁ 0 = γ 1 + (s : ℂ) * γ₁ 1
      simp
    · intro t
      -- The domination estimate prevents cancellation with the origin at every intermediate time.
      simpa using add_smul_ne_zero_of_abs_lt hγ₁ s t

-- Proof sketch: form the loop `t ↦ 1 + γ₁ t / γ t`, show it has index `0` at the origin because
-- its image lies in the open disc centered at `1` of radius `1`, identify `γ.add γ₁` with the
-- pointwise product of `γ` and this auxiliary loop, and apply Proposition 8.2.
/-- Proposition 8.3: adding a pointwise perturbation of strictly smaller modulus preserves the
winding index about `0`. -/
theorem closedPathIndex_add_eq_of_abs_lt
    (hγ₁ : ∀ t : I, ‖γ₁ t‖ < ‖γ t‖) :
    closedPathIndex (γ.add γ₁) ⟨0, zero_not_mem_range_add_of_abs_lt hγ₁⟩ =
      closedPathIndex γ ⟨0, zero_not_mem_range_of_abs_lt hγ₁⟩ := by
  -- The executable source-faithful core is the straight-line deformation from `γ` to `γ + γ₁`
  -- through loops avoiding `0`, after which the existing homotopy-invariance theorem finishes.
  let hHomotopic : ClosedPathHomotopicIn ({0} : Set ℂ)ᶜ γ (γ.add γ₁) :=
    closedPathHomotopicIn_add_of_abs_lt hγ₁
  have hIndex :
      γ.closedPathIndexAt 0
          (not_mem_range_left_of_closedPathHomotopicIn_compl_singleton hHomotopic) =
        (γ.add γ₁).closedPathIndexAt 0
          (not_mem_range_right_of_closedPathHomotopicIn_compl_singleton hHomotopic) :=
    closedPathIndex_eq_of_homotopic_avoiding_point hHomotopic
  simpa [Path.closedPathIndexAt_def] using hIndex.symm

end Path
