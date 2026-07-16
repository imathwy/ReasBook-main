import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_11.Theorem_2_29
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_41.Corollary_6_22

-- Declarations for this item will be appended below by the statement pipeline.
-- Domain sampling pass:
-- * source-facing layer: a smooth real-valued function that vanishes on a closed set, is positive
--   away from it, and lies below a prescribed positive continuous function.
-- * core/canonical owners used here: `exists_nonneg_smooth_zero_set_eq_of_isClosed` for the
--   closed zero-set factor, and `exists_positive_smooth_lt` for the positive smooth minorant.
-- * primitive data: a bundled smooth map `C^∞⟮I, M; ℝ⟯`.
-- * derived API: the vanishing, positivity-off, and pointwise upper-bound clauses, stated
--   directly instead of via a local wrapper class.

open scoped ContDiff Manifold

namespace Manifold

section

universe uE uH uM

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- Problem 6-3: if `B ⊆ M` is closed and `δ : M → ℝ` is continuous and strictly positive, then
there exists a smooth function `δ̃ : M → ℝ` that vanishes on `B`, is positive on `M \ B`, and
satisfies `δ̃ x < δ x` for every `x : M`. -/
theorem exists_smooth_zero_on_and_positive_off_lt_of_isClosed
    {B : Set M} (hB : IsClosed B) {δ : M → ℝ} (hδ_cont : Continuous δ)
    (hδ_pos : ∀ x : M, 0 < δ x) :
    ∃ δtilde : C^∞⟮I, M; ℝ⟯,
      Set.EqOn δtilde (fun _ ↦ (0 : ℝ)) B ∧
      (∀ x : M, x ∉ B → 0 < δtilde x) ∧
      (∀ x : M, δtilde x < δ x) := by
  obtain ⟨f, hf_nonneg, hf_zero⟩ := exists_nonneg_smooth_zero_set_eq_of_isClosed I hB
  obtain ⟨e, he⟩ :
      ∃ e : C^∞⟮I, M; ℝ⟯, ∀ x : M, 0 < e x ∧ e x < δ x :=
    exists_positive_smooth_lt hδ_cont hδ_pos
  let r : C^∞⟮I, M; ℝ⟯ :=
    ⟨fun x ↦ f x / (1 + f x), by
      have hden_ne : ∀ x : M, 1 + f x ≠ 0 := fun x ↦ by
        linarith [hf_nonneg x]
      exact f.2.div₀ (contMDiff_const.add f.2) hden_ne⟩
  refine ⟨r * e, ?_, ?_, ?_⟩
  · intro x hx
    have hfx_zero : f x = 0 := by
      have hx_zero : x ∈ f ⁻¹' ({0} : Set ℝ) := by
        rw [hf_zero]
        exact hx
      simpa using hx_zero
    simp [r, hfx_zero]
  · intro x hx
    have hfx_ne : f x ≠ 0 := by
      intro hfx_zero
      apply hx
      rw [← hf_zero]
      simp [hfx_zero]
    have hfx_pos : 0 < f x := lt_of_le_of_ne (hf_nonneg x) (Ne.symm hfx_ne)
    have hratio_pos : 0 < f x / (1 + f x) := by
      have hden_pos : 0 < 1 + f x := by
        linarith [hf_nonneg x]
      exact div_pos hfx_pos hden_pos
    exact mul_pos hratio_pos (he x).1
  · intro x
    have hden_pos : 0 < 1 + f x := by
      linarith [hf_nonneg x]
    have hratio_lt_one : f x / (1 + f x) < 1 := by
      refine (div_lt_one hden_pos).2 ?_
      linarith
    have hmul_lt : (f x / (1 + f x)) * e x < e x := by
      simpa using mul_lt_mul_of_pos_right hratio_lt_one (he x).1
    calc
      (r * e) x = (f x / (1 + f x)) * e x := by rfl
      _ < e x := hmul_lt
      _ < δ x := (he x).2

end

end Manifold
