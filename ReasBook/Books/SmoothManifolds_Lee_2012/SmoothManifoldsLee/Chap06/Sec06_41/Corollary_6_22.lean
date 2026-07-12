import Mathlib.Geometry.Manifold.SmoothApprox

-- Declarations for this item will be appended below by the statement pipeline.
-- Domain sampling pass:
-- * source-facing layer: a positive smooth minorant for a positive continuous scalar function.
-- * core/canonical owner: `Continuous.exists_contMDiff_approx`.
-- * derived API used here: bundled smooth maps `C^∞⟮I, M; ℝ⟯`.

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

-- Semantic recall note: this corollary is implemented directly from the canonical Whitney
-- approximation owner `Continuous.exists_contMDiff_approx`.

/-- Corollary 6.22: if `δ : M → ℝ` is a positive continuous function on a smooth manifold with or
without boundary, then there exists a smooth function `e : M → ℝ` such that `0 < e x < δ x` for
every `x : M`. -/
theorem exists_positive_smooth_lt
    {δ : M → ℝ} (hδ_cont : Continuous δ) (hδ_pos : ∀ x : M, 0 < δ x) :
    ∃ e : C^∞⟮I, M; ℝ⟯, ∀ x : M, 0 < e x ∧ e x < δ x := by
  let δhalf : M → ℝ := fun x ↦ (1 / 2 : ℝ) * δ x
  have hδhalf_cont : Continuous δhalf := continuous_const.mul hδ_cont
  have hδhalf_pos : ∀ x : M, 0 < δhalf x := fun x ↦ mul_pos one_half_pos (hδ_pos x)
  obtain ⟨e, he_approx, -⟩ :=
    hδhalf_cont.exists_contMDiff_approx I (⊤ : ℕ∞) hδhalf_cont hδhalf_pos
  refine ⟨e, fun x ↦ ?_⟩
  have hx : |e x - δhalf x| < δhalf x := by
    simpa [Real.dist_eq] using he_approx x
  have hx' := abs_lt.mp hx
  constructor
  · linarith [hx'.1]
  · dsimp [δhalf] at hx' ⊢
    linarith [hx'.2]

end

end Manifold
