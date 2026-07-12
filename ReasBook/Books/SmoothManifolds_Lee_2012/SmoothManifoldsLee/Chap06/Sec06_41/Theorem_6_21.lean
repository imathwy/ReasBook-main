import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothApprox
import SmoothManifolds_Lee_2012.Chap02.Sec02_11.Lemma_2_26
import SmoothManifolds_Lee_2012.Chap06.Sec06_41.Definition_6_41_extra_1

-- Declarations for this item will be appended below by the statement pipeline.
-- Domain sampling pass:
-- * source-facing layer: this theorem is the relative Whitney approximation statement for maps
--   smooth on a closed subset.
-- * core/canonical owner: `Continuous.exists_contMDiff_approx_and_eqOn` from mathlib's
--   `SmoothApprox`.
-- * bridge/view owners used here: the project owner `delta_close` for pointwise control and the
--   local closed-subset extension lemma translating Lee's `Function.IsSmoothOn` hypothesis into a
--   global smooth map on the closed set neighborhood.

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

variable {k : ℕ}

local notation "I_k" => 𝓘(ℝ, EuclideanSpace ℝ (Fin k))

/-- Theorem 6.21 (Whitney Approximation Theorem for Functions): if `F : M → ℝ^k` is continuous
and `δ : M → ℝ` is continuous and strictly positive, then for every closed subset `A ⊆ M` on
which `F` is smooth, there exists a smooth map `F̃ : M → ℝ^k` that agrees with `F` on `A` and is
pointwise `δ`-close to `F`. -/
theorem exists_smooth_approximation_eqOn_of_isClosed
    {F : M → EuclideanSpace ℝ (Fin k)} (hF : Continuous F)
    {δ : M → ℝ} (hδ_cont : Continuous δ) (hδ_pos : ∀ x : M, 0 < δ x)
    {A : Set M} (hA : IsClosed A)
    (hFA : (fun x : A ↦ F x).IsSmoothOn I I_k) :
    ∃ Ftilde : C^∞⟮I, M; I_k, EuclideanSpace ℝ (Fin k)⟯,
      Set.EqOn Ftilde F A ∧ delta_close δ Ftilde F := by
  obtain ⟨G, hG_eq, -⟩ :=
    exists_supported_contMDiffMap_extension_of_isClosed
      hA isOpen_univ (Set.subset_univ A) (fun x : A ↦ F x) hFA
  let D : M → EuclideanSpace ℝ (Fin k) := fun x ↦ F x - G x
  have hD_cont : Continuous D := hF.sub G.2.continuous
  obtain ⟨H, hH_approx, hH_support⟩ :=
    hD_cont.exists_contMDiff_approx I (⊤ : ℕ∞) hδ_cont hδ_pos
  refine ⟨⟨fun x ↦ G x + H x, G.2.add H.2⟩, ?_, ?_⟩
  · intro x hx
    have hHx : H x = 0 := by
      by_contra hHx
      exact (hH_support hHx) (by
        simpa [D] using sub_eq_zero.mpr (hG_eq ⟨x, hx⟩).symm)
    simpa [hHx] using hG_eq ⟨x, hx⟩
  · intro x
    have hGH : dist (G x + H x) (G x + D x) < δ x := by
      simpa using hH_approx x
    simpa [D, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hGH

end

end Manifold
