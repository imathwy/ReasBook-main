import SmoothManifolds_Lee_2012.Chap02.Sec02_11.Definition_2_11_extra_2
import Mathlib.Geometry.Manifold.PartitionOfUnity

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe uE uH uM

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- Lemma 2.26 (Extension Lemma for Smooth Functions): if `A` is a closed subset of a smooth
manifold `M`, `f : A → EuclideanSpace ℝ (Fin k)` is smooth in the sense of
`Function.IsSmoothOn`, and `U` is an open set containing `A`, then `f` extends to a global smooth
map on `M` whose topological support is contained in `U`. -/
theorem exists_supported_contMDiffMap_extension_of_isClosed
    {A U : Set M} (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U)
    {k : ℕ} (f : A → EuclideanSpace ℝ (Fin k))
    (hf : f.IsSmoothOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k))) :
    ∃ F : C^∞⟮I, M; 𝓘(ℝ, EuclideanSpace ℝ (Fin k)), EuclideanSpace ℝ (Fin k)⟯,
      (∀ x : A, F x = f x) ∧ tsupport F ⊆ U := sorry
