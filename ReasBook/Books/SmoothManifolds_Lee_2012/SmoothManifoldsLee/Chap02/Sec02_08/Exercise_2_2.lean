import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_06.Definition_1_6_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace ChartedSpace IsManifold
open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uN

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type uH'} [TopologicalSpace H']
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}

/-- Exercise 2.2 (1): for an open submanifold `U ⊆ ℝ^n`, smoothness of the restricted map
`U → ℝ^k` in the manifold sense is equivalent to ordinary smoothness on the ambient open set. -/
theorem contMDiff_open_submanifold_euclidean_iff_contDiffOn
    {n k : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k)} :
    ContMDiff (𝓡 n) (𝓡 k) ∞ (fun x : U ↦ f x) ↔
      ContDiffOn ℝ ∞ f (U : Set (EuclideanSpace ℝ (Fin n))) := by
  constructor
  · intro hf x hx
    exact (contMDiffAt_subtype_iff.mp (hf ⟨x, hx⟩)).contDiffAt.contDiffWithinAt
  · intro hf x
    exact contMDiffAt_subtype_iff.mpr <|
      (contMDiffOn_iff_contDiffOn.mpr hf).contMDiffAt (U.isOpen.mem_nhds x.2)

/-- Exercise 2.2 (2): for an open submanifold with boundary `U ⊆ 𝕳^n`, smoothness of the
restricted map `U → ℝ^k` in the manifold-with-boundary sense is equivalent to Lee's local smooth
ambient-extension criterion on the corresponding open subset of the Euclidean half-space. -/
theorem contMDiff_open_submanifold_halfspace_iff_forall_exists_smoothAmbientExtension
    {n k : ℕ} [NeZero n] {U : Opens (EuclideanHalfSpace n)}
    {f : EuclideanHalfSpace n → EuclideanSpace ℝ (Fin k)} :
    ContMDiff (𝓡∂ n) (𝓡 k) ∞ (fun x : U ↦ f x) ↔
      ∀ x ∈ (U : Set (EuclideanHalfSpace n)),
        ∃ V : Set (EuclideanSpace ℝ (Fin n)),
          IsOpen V ∧
          x.1 ∈ V ∧
          ((𝓡∂ n) ⁻¹' V) ⊆ (U : Set (EuclideanHalfSpace n)) ∧
          ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k),
            ContDiffOn ℝ ∞ g V ∧
            Set.EqOn (fun z : EuclideanHalfSpace n ↦ g z.1) f ((𝓡∂ n) ⁻¹' V) := by
  have hsub :
      ContMDiff (𝓡∂ n) (𝓡 k) ∞ (fun x : U ↦ f x) ↔
        ContMDiffOn (𝓡∂ n) (𝓡 k) ∞ f (U : Set (EuclideanHalfSpace n)) := by
    constructor
    · intro hf x hx
      exact (contMDiffAt_subtype_iff.mp (hf ⟨x, hx⟩)).contMDiffWithinAt
    · intro hf x
      exact contMDiffAt_subtype_iff.mpr <| hf.contMDiffAt (U.isOpen.mem_nhds x.2)
  exact hsub.trans <|
    contMDiffOn_halfSpace_iff_forall_exists_smoothAmbientExtension U.isOpen
