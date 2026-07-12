import Mathlib.Geometry.Manifold.ContMDiff.Constructions

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uι uE uH uM uF uG uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {ι : Type uι} [Fintype ι]
variable {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
variable {H : ι → Type uH} [∀ i, TopologicalSpace (H i)]
variable {I : (i : ι) → ModelWithCorners 𝕜 (E i) (H i)}
variable {M : ι → Type uM} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type uG} [TopologicalSpace G]
variable {J : ModelWithCorners 𝕜 F G}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]

/- Proposition 2.12: a map into a finite product manifold is smooth if and only if all component
maps are smooth. The core owner theorem is mathlib's `contMDiff_pi_space`; this chapter theorem is
the source-facing bridge from product model spaces to the canonical manifold owner
`ContMDiff J (ModelWithCorners.pi I) ∞ Φ`. -/
theorem contMDiff_pi_iff {Φ : N → ∀ i : ι, M i} :
    ContMDiff J (ModelWithCorners.pi I) ∞ Φ ↔
      ∀ i : ι, ContMDiff J (I i) ∞ (fun x ↦ Φ x i) := by
  constructor
  · intro h i x
    have hx := h x
    rw [contMDiffAt_iff_target] at hx ⊢
    constructor
    · exact (continuous_apply i).continuousAt.comp hx.1
    · exact contMDiffAt_pi_space.1 hx.2 i
  · intro h x
    rw [contMDiffAt_iff_target]
    constructor
    · exact continuousAt_pi.2 fun i ↦ (h i x).continuousAt
    · refine contMDiffAt_pi_space.2 ?_
      intro i
      exact (contMDiffAt_iff_target.1 (h i x)).2
