import Mathlib.Geometry.Manifold.SmoothEmbedding
import SmoothManifolds_Lee_2012.Chap04.Sec04_24.Exercise_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe u𝕜 uE uH uM uE' uH'

section ImmersionDerivedApi

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H}
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
variable {J : ModelWithCorners 𝕜 E' H'}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
variable {f : M → N}

namespace Manifold.IsImmersionAtOfComplement

/-- An immersion at a point is `C^n` at that point. -/
theorem contMDiffAt {x : M} (h : IsImmersionAtOfComplement F I J n f x) :
    ContMDiffAt I J n f x := by
  rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
    h.codChart_mem_maximalAtlas h.mem_domChart_source h.mem_codChart_source]
  simp only [Set.preimage_univ]
  refine ⟨h.ex416_continuousAt.continuousWithinAt, ?_⟩
  have hx :
      h.domChart.extend I x ∈ (h.domChart.extend I).target := by
    simpa using (h.domChart.extend I).map_source <| by
      simpa [OpenPartialHomeomorph.extend_source] using h.mem_domChart_source
  have hmodel :
      ContDiffWithinAt 𝕜 n (fun y : E ↦ h.equiv (y, (0 : F))) ((h.domChart.extend I).target)
        (h.domChart.extend I x) := by
    simpa [Function.comp] using
      (h.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E F)).contDiff.contDiffWithinAt
  simpa [Set.inter_univ] using
    (hmodel.congr_of_mem (fun y hy ↦ h.writtenInCharts hy) hx).congr_set
      (h.domChart.extend_target_eventuallyEq h.mem_domChart_source)

end Manifold.IsImmersionAtOfComplement

namespace Manifold.IsImmersionAt

/-- An immersion at a point is `C^n` at that point. -/
theorem contMDiffAt {x : M} (h : IsImmersionAt I J n f x) :
    ContMDiffAt I J n f x :=
  h.isImmersionAtOfComplement_complement.contMDiffAt

end Manifold.IsImmersionAt

namespace Manifold.IsImmersion

/-- An immersion is `C^n`. -/
theorem contMDiff (h : IsImmersion I J n f) : ContMDiff I J n f :=
  fun x ↦ (h.isImmersionAt x).contMDiffAt

end Manifold.IsImmersion

end ImmersionDerivedApi

section SubmanifoldsWithBoundary

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I ⊤ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable (J : ModelWithCorners 𝕜 E' H') (S : Set M)
variable [ChartedSpace H' S] [IsManifold J ⊤ S]

/- Definition 5.36-extra-1, immersed form: once the manifold-with-boundary structure on the
subtype `S` is fixed, the owner abstraction is the canonical immersion predicate for the subtype
inclusion. -/
#check Manifold.IsImmersion J I ⊤ (Subtype.val : S → M)

/- Definition 5.36-extra-1, embedded form: the corresponding embedded notion is the canonical
smooth-embedding predicate for the same subtype inclusion. -/
#check Manifold.IsSmoothEmbedding J I ⊤ (Subtype.val : S → M)

end SubmanifoldsWithBoundary
