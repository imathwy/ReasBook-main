import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5
import ConvexAnalysis_Rockafellar_1970.Chap04.Corollary_19_2_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar

namespace Function.HasPolyhedralEpigraph

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]

omit [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E] in
private theorem isPolyhedral_Iic (μ : 𝕜) : (Set.Iic μ : Set 𝕜).IsPolyhedral 𝕜 := by
  refine ⟨{((LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜), μ)}, ?_⟩
  ext t
  simp [closedHalfSpaceLE, HasLinearPairing.pairingLinear]

/-- A function with polyhedral epigraph has polyhedral scalar sublevel sets. -/
theorem isPolyhedral_preimage_Iic {f : E → WithTopBot 𝕜}
    (hf : f.HasPolyhedralEpigraph) (μ : 𝕜) :
    (f ⁻¹' Set.Iic (μ : WithTopBot 𝕜)).IsPolyhedral 𝕜 := by
  let fstMap : E × 𝕜 →ₗ[𝕜] E := LinearMap.fst 𝕜 E 𝕜
  let sndMap : E × 𝕜 →ₗ[𝕜] 𝕜 := LinearMap.snd 𝕜 E 𝕜
  have hsnd : (sndMap ⁻¹' (Set.Iic μ : Set 𝕜)).IsPolyhedral 𝕜 :=
    (isPolyhedral_Iic μ).linear_preimage sndMap
  have hcap : (epi f ∩ sndMap ⁻¹' (Set.Iic μ : Set 𝕜)).IsPolyhedral 𝕜 :=
    Set.IsPolyhedral.inter (𝕜 := 𝕜) hf hsnd
  have himageFG :
      (fstMap '' (epi f ∩ sndMap ⁻¹' (Set.Iic μ : Set 𝕜))).IsFinitelyGeneratedConvex 𝕜 :=
    hcap.isFinitelyGeneratedConvex.linear_image fstMap
  have himage : (fstMap '' (epi f ∩ sndMap ⁻¹' (Set.Iic μ : Set 𝕜))).IsPolyhedral 𝕜 :=
    himageFG.isPolyhedral
  have hEq :
      fstMap '' (epi f ∩ sndMap ⁻¹' (Set.Iic μ : Set 𝕜)) =
        f ⁻¹' Set.Iic (μ : WithTopBot 𝕜) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with ⟨hp_epi, hp_iic⟩
      have hfx : f p.1 ≤ (p.2 : WithTopBot 𝕜) := (mem_epi_iff.mp hp_epi)
      have hpμ : (p.2 : WithTopBot 𝕜) ≤ (μ : WithTopBot 𝕜) :=
        (WithTopBot.coe_le_coe).2 hp_iic
      simpa [Set.mem_preimage, Set.mem_Iic, fstMap, LinearMap.fst_apply] using hfx.trans hpμ
    · intro hx
      have hfx : f x ≤ (μ : WithTopBot 𝕜) := by
        simpa [Set.mem_preimage, Set.mem_Iic] using hx
      refine ⟨(x, μ), ?_, by simp [fstMap, LinearMap.fst_apply]⟩
      refine ⟨?_, ?_⟩
      · exact (mem_epi_iff).2 hfx
      · simp [Set.mem_preimage, Set.mem_Iic, sndMap]
  simpa [hEq] using himage

end Function.HasPolyhedralEpigraph

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
  [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X]
variable {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module 𝕜 Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y] [FiniteDimensional 𝕜 Y]

namespace Set.IsPolyhedral

variable [HasPairing Y X 𝕜]

/-- Corollary 19.2.2: the polar of a polyhedral set is polyhedral. -/
theorem polar {C : Set X} (hC : C.IsPolyhedral 𝕜) :
    (Cᵒ[𝕜]).IsPolyhedral 𝕜 := by
  have hsupport := hC.hasPolyhedralEpigraph_supportFunction
  simpa [Set.polar] using
    (hsupport.isPolyhedral_preimage_Iic (1 : 𝕜))

end Set.IsPolyhedral

end
