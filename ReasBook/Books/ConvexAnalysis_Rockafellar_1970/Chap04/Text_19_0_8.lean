import Mathlib
import Mathlib.Algebra.Order.Ring.Defs
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar

section CoreOwner

namespace Function

variable {𝕜 : Type*} [Semiring 𝕜] [Preorder 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type*} [AddCommMonoid α] [Module 𝕜 α] [Preorder α]

/-- Text 19.0.8 owner predicate at the primitive codomain/scalar layer:
polyhedrality of the intrinsic epigraph `epi f` for `f : E → WithTopBot α`. -/
abbrev HasPolyhedralEpigraph (f : E → WithTopBot α) : Prop :=
  (epi f).IsPolyhedral 𝕜

namespace HasPolyhedralEpigraph

/-- Owner-side theorem: `HasPolyhedralEpigraph` is exactly polyhedrality of `epi f`. -/
theorem isPolyhedral {f : E → WithTopBot α} (hf : f.HasPolyhedralEpigraph) :
    (epi f).IsPolyhedral 𝕜 :=
  hf

end HasPolyhedralEpigraph

end Function

end CoreOwner

section ConvexityLayer

variable {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type*} [AddCommMonoid α] [Module 𝕜 α] [PartialOrder α]

namespace Function.HasPolyhedralEpigraph

/-- A function with polyhedral epigraph is convex. -/
theorem isConvex {f : E → WithTopBot α} (hf : f.HasPolyhedralEpigraph) :
    f.IsConvex 𝕜 := by
  exact hf.isPolyhedral.convex

end Function.HasPolyhedralEpigraph

end ConvexityLayer

section IndicatorLayer

variable {𝕜 : Type*} [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]

namespace Set

/-- Set-owner bridge: the product with the nonnegative vertical ray is polyhedral
iff the base set is polyhedral. -/
private theorem isPolyhedral_prod_Ici_zero_iff (C : Set E) :
    (C ×ˢ Set.Ici (0 : 𝕜)).IsPolyhedral 𝕜 ↔ C.IsPolyhedral 𝕜 := by
  constructor
  · intro hprod
    classical
    rcases hprod with ⟨S, hS⟩
    let inlMap : E →ₗ[𝕜] E × 𝕜 := LinearMap.inl 𝕜 E 𝕜
    let projectedParams : Finset ((E →ₗ[𝕜] 𝕜) × 𝕜) :=
      S.image fun y ↦ (y.1.comp inlMap, y.2)
    refine ⟨projectedParams, ?_⟩
    ext x
    constructor
    · intro hx
      have hxS : ∀ y ∈ S, (x, (0 : 𝕜)) ∈ closedHalfSpaceLE y.1 y.2 := by
        have hxProd : (x, (0 : 𝕜)) ∈ C ×ˢ Set.Ici (0 : 𝕜) := by
          exact ⟨hx, by simp⟩
        rw [hS] at hxProd
        simpa [Set.mem_iInter] using hxProd
      simpa [Set.mem_iInter, inlMap, LinearMap.inl_apply, LinearMap.comp_apply] using
        (show ∀ z ∈ projectedParams, x ∈ closedHalfSpaceLE z.1 z.2 from by
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
          simpa [inlMap, LinearMap.inl_apply, LinearMap.comp_apply] using hxS y hy)
    · intro hx
      have hxProjected : ∀ z ∈ projectedParams, x ∈ closedHalfSpaceLE z.1 z.2 := by
        simpa [Set.mem_iInter] using hx
      have hxProd : (x, (0 : 𝕜)) ∈ C ×ˢ Set.Ici (0 : 𝕜) := by
        rw [hS]
        simpa [Set.mem_iInter, inlMap, LinearMap.inl_apply, LinearMap.comp_apply] using
          (show ∀ y ∈ S, (x, (0 : 𝕜)) ∈ closedHalfSpaceLE y.1 y.2 from by
            intro y hy
            have hyProjected : (y.1.comp inlMap, y.2) ∈ projectedParams :=
              Finset.mem_image.mpr ⟨y, hy, rfl⟩
            simpa [inlMap, LinearMap.inl_apply, LinearMap.comp_apply] using
              (hxProjected _ hyProjected))
      exact hxProd.1
  · intro hC
    classical
    rcases hC with ⟨S, hS⟩
    let fstMap : E × 𝕜 →ₗ[𝕜] E := LinearMap.fst 𝕜 E 𝕜
    let sndMap : E × 𝕜 →ₗ[𝕜] 𝕜 := LinearMap.snd 𝕜 E 𝕜
    let liftedParams : Finset ((E × 𝕜 →ₗ[𝕜] 𝕜) × 𝕜) :=
      S.image fun y ↦ (y.1.comp fstMap, y.2)
    let rayParam : (E × 𝕜 →ₗ[𝕜] 𝕜) × 𝕜 := (-sndMap, 0)
    refine ⟨insert rayParam liftedParams, ?_⟩
    ext p
    rw [hS]
    constructor
    · rintro ⟨hpC, hpμ⟩
      have hpS : ∀ y ∈ S, p.1 ∈ closedHalfSpaceLE y.1 y.2 := by
        simpa [Set.mem_iInter] using hpC
      simpa [Set.mem_iInter, fstMap, sndMap, rayParam, liftedParams,
        LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply] using
        (show ∀ z ∈ insert rayParam liftedParams, p ∈ closedHalfSpaceLE z.1 z.2 from by
          intro z hz
          rcases Finset.mem_insert.mp hz with hzRay | hzLift
          · subst hzRay
            have hp2 : (0 : 𝕜) ≤ p.2 := hpμ
            have hneg : -p.2 ≤ (0 : 𝕜) := neg_nonpos.mpr hp2
            change (-LinearMap.snd 𝕜 E 𝕜 p) ≤ (0 : 𝕜)
            simpa [LinearMap.snd_apply] using hneg
          · rcases Finset.mem_image.mp hzLift with ⟨y, hy, rfl⟩
            simpa [fstMap, LinearMap.fst_apply, LinearMap.comp_apply] using hpS y hy)
    · intro hp
      have hpAll : ∀ z ∈ insert rayParam liftedParams, p ∈ closedHalfSpaceLE z.1 z.2 := by
        simpa [Set.mem_iInter] using hp
      have hpμ : p.2 ∈ Set.Ici (0 : 𝕜) := by
        have hray : p ∈ closedHalfSpaceLE rayParam.1 rayParam.2 :=
          hpAll rayParam (Finset.mem_insert_self rayParam liftedParams)
        have hneg : -p.2 ≤ (0 : 𝕜) := by
          change (-LinearMap.snd 𝕜 E 𝕜 p) ≤ (0 : 𝕜) at hray
          simpa [LinearMap.snd_apply] using hray
        exact neg_nonpos.mp hneg
      have hpC : p.1 ∈ ⋂ y ∈ S, closedHalfSpaceLE y.1 y.2 := by
        simpa [Set.mem_iInter] using
          (show ∀ y ∈ S, p.1 ∈ closedHalfSpaceLE y.1 y.2 from by
            intro y hy
            have hyLift : (y.1.comp fstMap, y.2) ∈ liftedParams :=
              Finset.mem_image.mpr ⟨y, hy, rfl⟩
            have hpy : p ∈ closedHalfSpaceLE (y.1.comp fstMap) y.2 :=
              hpAll _ (Finset.mem_insert.mpr <| Or.inr hyLift)
            simpa [fstMap, LinearMap.fst_apply, LinearMap.comp_apply] using hpy)
      exact ⟨hpC, hpμ⟩

end Set

namespace Function.HasPolyhedralEpigraph

/-- Canonical owner bridge for indicators: `δ[𝕜](· | C)` has polyhedral epigraph exactly
when `C` is polyhedral. -/
theorem indicator_iff_isPolyhedral (C : Set E) :
    (δ[𝕜](· | C)).HasPolyhedralEpigraph ↔ C.IsPolyhedral 𝕜 := by
  rw [Function.HasPolyhedralEpigraph, epi_indicator_eq_prod]
  exact Set.isPolyhedral_prod_Ici_zero_iff C

end Function.HasPolyhedralEpigraph

namespace Set

/-- Set-owner bridge for indicators: `C` is polyhedral iff the indicator of `C` has polyhedral
epigraph. -/
theorem isPolyhedral_iff_hasPolyhedralEpigraph_indicator (C : Set E) :
    C.IsPolyhedral 𝕜 ↔ (δ[𝕜](· | C)).HasPolyhedralEpigraph := by
  simpa using
    (Function.HasPolyhedralEpigraph.indicator_iff_isPolyhedral (C := C)).symm

end Set

namespace Set.IsPolyhedral

/-- Owner projection from a polyhedral base set to the indicator epigraph owner. -/
theorem hasPolyhedralEpigraph_indicator {C : Set E} (hC : C.IsPolyhedral 𝕜) :
    (δ[𝕜](· | C)).HasPolyhedralEpigraph :=
  (Set.isPolyhedral_iff_hasPolyhedralEpigraph_indicator C).1 hC

end Set.IsPolyhedral

namespace Function.HasPolyhedralEpigraph

/-- Owner projection from indicator-epigraph polyhedrality back to base-set polyhedrality. -/
theorem isPolyhedral_indicator {C : Set E}
    (hδ : (δ[𝕜](· | C)).HasPolyhedralEpigraph) :
    C.IsPolyhedral 𝕜 :=
  (Set.isPolyhedral_iff_hasPolyhedralEpigraph_indicator C).2 hδ

end Function.HasPolyhedralEpigraph

end IndicatorLayer

end
