import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_19_2_1 (from Chap04) -/
noncomputable section

section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {X : Type*} {Y : Type*}
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X]
variable [TopologicalSpace Y] [AddCommGroup Y] [Module 𝕜 Y]
variable [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y] [FiniteDimensional 𝕜 Y]
variable [HasPairing Y X 𝕜]

-- Canonical primal pairing orientation used by Fenchel-conjugate owners.
local instance : HasPairing X Y 𝕜 :=
  HasPairing.swap (X := Y) (Y := X) (L := 𝕜)
local instance : HasPairingSwap X Y 𝕜 where
  pairing_swap _ _ := rfl

namespace Set.IsPolyhedral

theorem hasPolyhedralEpigraph_supportFunction {C : Set X} (hC : C.IsPolyhedral 𝕜) :
    (δᵛ[WithTopBot 𝕜](· | C)).HasPolyhedralEpigraph := by
  have hindicator : (δ[𝕜](· | C)).HasPolyhedralEpigraph :=
    Set.IsPolyhedral.hasPolyhedralEpigraph_indicator hC
  have hconj : ((δ[𝕜](· | C))⋆).HasPolyhedralEpigraph :=
    hindicator.convexConjugate
  have hsupport_eq :
      ((δ[𝕜](· | C))⋆) = (δᵛ[WithTopBot 𝕜](· | C)) := by
    simpa using
      (convexConjugate_indicator_eq_supportFunction (C := C))
  exact hsupport_eq ▸ hconj

end Set.IsPolyhedral

variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]

variable [ClosedIciTopology 𝕜]
variable [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]

namespace Function.HasPolyhedralEpigraph

theorem isPolyhedral_closure_of_supportFunction {C : Set E}
    (hsupport : (δᵛ[WithTopBot 𝕜](· | C)).HasPolyhedralEpigraph)
    (hC_convex : Convex 𝕜 C) :
    (closure C).IsPolyhedral 𝕜 := by
  have hconj : ((δᵛ[WithTopBot 𝕜](· | C))⋆).HasPolyhedralEpigraph :=
    hsupport.convexConjugate
  have hconj_eq :
      ((δᵛ[WithTopBot 𝕜](· | C))⋆) = (δ[𝕜](· | closure C)) := by
    simpa using
      (convexConjugate_supportFunction_eq_indicatorFunction_closure (C := C) hC_convex)
  rw [hconj_eq] at hconj
  exact Function.HasPolyhedralEpigraph.isPolyhedral_indicator hconj

theorem isPolyhedral_of_supportFunction {C : Set E}
    (hsupport : (δᵛ[WithTopBot 𝕜](· | C)).HasPolyhedralEpigraph)
    (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C) :
    C.IsPolyhedral 𝕜 := by
  simpa [hC_closed.closure_eq] using hsupport.isPolyhedral_closure_of_supportFunction hC_convex

theorem isPolyhedral_intrinsicClosure_of_supportFunction {C : Set E}
    (hsupport : (δᵛ[WithTopBot 𝕜](· | C)).HasPolyhedralEpigraph)
    (hC_convex : Convex 𝕜 C)
    (hC_affineSpan_closed : IsClosed (affineSpan 𝕜 C : Set E)) :
    (intrinsicClosure 𝕜 C).IsPolyhedral 𝕜 := by
  simpa [Set.intrinsicClosure_eq_closure_of_isClosed_affineSpan (𝕜 := 𝕜) (C := C)
    hC_affineSpan_closed] using
    hsupport.isPolyhedral_closure_of_supportFunction hC_convex

end Function.HasPolyhedralEpigraph

/-- Intrinsic owner form: under closed affine span, polyhedrality of the intrinsic closure is
equivalent to polyhedrality of the support-function epigraph. -/
theorem isPolyhedral_intrinsicClosure_iff_hasPolyhedralEpigraph_supportFunction
    (C : Set E) (hC_convex : Convex 𝕜 C)
    (hC_affineSpan_closed : IsClosed (affineSpan 𝕜 C : Set E)) :
    (intrinsicClosure 𝕜 C).IsPolyhedral 𝕜 ↔
      (δᵛ[WithTopBot 𝕜](· | C)).HasPolyhedralEpigraph := by
  constructor
  · intro hC_intrinsicClosure
    have hsupport_intrinsicClosure :
        (δᵛ[WithTopBot 𝕜](· | intrinsicClosure 𝕜 C)).HasPolyhedralEpigraph :=
      hC_intrinsicClosure.hasPolyhedralEpigraph_supportFunction
    have hclosure_eq : closure (intrinsicClosure 𝕜 C) = closure C := by
      refine Set.Subset.antisymm ?_ ?_
      · simpa [closure_closure] using
          (closure_mono (intrinsicClosure_subset_closure (𝕜 := 𝕜) (s := C)))
      · exact closure_mono (subset_intrinsicClosure (𝕜 := 𝕜) (s := C))
    have hsupport_eq :
        (δᵛ[WithTopBot 𝕜](· | intrinsicClosure 𝕜 C)) =
          (δᵛ[WithTopBot 𝕜](· | C)) :=
      supportFunction_eq_of_closure_eq (hCD := hclosure_eq)
    exact hsupport_eq ▸ hsupport_intrinsicClosure
  · intro hsupport
    exact hsupport.isPolyhedral_intrinsicClosure_of_supportFunction hC_convex
      hC_affineSpan_closed

/-- Ambient-closure owner form: for a convex set, polyhedrality of `closure C` is equivalent to
polyhedrality of the support-function epigraph. -/
theorem isPolyhedral_closure_iff_hasPolyhedralEpigraph_supportFunction
    (C : Set E) (hC_convex : Convex 𝕜 C) :
    (closure C).IsPolyhedral 𝕜 ↔
      (δᵛ[WithTopBot 𝕜](· | C)).HasPolyhedralEpigraph := by
  constructor
  · intro hclosure_polyhedral
    have hsupport_closure :
        (δᵛ[WithTopBot 𝕜](· | closure C)).HasPolyhedralEpigraph :=
      hclosure_polyhedral.hasPolyhedralEpigraph_supportFunction
    have hsupport_eq :
        (δᵛ[WithTopBot 𝕜](· | closure C)) = (δᵛ[WithTopBot 𝕜](· | C)) :=
      supportFunction_eq_of_closure_eq (C := closure C) (D := C) (by
        simp [closure_closure])
    exact hsupport_eq ▸ hsupport_closure
  · intro hsupport
    exact hsupport.isPolyhedral_closure_of_supportFunction hC_convex

/-- Corollary 19.2.1: for a closed convex set, set-side polyhedrality is equivalent to
polyhedrality of the support function epigraph. -/
theorem isPolyhedral_iff_hasPolyhedralEpigraph_supportFunction
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C) :
    C.IsPolyhedral 𝕜 ↔
      (δᵛ[WithTopBot 𝕜](· | C)).HasPolyhedralEpigraph := by
  constructor
  · intro hC_polyhedral
    exact hC_polyhedral.hasPolyhedralEpigraph_supportFunction
  · intro hsupport
    exact hsupport.isPolyhedral_of_supportFunction hC_closed hC_convex

end

/-! ### Corollary_19_2_2 (from Chap04) -/
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

/-! ### Theorem_19_2 (from Chap04) -/
noncomputable section

section

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 19.2 says that the Fenchel conjugate of a polyhedral convex function on
  a finite-dimensional pairing space is again polyhedral convex on the dual side.
- `core/canonical`: the primitive owner theorem in this file is on
  `Function.HasFinitelyGeneratedConvexEpigraph`; the source-facing theorem is then obtained by
  the Chapter 19.1.2 bridge between polyhedral and finitely generated epigraph owners.
- `bridge/view`: Corollary 19.1.2 already identifies the source-facing polyhedrality predicate
  `Function.HasPolyhedralEpigraph` with
  `Function.HasFinitelyGeneratedConvexEpigraph`, so this file reuses that bridge instead of
  introducing a parallel wrapper owner.

Domain-style sampling used here:
- conjugate notation `f⋆`;
- `Function.HasFinitelyGeneratedConvexEpigraph`.
- `Function.HasPolyhedralEpigraph.hasFinitelyGeneratedConvexEpigraph`;
- `Function.HasFinitelyGeneratedConvexEpigraph.hasPolyhedralEpigraph`.

Primitive data vs derived API:
- primitive input: the function `f : X → WithTopBot 𝕜` on the chapter's ordered extended codomain;
- core owner datum and output: finite generation of `epi f` and `epi (f⋆)`;
- source-facing bridge input/output: polyhedral epigraphs of `f` and `f⋆` on the dual pairing
  space.

Layer target: core theorem first, then source-facing bridge theorem.
-/

variable {𝕜 : Type*} {X : Type*} {XStar : Type*}

namespace Function.HasFinitelyGeneratedConvexEpigraph

variable [Ring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid XStar] [Module 𝕜 XStar]
variable [HasPairing X XStar 𝕜]

/-- Theorem 19.2, core owner form: finitely generated convex epigraphs are preserved by Fenchel
conjugation at the primitive pairing layer. -/
theorem convexConjugate
    {f : X → WithTopBot 𝕜} (hf : f.HasFinitelyGeneratedConvexEpigraph) :
    (f⋆).HasFinitelyGeneratedConvexEpigraph := by
  sorry

end Function.HasFinitelyGeneratedConvexEpigraph

section PolyhedralBridge

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasPairing X XStar 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X]
  [FiniteDimensional 𝕜 X]
variable [TopologicalSpace XStar] [IsTopologicalAddGroup XStar] [ContinuousSMul 𝕜 XStar]
  [FiniteDimensional 𝕜 XStar]

namespace Function.HasPolyhedralEpigraph

/-- Theorem 19.2, source-facing owner form: the Fenchel conjugate of a function with polyhedral
epigraph is again polyhedral at the intrinsic Chapter 19 owner layer. -/
theorem convexConjugate
    {f : X → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) :
    (f⋆).HasPolyhedralEpigraph := by
  exact (hf.hasFinitelyGeneratedConvexEpigraph.convexConjugate).hasPolyhedralEpigraph

end Function.HasPolyhedralEpigraph

end PolyhedralBridge

end
