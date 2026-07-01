import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_5
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_14
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_2

-- Declarations for this item will be appended below by the statement pipeline.

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
