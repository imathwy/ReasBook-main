import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_5
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_13
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

section IntrinsicInterior

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 6.5.1 states that if an affine set `M` meets the relative interior of
  a convex set `C`, then intersecting `C` with `M` preserves both relative interior and closure.
- `core/canonical`: the owner notions are `intrinsicInterior 𝕜`, `intrinsicClosure 𝕜`,
  `closure`, `Convex 𝕜`, and the affine-set owner object `AffineSubspace 𝕜 E`.
- `bridge/view`: Rockafellar's `ri` is formalized by notation `ri[𝕜](·)` over
  `intrinsicInterior 𝕜`; the textbook affine set `M` is represented canonically by an affine
  subspace and then coerced to a set.
- Primitive data vs derived API: the affine subspace `M` and convex set `C` are the input data,
  while the relative-interior and closure identities are derived geometric facts.
- Domain-style sampling used here: the chapter owner theorems
  `Convex.intrinsicInterior_iInter_eq_iInter_intrinsicInterior`,
  `Convex.intrinsicClosure_iInter_eq_iInter_intrinsicClosure`, and the bridge
  `intrinsicClosure_eq_closure`.
- Layer target: this item stays `source-facing`, but both displayed identities are thin affine
  specializations of the owner theorems from Theorem 6.5 rather than parallel local reproofs.
-/

namespace AffineSubspace

/-- Corollary 6.5.1 (1): if an affine set `M` meets the relative interior of a convex set `C`,
then the relative interior of `M ∩ C` is exactly `M ∩ ri[𝕜](C)`. -/
-- Proof sketch: view relative interior as `ri`. Because `M` meets
-- `ri C`, the affine spans of `M ∩ C` and `M ∩ ri C` agree with
-- the affine section cut out by `M`, and the intrinsic interior inside that affine section reduces
-- to ordinary interior in the subtype corresponding to `M`.
theorem intrinsicInterior_inter_eq (M : AffineSubspace 𝕜 E) {C : Set E} [FiniteDimensional 𝕜 E]
    (hC : Convex 𝕜 C)
    (hri : ((M : Set E) ∩ ri[𝕜](C)).Nonempty) :
    ri[𝕜]((M : Set E) ∩ C) = (M : Set E) ∩ ri[𝕜](C) := by
  have hMri : ri[𝕜]((M : Set E)) = (M : Set E) := M.intrinsicInterior_coe
  let D : Bool → Set E := fun b ↦ cond b (M : Set E) C
  have hDconv : ∀ b : Bool, Convex 𝕜 (D b) := by
    intro b
    cases b
    · simpa [D] using hC
    · simpa [D] using M.convex
  have hDri : (⋂ b : Bool, ri[𝕜](D b)).Nonempty := by
    rcases hri with ⟨x, hxM, hxC⟩
    refine ⟨x, Set.mem_iInter.2 fun b ↦ ?_⟩
    cases b
    · simpa [D] using hxC
    · simpa [D, hMri] using hxM
  calc
    ri[𝕜]((M : Set E) ∩ C) = ri[𝕜](⋂ b : Bool, D b) := by
      rw [Set.inter_eq_iInter]
    _ = ⋂ b : Bool, ri[𝕜](D b) := by
      simpa [D] using Convex.intrinsicInterior_iInter_eq_iInter_intrinsicInterior hDconv hDri
    _ = (M : Set E) ∩ ri[𝕜](C) := by
      ext x
      constructor
      · intro hx
        refine ⟨?_, ?_⟩
        · simpa [D, hMri] using (Set.mem_iInter.1 hx) true
        · simpa [D] using (Set.mem_iInter.1 hx) false
      · rintro ⟨hxM, hxC⟩
        refine Set.mem_iInter.2 fun b ↦ ?_
        cases b
        · simpa [D] using hxC
        · simpa [D, hMri] using hxM

end AffineSubspace

end IntrinsicInterior

section IntrinsicClosure

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]

namespace AffineSubspace

/-- Intrinsic-closure companion to Corollary 6.5.1: if an affine set `M` meets `ri[𝕜](C)` for a
convex set `C`, then the intrinsic closure of `M ∩ C` is exactly
`M ∩ cl[𝕜](C)`. -/
theorem intrinsicClosure_inter_eq (M : AffineSubspace 𝕜 E) {C : Set E} (hC : Convex 𝕜 C)
    (hri : ((M : Set E) ∩ ri[𝕜](C)).Nonempty) :
    cl[𝕜]((M : Set E) ∩ C) = (M : Set E) ∩ cl[𝕜](C) := by
  have hMri : ri[𝕜]((M : Set E)) = (M : Set E) := M.intrinsicInterior_coe
  have hMicl : cl[𝕜]((M : Set E)) = (M : Set E) := M.intrinsicClosure_coe
  let D : Bool → Set E := fun b ↦ cond b (M : Set E) C
  have hDconv : ∀ b : Bool, Convex 𝕜 (D b) := by
    intro b
    cases b
    · simpa [D] using hC
    · simpa [D] using M.convex
  have hDri : (⋂ b : Bool, ri[𝕜](D b)).Nonempty := by
    rcases hri with ⟨x, hxM, hxC⟩
    refine ⟨x, Set.mem_iInter.2 fun b ↦ ?_⟩
    cases b
    · simpa [D] using hxC
    · simpa [D, hMri] using hxM
  calc
    cl[𝕜]((M : Set E) ∩ C) = cl[𝕜](⋂ b : Bool, D b) := by
      rw [Set.inter_eq_iInter]
    _ = ⋂ b : Bool, cl[𝕜](D b) := by
      simpa [D] using Convex.intrinsicClosure_iInter_eq_iInter_intrinsicClosure hDconv hDri
    _ = (M : Set E) ∩ cl[𝕜](C) := by
      ext x
      constructor
      · intro hx
        refine ⟨?_, ?_⟩
        · simpa [D, hMicl] using (Set.mem_iInter.1 hx) true
        · simpa [D] using (Set.mem_iInter.1 hx) false
      · rintro ⟨hxM, hxC⟩
        refine Set.mem_iInter.2 fun b ↦ ?_
        cases b
        · simpa [D] using hxC
        · simpa [D, hMicl] using hxM

end AffineSubspace

end IntrinsicClosure

section ClosureIsClosedAffineSpan

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]

namespace AffineSubspace

/-- Primitive ambient-closure form of Corollary 6.5.1 (2): if an affine set `M` meets
`ri[𝕜](C)` for a convex set `C`, and the affine hulls `aff[𝕜] C` and `aff[𝕜] (M ∩ C)` are closed,
then
`closure (M ∩ C) = M ∩ closure C`. -/
theorem closure_inter_eq_of_isClosed_affineSpan (M : AffineSubspace 𝕜 E) {C : Set E}
    (hC : Convex 𝕜 C) (hri : ((M : Set E) ∩ ri[𝕜](C)).Nonempty)
    (hclosedC : IsClosed (aff[𝕜] C : Set E))
    (hclosedInter : IsClosed (aff[𝕜] ((M : Set E) ∩ C) : Set E)) :
    closure ((M : Set E) ∩ C) = (M : Set E) ∩ closure C := by
  have hclInter :
      cl[𝕜]((M : Set E) ∩ C) = closure ((M : Set E) ∩ C) :=
    Set.intrinsicClosure_eq_closure_of_isClosed_affineSpan
      (hclosed := hclosedInter)
  have hclC : cl[𝕜](C) = closure C :=
    Set.intrinsicClosure_eq_closure_of_isClosed_affineSpan
      (hclosed := hclosedC)
  calc
    closure ((M : Set E) ∩ C) = cl[𝕜]((M : Set E) ∩ C) := by
      exact hclInter.symm
    _ = (M : Set E) ∩ cl[𝕜](C) := M.intrinsicClosure_inter_eq hC hri
    _ = (M : Set E) ∩ closure C := by simp [hclC]

end AffineSubspace

end ClosureIsClosedAffineSpan

section Closure

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T1Space E]

namespace AffineSubspace

/-- Corollary 6.5.1 (2), ambient-closure form on the finite-direction affine-hull layer:
if an affine set `M` meets `ri[𝕜](C)` for a convex set `C`, and `aff[𝕜] C` has
finite-dimensional direction, then `closure (M ∩ C) = M ∩ closure C`. -/
theorem closure_inter_eq (M : AffineSubspace 𝕜 E) {C : Set E} (hC : Convex 𝕜 C)
    (hri : ((M : Set E) ∩ ri[𝕜](C)).Nonempty)
    [FiniteDimensional 𝕜 (aff[𝕜] C).direction] :
    closure ((M : Set E) ∩ C) = (M : Set E) ∩ closure C := by
  have hfd_inter : FiniteDimensional 𝕜 (aff[𝕜] ((M : Set E) ∩ C)).direction :=
    Submodule.finiteDimensional_of_le <|
      AffineSubspace.direction_le <|
        affineSpan_mono 𝕜 (Set.inter_subset_right : ((M : Set E) ∩ C) ⊆ C)
  exact M.closure_inter_eq_of_isClosed_affineSpan hC hri
    (Set.isClosed_affineSpan (C := C))
    (Set.isClosed_affineSpan
      (C := ((M : Set E) ∩ C)))

end AffineSubspace

end Closure
