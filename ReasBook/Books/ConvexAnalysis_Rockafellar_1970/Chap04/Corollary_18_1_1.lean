import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_18_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 18.1.1 says that a face `C'` of a convex set `C`, represented by
  `C'.IsFace 𝕜 C`, is exactly the
  intersection of `C` with the intrinsic closure of `C'`; the ambient `closure` formulation is a
  finite-dimensional bridge corollary, and therefore a face is closed whenever `C` is closed.
- `core/canonical`: the source-facing owner is `Set.IsFace`, together with the upstream owner
  theorem `Set.IsFace.subset_of_nonempty_inter_ri`, plus `intrinsicClosure` and
  `IsClosed`.
- `bridge/view`: the ambient closure identity is a theorem-level bridge obtained from
  `intrinsicClosure_eq_closure`.

Domain-style sampling used here:
- `Set.IsFace.subset_of_nonempty_inter_ri`;
- `Set.IsFace.subset`;
- `Convex 𝕜 C`;
- `intrinsicClosure` and `subset_intrinsicClosure`;
- `intrinsicClosure_eq_closure`;
- `IsClosed.inter` and `isClosed_closure`.

Primitive data vs derived API:
- primitive owner input: the face hypothesis `C'.IsFace 𝕜 C` together with the meet witness
  `(C' ∩ ri[𝕜](C ∩ intrinsicClosure 𝕜 C')).Nonempty`;
  plus convexity of `C` yields the same intrinsic identity directly;
- derived finite-dimensional bridge API: finite-dimensional hypotheses plus an explicit witness
  `C'.Nonempty` produce the owner-level relative-interior witness via
  `Convex.intrinsicInterior_nonempty`.
- ambient closure bridge and closedness are then derived.

Layer target: the intrinsic closure identity is `source-facing`; the ambient closure statement and
closedness theorem are `bridge/view` corollaries.

Ambient refinement: the primitive owner theorem only uses `Theorem_18_1`, hence it stays on the
same scalar-general owner layer as `Set.IsFace.subset_of_nonempty_inter_ri`. Finite-dimensional
normed assumptions are needed only for the bridge from `C'.Nonempty` (via
`Convex.intrinsicInterior_nonempty`, then `Convex.ri_intrinsicClosure_eq_ri`) and for the ambient
closure bridge
`intrinsicClosure_eq_closure`. Specializing `𝕜 = ℝ` recovers the textbook formulation.
-/

namespace Set.IsFace

section PrimitiveOwner

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Primitive owner form behind Corollary 18.1.1: if a face `C'` of `C` meets
`ri[𝕜](C ∩ intrinsicClosure 𝕜 C')`, then `C' = C ∩ intrinsicClosure 𝕜 C'`. -/
theorem eq_inter_intrinsicClosure_of_nonempty_inter_ri_inter
    {C C' : Set E} (hC' : C'.IsFace 𝕜 C)
    (hmeet : (C' ∩ ri[𝕜](C ∩ intrinsicClosure 𝕜 C')).Nonempty) :
    C' = C ∩ intrinsicClosure 𝕜 C' := by
  refine Subset.antisymm ?_ ?_
  · intro x hx
    exact ⟨hC'.subset hx, subset_intrinsicClosure hx⟩
  · exact hC'.subset_of_nonempty_inter_ri inter_subset_left hmeet

end PrimitiveOwner

section RelativeInteriorBridge

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 E]

/-- Owner-level bridge to `eq_inter_intrinsicClosure_of_nonempty_inter_ri_inter`: a
nonempty relative interior witness for `C'` provides the needed meet condition. -/
theorem eq_inter_intrinsicClosure_of_nonempty_ri {C C' : Set E} (hC' : C'.IsFace 𝕜 C)
    (hC : Convex 𝕜 C) (hriC' : (ri[𝕜](C')).Nonempty) :
    C' = C ∩ intrinsicClosure 𝕜 C' := by
  let D := C ∩ intrinsicClosure 𝕜 C'
  have hC'D : C' ⊆ D := by
    intro x hx
    exact ⟨hC'.subset hx, subset_intrinsicClosure hx⟩
  have hD_conv : Convex 𝕜 D := hC.inter (Convex.intrinsicClosure (𝕜 := 𝕜) hC'.convex)
  have hclosure : intrinsicClosure 𝕜 D = intrinsicClosure 𝕜 C' := by
    refine Subset.antisymm ?_ (intrinsicClosure_mono (𝕜 := 𝕜) hC'D)
    simpa [D] using
      intrinsicClosure_mono (𝕜 := 𝕜)
        (inter_subset_right : C ∩ intrinsicClosure 𝕜 C' ⊆ intrinsicClosure 𝕜 C')
  have hri : ri[𝕜](C') = ri[𝕜](D) := by
    calc
      ri[𝕜](C') = ri[𝕜](intrinsicClosure 𝕜 C') := by
        simpa using (hC'.convex.ri_intrinsicClosure_eq_ri_of_nonempty hriC').symm
      _ = ri[𝕜](intrinsicClosure 𝕜 D) := by rw [← hclosure]
      _ = ri[𝕜](D) := by
        simpa using hD_conv.ri_intrinsicClosure_eq_ri
  rcases hriC' with ⟨x, hxri⟩
  have hmeet : (C' ∩ ri[𝕜](D)).Nonempty := by
    refine ⟨x, intrinsicInterior_subset hxri, ?_⟩
    rwa [hri] at hxri
  simpa [D] using hC'.eq_inter_intrinsicClosure_of_nonempty_inter_ri_inter hmeet

end RelativeInteriorBridge

section FiniteDimensionalBridge

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 E]

/-- Finite-dimensional bridge to `eq_inter_intrinsicClosure_of_nonempty_ri`: an explicit witness
`C'.Nonempty` provides the needed relative-interior witness. -/
theorem eq_inter_intrinsicClosure_of_nonempty {C C' : Set E} (hC' : C'.IsFace 𝕜 C)
    (hC : Convex 𝕜 C) (hC'ne : C'.Nonempty) :
    C' = C ∩ intrinsicClosure 𝕜 C' := by
  exact hC'.eq_inter_intrinsicClosure_of_nonempty_ri hC
    (hC'.convex.intrinsicInterior_nonempty hC'ne)

/-- Primitive ambient-closure bridge for Corollary 18.1.1, from
`eq_inter_intrinsicClosure_of_nonempty`. -/
theorem eq_inter_closure_of_nonempty {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hC : Convex 𝕜 C)
    (hC'ne : C'.Nonempty) :
    C' = C ∩ closure C' := by
  simpa [intrinsicClosure_eq_closure 𝕜 C'] using
    hC'.eq_inter_intrinsicClosure_of_nonempty hC hC'ne

end FiniteDimensionalBridge

section SourceFacing

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 E]

/-- Corollary 18.1.1, intrinsic owner form: a face `C'` of a convex set `C`, represented by
`C'.IsFace 𝕜 C`, is exactly `C ∩ intrinsicClosure 𝕜 C'`. -/
theorem eq_inter_intrinsicClosure {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hC : Convex 𝕜 C) :
    C' = C ∩ intrinsicClosure 𝕜 C' := by
  obtain rfl | hC'ne := Set.eq_empty_or_nonempty C'
  · simp
  exact hC'.eq_inter_intrinsicClosure_of_nonempty hC hC'ne

/-- Corollary 18.1.1, ambient-closure bridge: in the same finite-dimensional setting,
`eq_inter_intrinsicClosure` rewrites to `C' = C ∩ closure C'`. -/
theorem eq_inter_closure {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hC : Convex 𝕜 C) :
    C' = C ∩ closure C' := by
  simpa [intrinsicClosure_eq_closure 𝕜 C'] using hC'.eq_inter_intrinsicClosure hC

/-- A face of a closed convex set is closed. -/
-- Proof sketch: rewrite `C'` using `hC'.eq_inter_closure hC`; then `C ∩ closure C'` is
-- closed because it is the intersection of the closed set `C` with the closed set `closure C'`.
theorem isClosed {C C' : Set E} (hC' : C'.IsFace 𝕜 C)
    (hC : Convex 𝕜 C) (hC_closed : IsClosed C) : IsClosed C' := by
  rw [hC'.eq_inter_closure hC]
  exact hC_closed.inter isClosed_closure

end SourceFacing

end Set.IsFace

end
