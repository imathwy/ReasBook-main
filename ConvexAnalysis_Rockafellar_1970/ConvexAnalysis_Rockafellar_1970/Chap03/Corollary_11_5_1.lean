import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_0_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_11_5

-- Declarations for this item will be appended below by the statement pipeline.

section

open Set
open scoped Rockafellar

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [Nontrivial (StrongDual ℝ E)]
local notation "E⋆" => StrongDual ℝ E

local instance instHasLinearPairingStrongDualTopologicalCor1151 :
    HasLinearPairing E E⋆ ℝ where
  pairingLinear :=
    { toFun := fun x =>
        { toFun := fun l => l x
          map_add' := by
            intro l₁ l₂
            simp
          map_smul' := by
            intro a l
            simp }
      map_add' := by
        intro x z
        ext l
        simp
      map_smul' := by
        intro a x
        ext l
        simp }

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 11.5.1 states that for any subset `S ⊆ R^n`, the closure of its
  convex hull is, in positive dimension, the intersection of all closed half-spaces containing
  `S`.
- `core/canonical`: the owner abstractions are `closedConvexHull ℝ`, the chapter predicate
  `closedHalfSpace[_,_]`, and the set-theoretic intersection operator `⋂₀`.
- `bridge/view`: the textbook phrase “the closed half-spaces containing `S`” is rendered as the
  family `{s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ S ⊆ s}`.
- Primitive data vs derived API: the primitive input is the subset `S`, while the canonical owner
  object `closedConvexHull ℝ S` is generated data. The half-space containment equivalence and the
  displayed intersection formula are theorem-level bridge API.
- Domain-style sampling used here: `closedConvexHull ℝ`,
  `closedConvexHull_eq_closure_convexHull`, the owner methods
  `Set.IsClosedHalfSpace.convex`, the orientation closedness bridges
  `closedHalfSpaceLE_closed_of_continuous`/`closedHalfSpaceGE_closed_of_continuous`, and the
  preceding chapter theorem
  `closed_convex_eq_sInter_closedHalfSpacesContaining`.
- Layer target: `bridge/view`; this is the specialization of Theorem 11.5 to the canonical owner
  `closedConvexHull ℝ S`, together with the observation that a closed half-space contains that
  owner object exactly when it contains `S`.
- Ambient refinement: the source `R^n` statement in positive dimension is a Euclidean
  specialization of the canonical real locally convex topological vector-space statement with
  nontrivial continuous dual, phrased with dual-owner closed half-spaces.
-/

theorem closedConvexHull_eq_sInter_closedHalfSpacesContaining {S : Set E} :
    closedConvexHull ℝ S = ⋂₀ {s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ S ⊆ s} := by
  have hfamily :
      {s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ closedConvexHull ℝ S ⊆ s} =
        {s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ S ⊆ s} := by
    ext s
    constructor
    · rintro ⟨hs, hsubset⟩
      exact ⟨hs, subset_trans subset_closedConvexHull hsubset⟩
    · rintro ⟨hs, hsubset⟩
      have hs_closed : IsClosed s := by
        rcases hs with ⟨l, β, -, rfl | rfl⟩
        · exact closedHalfSpaceLE_closed_of_continuous l β l.continuous
        · exact closedHalfSpaceGE_closed_of_continuous l β l.continuous
      exact ⟨hs, closedConvexHull_min hsubset hs.convex hs_closed⟩
  simpa [hfamily] using
    closed_convex_eq_sInter_closedHalfSpacesContaining (closedConvexHull ℝ S)
      isClosed_closedConvexHull convex_closedConvexHull

theorem closure_convexHull_eq_sInter_closedHalfSpacesContaining {S : Set E} :
    closure (convexHull ℝ S) =
      ⋂₀ {s : Set E | (closedHalfSpace[E⋆,ℝ] s) ∧ S ⊆ s} := by
  simpa [closedConvexHull_eq_closure_convexHull] using
    (closedConvexHull_eq_sInter_closedHalfSpacesContaining (S := S))

end
