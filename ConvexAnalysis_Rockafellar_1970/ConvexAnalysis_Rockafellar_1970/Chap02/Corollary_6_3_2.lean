import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar
local notation "cl[" 𝕜 "](" C ")" => intrinsicClosure 𝕜 C

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 6.3.2 says that for a convex set `C` in a finite-dimensional ordered
  normed-field ambient space, every ambient open set meeting `intrinsicClosure 𝕜 C` also meets
  the relative interior of `C`; the ambient-`closure` phrasing is a bridge corollary. Specializing
  to `𝕜 = ℝ` recovers the textbook statement.
- `core/canonical`: the owner notions are `Convex 𝕜`, `intrinsicClosure 𝕜`, `IsOpen`, and
  `intrinsicInterior 𝕜`; both primitive and source-facing surfaces are intrinsic-first, with
  ambient-`closure` phrasing retained as a bridge theorem.
- `bridge/view`: the primitive intrinsic theorem below is the owner-level core; the
  ambient-`closure` and convex finite-dimensional statements are thin wrappers from `Theorem_6_3`.
- Domain-style sampling: the relevant canonical declarations in this domain are
  `intrinsicInterior`, `Convex.intrinsicClosure_ri_eq_intrinsicClosure` and
  `Convex.closure_intrinsicInterior_eq_closure` from `Theorem_6_3`,
  `closure_inter_open_nonempty_iff`, and mathlib's `intrinsicInterior_nonempty`.
- Primitive data vs derived API: no new data is introduced here; the nonemptiness conclusion is a
  derived topological consequence of the owner closure theorem.
- Layer target: this item is a `bridge/view` consequence. The primitive bridge surface belongs to
  `Set`, while the finite-dimensional convex corollary stays on the `Convex` owner namespace.
-/

namespace Set

section Primitive

variable {𝕜 V P : Type*} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [TopologicalSpace P] [AddTorsor V P]

/-- Primitive ambient-closure bridge: if `closure (ri[𝕜](C)) = closure C` and an ambient open set
`U` meets `closure C`, then `U` also meets `ri[𝕜](C)`. -/
theorem inter_ri_nonempty_of_isOpen_of_inter_closure_nonempty
    {C U : Set P} (hri : closure (ri[𝕜](C)) = closure C) (hU : IsOpen U)
    (hCU : (closure C ∩ U).Nonempty) :
    (ri[𝕜](C) ∩ U).Nonempty := by
  exact (closure_inter_open_nonempty_iff hU).1 <| by
    simpa [hri] using hCU

/-- Primitive intrinsic-closure owner bridge: if `cl[𝕜](ri[𝕜](C)) = cl[𝕜](C)` and an ambient open
set `U` meets `cl[𝕜](C)`, then `U` also meets `ri[𝕜](C)`. -/
theorem inter_ri_nonempty_of_isOpen_of_inter_intrinsicClosure_nonempty
    {C U : Set P} (hri : cl[𝕜](ri[𝕜](C)) = cl[𝕜](C)) (hU : IsOpen U)
    (hCU : (cl[𝕜](C) ∩ U).Nonempty) :
    (ri[𝕜](C) ∩ U).Nonempty := by
  exact (closure_inter_open_nonempty_iff hU).1 <| by
    rcases hCU with ⟨x, hxC, hxU⟩
    have hxri : x ∈ cl[𝕜](ri[𝕜](C)) := by
      simpa [hri] using hxC
    exact ⟨x, intrinsicClosure_subset_closure hxri, hxU⟩

end Primitive

end Set

namespace Convex

section SourceFacing

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- Corollary 6.3.2, intrinsic-closure owner form in finite-dimensional spaces: if `C` is convex
and an ambient open set `U` meets `cl[𝕜](C)`, then `U` also meets `ri[𝕜](C)`. -/
theorem inter_ri_nonempty_of_isOpen_of_inter_intrinsicClosure_nonempty
    {C U : Set E} (hC : Convex 𝕜 C) (hU : IsOpen U)
    (hCU : (cl[𝕜](C) ∩ U).Nonempty) :
    (ri[𝕜](C) ∩ U).Nonempty := by
  exact Set.inter_ri_nonempty_of_isOpen_of_inter_intrinsicClosure_nonempty
    hC.intrinsicClosure_ri_eq_intrinsicClosure hU hCU

/-- Corollary 6.3.2, ambient-closure bridge in finite-dimensional spaces: if `C` is convex and an
ambient open set `U` meets `closure C`, then `U` also meets `ri[𝕜](C)`. -/
theorem inter_ri_nonempty_of_isOpen_of_inter_closure_nonempty
    {C U : Set E} (hC : Convex 𝕜 C) (hU : IsOpen U) (hCU : (closure C ∩ U).Nonempty) :
    (ri[𝕜](C) ∩ U).Nonempty := by
  exact Set.inter_ri_nonempty_of_isOpen_of_inter_closure_nonempty
    hC.closure_intrinsicInterior_eq_closure hU hCU

end SourceFacing

end Convex

end
