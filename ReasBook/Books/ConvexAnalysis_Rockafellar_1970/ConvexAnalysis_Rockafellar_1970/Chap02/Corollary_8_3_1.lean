import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_13

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

universe u v

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 8.3.1 identifies `0⁺[𝕜] (ri[𝕜](C))` with `0⁺[𝕜] (closure C)` and
  gives the base-point positive-ray criterion from `x ∈ ri[𝕜](C)`.
- `core/canonical`: the chapter owner is `recessionCone`; primitive bridge mechanics remain
  abstract, while source-facing corollary surfaces derive bridge facts from canonical chapter
  theorems instead of exposing capability-style hypotheses.
- `bridge/view`: in finite-dimensional normed spaces, Theorem 6.3 supplies
  `ri[𝕜](closure C) = ri[𝕜](C)`, `cl[𝕜](C) = closure C`, and relative-interior
  nonemptiness for convex nonempty sets; Theorem 8.3 (2) supplies
  `0⁺[𝕜] (closure C) ⊆ 0⁺[𝕜] (ri[𝕜](closure C))`.
- Primitive data vs derived API: the primitive layer here is an ambient closed-convex bridge
  theorem for an arbitrary subset `S ⊆ A`, with explicit bridge data
  `A.Nonempty → S.Nonempty`, `S ⊆ A`, and `0⁺[𝕜] A ⊆ 0⁺[𝕜] S`.
- Layer target: keep owner-level core results at the weakest reusable topological ordered-semifield
  layer; finite-dimensional source-facing consequences are obtained by canonical upstream bridges.
-/

namespace Convex

/-- Primitive ambient bridge form: if `A` is closed convex, `S` is nonempty whenever `A` is
nonempty, `S ⊆ A`, and every recession direction of `A` is one of `S`, then the recession cones
of `S` and `A` coincide. -/
theorem recessionCone_eq_of_nonempty_subset {A S : Set E}
    (hA : Convex 𝕜 A) (hAclosed : IsClosed A)
    (hS_nonempty : A.Nonempty → S.Nonempty) (hS_subset : S ⊆ A)
    (hA_subset : 0⁺[𝕜] A ⊆ 0⁺[𝕜] S) :
    0⁺[𝕜] S = 0⁺[𝕜] A := by
  refine subset_antisymm ?_ hA_subset
  intro y hy
  by_cases hSne : S.Nonempty
  · rcases hSne with ⟨x, hx⟩
    exact Convex.mem_recessionCone_of_nonneg_ray (C := A) (x := x) (y := y)
      (hC := hA) hAclosed fun (a : 𝕜) ha ↦
        hS_subset <| (Set.mem_recessionCone_iff.mp hy) x hx a ha
  · have hAne : ¬ A.Nonempty := by
      intro hAne
      exact hSne (hS_nonempty hAne)
    have hA_empty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hAne
    simp [hA_empty]

/-- Primitive ambient base-point criterion: once `0⁺[𝕜] S = 0⁺[𝕜] A` for a bridge subset
`S ⊆ A`, membership in `0⁺[𝕜] A` is equivalent to the positive-ray condition from any base
point `x ∈ S`. -/
theorem mem_recessionCone_iff_forall_pos_smul_add_mem_of_recessionCone_eq
    {A S : Set E} (hEq : 0⁺[𝕜] S = 0⁺[𝕜] A)
    (hA : Convex 𝕜 A) (hAclosed : IsClosed A) (hS_subset : S ⊆ A) {x y : E}
    (hx : x ∈ S) :
    y ∈ 0⁺[𝕜] A ↔ ∀ a > (0 : 𝕜), x + a • y ∈ S := by
  constructor
  · intro hy a ha
    have hy' : y ∈ 0⁺[𝕜] S := by
      simpa [hEq] using hy
    exact (Set.mem_recessionCone_iff.mp hy') x hx a ha.le
  · intro hy
    exact Convex.mem_recessionCone_of_nonneg_ray (C := A) (x := x) (y := y)
      (hC := hA) hAclosed fun (a : 𝕜) ha ↦ by
        rcases eq_or_lt_of_le ha with rfl | ha_pos
        · simpa using hS_subset hx
        · exact hS_subset (hy a ha_pos)

end Convex

end

section

open scoped Rockafellar

universe u v

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

namespace Convex

/-- Corollary 8.3.1 at the primitive intrinsic bridge layer: if `cl[𝕜](C)` is closed,
if `ri[𝕜](C)` is nonempty whenever `C` is nonempty, and if every recession direction of
`cl[𝕜](C)` is one of `ri[𝕜](C)`, then these sets have the same recession cone. -/
theorem recessionCone_ri_eq_recessionCone_intrinsicClosure_of_bridge {C : Set E} (hC : Convex 𝕜 C)
    (hIC_closed : IsClosed (cl[𝕜](C)))
    (hri_nonempty : C.Nonempty → (ri[𝕜](C)).Nonempty)
    (hintrinsic_subset : 0⁺[𝕜] (cl[𝕜](C)) ⊆ 0⁺[𝕜] (ri[𝕜](C))) :
    0⁺[𝕜] (ri[𝕜](C)) = 0⁺[𝕜] (cl[𝕜](C)) := by
  refine recessionCone_eq_of_nonempty_subset (A := cl[𝕜](C)) (S := ri[𝕜](C))
    hC.intrinsicClosure hIC_closed ?_
    (fun _ hx ↦ subset_intrinsicClosure (intrinsicInterior_subset hx))
    hintrinsic_subset
  intro hIC_nonempty
  have hCne : C.Nonempty := by
    by_contra hCne
    have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
    simpa [hC_empty] using hIC_nonempty
  exact hri_nonempty hCne

/-- Primitive ambient-closure bridge for Corollary 8.3.1: if `ri[𝕜](C)` is nonempty whenever `C`
is nonempty and if every recession direction of `closure C` is a recession direction of
`ri[𝕜](C)`, then `ri[𝕜](C)` and `closure C` have the same recession cone. -/
theorem recessionCone_ri_eq_recessionCone_closure_of_bridge {C : Set E} (hC : Convex 𝕜 C)
    (hri_nonempty : C.Nonempty → (ri[𝕜](C)).Nonempty)
    (hclosure_subset : 0⁺[𝕜] (closure C) ⊆ 0⁺[𝕜] (ri[𝕜](C))) :
    0⁺[𝕜] (ri[𝕜](C)) = 0⁺[𝕜] (closure C) := by
  refine recessionCone_eq_of_nonempty_subset (A := closure C) (S := ri[𝕜](C))
    hC.closure isClosed_closure ?_
    (fun _ hx ↦ subset_closure (intrinsicInterior_subset hx))
    hclosure_subset
  intro hclosure_nonempty
  have hCne : C.Nonempty := by
    by_contra hCne
    have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
    simpa [hC_empty] using hclosure_nonempty
  exact hri_nonempty hCne

/-- Primitive intrinsic bridge base-point criterion for Corollary 8.3.1: under the bridge
hypotheses making `0⁺[𝕜] (ri[𝕜](C)) = 0⁺[𝕜] (cl[𝕜](C))`, membership in
`0⁺[𝕜] (cl[𝕜](C))` is equivalent to the positive-ray condition from any base point
`x ∈ ri[𝕜](C)`. -/
theorem mem_recessionCone_intrinsicClosure_iff_forall_pos_smul_add_mem_of_bridge {C : Set E}
    (hC : Convex 𝕜 C) (hIC_closed : IsClosed (cl[𝕜](C)))
    (hri_nonempty : C.Nonempty → (ri[𝕜](C)).Nonempty)
    (hintrinsic_subset : 0⁺[𝕜] (cl[𝕜](C)) ⊆ 0⁺[𝕜] (ri[𝕜](C)))
    {x y : E} (hx : x ∈ ri[𝕜](C)) :
    y ∈ 0⁺[𝕜] (cl[𝕜](C)) ↔ ∀ a > (0 : 𝕜), x + a • y ∈ ri[𝕜](C) := by
  exact mem_recessionCone_iff_forall_pos_smul_add_mem_of_recessionCone_eq
    (recessionCone_ri_eq_recessionCone_intrinsicClosure_of_bridge hC hIC_closed hri_nonempty
      hintrinsic_subset)
    hC.intrinsicClosure hIC_closed
    (fun _ hz ↦ subset_intrinsicClosure (intrinsicInterior_subset hz))
    hx

/-- Primitive ambient-closure bridge base-point criterion for Corollary 8.3.1: under the bridge
hypotheses making `0⁺[𝕜] (ri[𝕜](C)) = 0⁺[𝕜] (closure C)`, membership in `0⁺[𝕜] (closure C)` is
equivalent to the positive-ray condition from any base point `x ∈ ri[𝕜](C)`. -/
theorem mem_recessionCone_closure_iff_forall_pos_smul_add_mem_of_bridge {C : Set E}
    (hC : Convex 𝕜 C) (hri_nonempty : C.Nonempty → (ri[𝕜](C)).Nonempty)
    (hclosure_subset : 0⁺[𝕜] (closure C) ⊆ 0⁺[𝕜] (ri[𝕜](C)))
    {x y : E} (hx : x ∈ ri[𝕜](C)) :
    y ∈ 0⁺[𝕜] (closure C) ↔ ∀ a > (0 : 𝕜), x + a • y ∈ ri[𝕜](C) := by
  exact mem_recessionCone_iff_forall_pos_smul_add_mem_of_recessionCone_eq
    (recessionCone_ri_eq_recessionCone_closure_of_bridge hC hri_nonempty hclosure_subset)
    hC.closure isClosed_closure
    (fun _ hz ↦ subset_closure (intrinsicInterior_subset hz))
    hx

end Convex

end

section

open scoped Rockafellar

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Convex

private theorem recessionCone_intrinsicClosure_subset_recessionCone_ri {C : Set E}
    (hC : Convex 𝕜 C) :
    0⁺[𝕜] (cl[𝕜](C)) ⊆ 0⁺[𝕜] (ri[𝕜](C)) := by
  have hsubset :
      0⁺[𝕜] (cl[𝕜](C)) ⊆ 0⁺[𝕜] (ri[𝕜](cl[𝕜](C))) :=
    hC.intrinsicClosure.recessionCone_subset_ri
  rw [← hC.ri_intrinsicClosure_eq_ri]
  exact hsubset

private theorem recessionCone_closure_subset_recessionCone_ri {C : Set E}
    (hC : Convex 𝕜 C) :
    0⁺[𝕜] (closure C) ⊆ 0⁺[𝕜] (ri[𝕜](C)) := by
  simpa [intrinsicClosure_eq_closure 𝕜 C] using
    (recessionCone_intrinsicClosure_subset_recessionCone_ri (hC := hC))

private theorem ri_nonempty_of_nonempty {C : Set E} (hC : Convex 𝕜 C) :
    C.Nonempty → (ri[𝕜](C)).Nonempty := fun hCne ↦
  hC.intrinsicInterior_nonempty hCne

/-- Corollary 8.3.1, intrinsic-closure owner form: in finite-dimensional normed spaces over an
ordered complete nontrivially normed field, `ri[𝕜](C)` and `cl[𝕜](C)` have the same
recession cone. -/
theorem recessionCone_ri_eq_recessionCone_intrinsicClosure {C : Set E}
    (hC : Convex 𝕜 C) :
    0⁺[𝕜] (ri[𝕜](C)) = 0⁺[𝕜] (cl[𝕜](C)) := by
  have hIC_closed : IsClosed (cl[𝕜](C)) := by
    simpa [intrinsicClosure_eq_closure 𝕜 C] using (isClosed_closure : IsClosed (closure C))
  exact recessionCone_ri_eq_recessionCone_intrinsicClosure_of_bridge hC hIC_closed
    (ri_nonempty_of_nonempty hC)
    (recessionCone_intrinsicClosure_subset_recessionCone_ri hC)

/-- Corollary 8.3.1, ambient-closure bridge form. -/
theorem recessionCone_ri_eq_recessionCone_closure {C : Set E}
    (hC : Convex 𝕜 C) :
    0⁺[𝕜] (ri[𝕜](C)) = 0⁺[𝕜] (closure C) := by
  simpa [intrinsicClosure_eq_closure 𝕜 C] using
    (hC.recessionCone_ri_eq_recessionCone_intrinsicClosure)

/-- If `x ∈ ri[𝕜](C)`, then a vector `y` belongs to the recession cone of `cl[𝕜](C)`
exactly when every positive translate `x + a • y` remains in `ri[𝕜](C)`. -/
theorem mem_recessionCone_intrinsicClosure_iff_forall_pos_smul_add_mem {C : Set E}
    (hC : Convex 𝕜 C)
    {x y : E} (hx : x ∈ ri[𝕜](C)) :
    y ∈ 0⁺[𝕜] (cl[𝕜](C)) ↔ ∀ a > (0 : 𝕜), x + a • y ∈ ri[𝕜](C) := by
  have hIC_closed : IsClosed (cl[𝕜](C)) := by
    simpa [intrinsicClosure_eq_closure 𝕜 C] using (isClosed_closure : IsClosed (closure C))
  exact mem_recessionCone_intrinsicClosure_iff_forall_pos_smul_add_mem_of_bridge hC hIC_closed
    (ri_nonempty_of_nonempty hC)
    (recessionCone_intrinsicClosure_subset_recessionCone_ri hC)
    hx

/-- Ambient-closure bridge for Corollary 8.3.1: a vector belongs to the recession cone of
`closure C` exactly when every positive translate from a base point in `ri[𝕜](C)` stays in
`ri[𝕜](C)`. -/
theorem mem_recessionCone_closure_iff_forall_pos_smul_add_mem {C : Set E}
    (hC : Convex 𝕜 C)
    {x y : E} (hx : x ∈ ri[𝕜](C)) :
    y ∈ 0⁺[𝕜] (closure C) ↔ ∀ a > (0 : 𝕜), x + a • y ∈ ri[𝕜](C) := by
  simpa [intrinsicClosure_eq_closure 𝕜 C] using
    (hC.mem_recessionCone_intrinsicClosure_iff_forall_pos_smul_add_mem (x := x) (y := y) hx)

end Convex

end
