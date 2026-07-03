

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_8_3_1 (from Chap02) -/
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

/-! ### Corollary_8_3_2 (from Chap02) -/
section

universe u v

open scoped Pointwise Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Corollary 8.3.2 identifies Rockafellar's recession cone `0⁺ C` for a closed
  convex set `C` containing the origin with the intersection of all positive dilates of `C`, and
  then rewrites membership as the inverse-rescaling criterion from the text.
- `core/canonical`: the owner abstraction for this source notion is the chapter recession-cone
  owner `recessionCone 𝕜 C`, written on the public surface as `0⁺[𝕜] C`, together with the
  canonical pointwise scalar action `ε • C` on sets.
- `bridge/view`: `Set.mem_recessionCone_iff` expands the owner into the textbook ray condition,
  `Convex.mem_recessionCone_of_nonneg_ray` is the owner-side closed-convex ray constructor from
  Theorem 8.3, and `Set.mem_smul_set_iff_inv_smul_mem₀` rewrites positive-dilate membership into
  the inverse-rescaling form.
- Domain-style sampling: `recessionCone`, `Set.mem_recessionCone_iff`,
  `Convex.mem_recessionCone_of_nonneg_ray`, and `Set.mem_smul_set_iff_inv_smul_mem₀`.
- Primitive data vs derived API: the primitive owner-side inclusion
  `0⁺[𝕜] C ⊆ ⋂ ε > 0, ε • C` uses only origin-membership `0 ∈ C`; the reverse inclusion is the
  closed-convex upgrade that uses Theorem 8.3's ray constructor. The source-facing equality and
  inverse-rescaling membership criterion are derived by composing those two layers, rather than
  keeping the strong assumptions in both directions.
- Layer target: this item keeps the primitive inclusion at the `Set` owner layer and exposes the
  source-facing closed-convex equalities on the existing `Convex` owner namespace.
-/

namespace Set

variable {𝕜 : Type v} [GroupWithZero 𝕜] [Preorder 𝕜]
variable {E : Type u} [MulAction 𝕜 E]

/-- Membership in the intersection of all positive dilates of `C` is exactly the inverse-rescaling
criterion `ε⁻¹ • y ∈ C` for every positive scalar `ε`. -/
theorem mem_iInter_pos_smul_iff_forall_pos_inv_smul_mem {C : Set E} {y : E} :
    y ∈ ⋂ ε > (0 : 𝕜), ε • C ↔ ∀ ε : 𝕜, 0 < ε → ε⁻¹ • y ∈ C := by
  constructor
  · intro hy ε hε
    exact (Set.mem_smul_set_iff_inv_smul_mem₀ hε.ne' C y).mp
      (Set.mem_iInter.mp (Set.mem_iInter.mp hy ε) hε)
  · intro hy
    exact Set.mem_iInter.mpr fun ε ↦
      Set.mem_iInter.mpr fun hε ↦
        (Set.mem_smul_set_iff_inv_smul_mem₀ hε.ne' C y).mpr (hy ε hε)

/-- Owner-level set form: the intersection of all positive dilates of `C` is exactly the set of
points whose inverse positive rescalings all lie in `C`. -/
theorem iInter_pos_smul_eq_setOf_forall_pos_inv_smul_mem {C : Set E} :
    (⋂ ε > (0 : 𝕜), ε • C) = {y : E | ∀ ε : 𝕜, 0 < ε → ε⁻¹ • y ∈ C} := by
  ext y
  exact mem_iInter_pos_smul_iff_forall_pos_inv_smul_mem

end Set

end

section

universe u v

open scoped Pointwise Rockafellar

namespace Set

variable {𝕜 : Type v} [GroupWithZero 𝕜] [PartialOrder 𝕜] [PosMulReflectLT 𝕜]
variable {E : Type u} [AddZeroClass E] [MulAction 𝕜 E]

/-- Primitive owner-side inclusion for Corollary 8.3.2: if `0 ∈ C`, every recession direction of
`C` belongs to every positive dilate `ε • C`. -/
theorem recessionCone_subset_iInter_pos_smul {C : Set E} (h0C : (0 : E) ∈ C) :
    0⁺[𝕜] C ⊆ ⋂ ε > (0 : 𝕜), ε • C := by
  intro y hy
  exact Set.mem_iInter.mpr fun ε ↦
    Set.mem_iInter.mpr fun hε ↦
      (Set.mem_smul_set_iff_inv_smul_mem₀ hε.ne' C y).mpr <|
        by
          simpa [zero_add] using
            (Set.mem_recessionCone_iff.mp hy) 0 h0C ε⁻¹ (le_of_lt <| inv_pos.mpr hε)

end Set

end

section

universe u v

open scoped Pointwise Rockafellar

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

namespace Convex

variable {C : Set E}
variable (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (h0C : 0 ∈ C)

include hC_convex hC_closed

/-- Corollary 8.3.2, reverse inclusion: for a closed convex set, membership in every positive
dilate of `C` implies membership in `0⁺[𝕜] C`. -/
theorem iInter_pos_smul_subset_recessionCone :
    (⋂ ε > (0 : 𝕜), ε • C) ⊆ 0⁺[𝕜] C := by
  intro y hy
  have hy' : ∀ ε : 𝕜, 0 < ε → ε⁻¹ • y ∈ C :=
    Set.mem_iInter_pos_smul_iff_forall_pos_inv_smul_mem.mp hy
  have hy_mem : y ∈ C := by
    simpa using hy' 1 zero_lt_one
  have hRay : ∀ a : 𝕜, 0 ≤ a → y + a • y ∈ C := by
    intro a ha
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simpa [zero_smul] using hy_mem
    · have ha1_pos : 0 < a + 1 := add_pos_of_nonneg_of_pos ha zero_lt_one
      have h_inv : ((a + 1)⁻¹)⁻¹ • y ∈ C := hy' ((a + 1)⁻¹) (inv_pos.mpr ha1_pos)
      simpa [one_smul, add_smul, add_assoc, add_left_comm, add_comm, inv_inv] using h_inv
  exact hC_convex.mem_recessionCone_of_nonneg_ray (x := y) hC_closed hRay

/-- Corollary 8.3.2: if `C` is closed, convex, and contains the origin, then its recession
cone `0⁺[𝕜] C` is the intersection of all positive dilates `ε • C`. -/
theorem recessionCone_eq_iInter_pos_smul (h0C : 0 ∈ C) :
    0⁺[𝕜] C = ⋂ ε > (0 : 𝕜), ε • C := by
  exact Set.Subset.antisymm
    (Set.recessionCone_subset_iInter_pos_smul (C := C) h0C)
    (iInter_pos_smul_subset_recessionCone hC_convex hC_closed)

/-- Corollary 8.3.2, direct owner-level membership bridge: for a closed convex set `C` containing
the origin, membership in the recession cone is equivalent to membership in every positive
dilate. -/
theorem mem_recessionCone_iff_mem_iInter_pos_smul
    (h0C : 0 ∈ C) (y : E) :
    y ∈ 0⁺[𝕜] C ↔ y ∈ ⋂ ε > (0 : 𝕜), ε • C := by
  rw [recessionCone_eq_iInter_pos_smul hC_convex hC_closed h0C]

omit hC_convex hC_closed h0C

/-- Corollary 8.3.2 in owner-level inverse-rescaling form: for a closed convex set `C`
containing the origin, its recession cone is exactly the set of points whose inverse positive
rescalings all lie in `C`. -/
theorem recessionCone_eq_setOf_forall_pos_inv_smul_mem
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (h0C : 0 ∈ C) :
    0⁺[𝕜] C = {y : E | ∀ ε : 𝕜, 0 < ε → ε⁻¹ • y ∈ C} := by
  rw [recessionCone_eq_iInter_pos_smul hC_convex hC_closed h0C,
    Set.iInter_pos_smul_eq_setOf_forall_pos_inv_smul_mem]

/-- For a closed convex set `C` containing the origin, membership in `0⁺[𝕜] C` is
equivalent to the textbook condition that every inverse positive rescaling of the vector belongs
to `C`. -/
theorem mem_recessionCone_iff_forall_pos_inv_smul_mem
    (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C) (h0C : 0 ∈ C) (y : E) :
    y ∈ 0⁺[𝕜] C ↔ ∀ ε : 𝕜, 0 < ε → ε⁻¹ • y ∈ C := by
  rw [mem_recessionCone_iff_mem_iInter_pos_smul
    (hC_convex := hC_convex) (hC_closed := hC_closed) h0C y]
  exact Set.mem_iInter_pos_smul_iff_forall_pos_inv_smul_mem

end Convex

end

/-! ### Corollary_8_3_3 (from Chap02) -/
section

universe u v w

variable {I : Sort w}

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 8.3.3 states that the recession cone of a nonempty intersection of
  closed convex sets in a topological module over an ordered topological semifield is the
  intersection of their recession cones.
- `core/canonical`: the chapter owner object for this source notion is `recessionCone`.
- `bridge/view`: Theorem 8.2 separately identifies `recessionCone` with `asymptoticCone 𝕜` for
  closed convex nonempty sets, so this file should keep only the owner-level intersection formula.
  Binary intersections are a derived specialization via `Set.inter_eq_iInter`, not a second public
  owner theorem.
- Domain-style sampling:
  - primitive owner-side API: `recessionCone`, `Set.mem_recessionCone_iff`
  - upstream bridge API: `Convex.mem_recessionCone_of_nonneg_ray` and
    `Convex.mem_recessionCone_of_exists_pos_ray`.
- Primitive data vs derived API:
  - primitive direction `⋂₀ (recessionCone '' S) ⊆ 0⁺[𝕜] (⋂₀ S)` uses only the owner definition;
  - the reverse inclusion is exactly where the closed-convex bridge theorem is needed.
  - indexed `iInter` statements are derived from the intrinsic `sInter` owner layer via
    `Set.sInter_range`.
- Upstream-first minimality check:
  the stronger ordered-topological-semifield stack appears first in
  Theorem 8.3's bridge API (which is itself aligned with mathlib's
  asymptotic-cone layer), so this file keeps those assumptions only on the
  reverse inclusion and leaves the primitive inclusion at the weak owner layer.
- Layer target: `source-facing`, with the owner-only inclusion in `Set` (owner namespace) and the
  closed-convex bridge statements in `Convex`.
-/

namespace Set

section

variable {𝕜 : Type v} {P E : Type u} [Zero 𝕜] [LE 𝕜] [SMul 𝕜 E] [HAdd P E P]
variable {C : I → Set P}
variable {S : Set (Set P)}

/-- Intrinsic primitive inclusion for recession cones of arbitrary set-families:
membership in every recession cone of members of `S` implies membership in the recession cone of
their intersection `⋂₀ S`. This owner-level statement is ambient-intrinsic:
the family lives in an ambient point type `P`, while recession directions lie in `E`. -/
theorem sInter_recessionCone_subset_recessionCone_sInter :
    (⋂₀ ((fun t : Set P ↦ t.recessionCone 𝕜) '' S)) ⊆ (0⁺[𝕜] (⋂₀ S) : Set E) := by
  intro y hy
  rw [Set.mem_recessionCone_iff]
  intro x hx a ha
  refine Set.mem_sInter.mpr fun t ht ↦ ?_
  have hy_t : y ∈ t.recessionCone 𝕜 :=
    (Set.mem_sInter.mp hy) (t.recessionCone 𝕜) ⟨t, ht, rfl⟩
  exact (Set.mem_recessionCone_iff.mp hy_t) x ((Set.mem_sInter.mp hx) t ht) a ha

/-- The primitive owner-level inclusion for recession cones of indexed intersections:
membership in every `0⁺[𝕜] (C i)` implies membership in `0⁺[𝕜] (⋂ i, C i)`.
As above, this is stated on the intrinsic ambient/direction split `P`/`E`. -/
theorem iInter_recessionCone_subset_recessionCone_iInter :
    (⋂ i, (0⁺[𝕜] (C i) : Set E)) ⊆ (0⁺[𝕜] (⋂ i, C i) : Set E) := by
  simpa [Set.sInter_range] using
    (sInter_recessionCone_subset_recessionCone_sInter (S := Set.range C))

/-- Primitive bridge-layer reverse inclusion for arbitrary set-families:
if `⋂₀ S` is nonempty and each member `t ∈ S` has the owner-side bridge property that one
base-point nonnegative ray in direction `y` implies `y ∈ 0⁺[𝕜] t`, then every recession direction
of the intersection belongs to every member recession cone. -/
theorem recessionCone_sInter_subset_sInter_recessionCone_of_nonneg_ray
    (hS_nonempty : (⋂₀ S).Nonempty)
    (hRayToRecession :
      ∀ t ∈ S, ∀ {x : P} {y : E}, x ∈ t →
        (∀ a : 𝕜, 0 ≤ a → x + a • y ∈ t) → y ∈ (0⁺[𝕜] t : Set E)) :
    (0⁺[𝕜] (⋂₀ S) : Set E) ⊆ ⋂₀ ((fun t : Set P ↦ t.recessionCone 𝕜) '' S) := by
  intro y hy
  rcases hS_nonempty with ⟨x, hx⟩
  refine Set.mem_sInter.mpr fun t ht ↦ ?_
  rcases ht with ⟨t, htS, rfl⟩
  exact hRayToRecession t htS ((Set.mem_sInter.mp hx) t htS) fun a ha ↦
    (Set.mem_sInter.mp <| (Set.mem_recessionCone_iff.mp hy) x hx a ha) t htS

/-- Primitive bridge-layer equality for arbitrary set-families:
if `⋂₀ S` is nonempty and each member `t ∈ S` has the owner-side bridge property that one
base-point nonnegative ray in direction `y` implies `y ∈ 0⁺[𝕜] t`, then the recession cone of the
intersection is the intersection of the member recession cones. -/
theorem recessionCone_sInter_eq_sInter_recessionCone_of_nonneg_ray
    (hS_nonempty : (⋂₀ S).Nonempty)
    (hRayToRecession :
      ∀ t ∈ S, ∀ {x : P} {y : E}, x ∈ t →
        (∀ a : 𝕜, 0 ≤ a → x + a • y ∈ t) → y ∈ (0⁺[𝕜] t : Set E)) :
    (0⁺[𝕜] (⋂₀ S) : Set E) = ⋂₀ ((fun t : Set P ↦ t.recessionCone 𝕜) '' S) := by
  exact Set.Subset.antisymm
    (recessionCone_sInter_subset_sInter_recessionCone_of_nonneg_ray
      (S := S) hS_nonempty hRayToRecession)
    (sInter_recessionCone_subset_recessionCone_sInter (S := S))

/-- Primitive bridge-layer reverse inclusion for indexed intersections:
if `⋂ i, C i` is nonempty and each member `C i` has the owner-side bridge property that one
base-point nonnegative ray in direction `y` implies `y ∈ 0⁺[𝕜] (C i)`, then every recession
direction of the intersection belongs to each member recession cone. -/
theorem recessionCone_iInter_subset_iInter_recessionCone_of_nonneg_ray
    (hC_nonempty : (⋂ i, C i).Nonempty)
    (hRayToRecession :
      ∀ i, ∀ {x : P} {y : E}, x ∈ C i →
        (∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C i) → y ∈ (0⁺[𝕜] (C i) : Set E)) :
    (0⁺[𝕜] (⋂ i, C i) : Set E) ⊆ ⋂ i, (0⁺[𝕜] (C i) : Set E) := by
  simpa [Set.sInter_range] using
    (recessionCone_sInter_subset_sInter_recessionCone_of_nonneg_ray
      (S := Set.range C)
      (by simpa [Set.sInter_range] using hC_nonempty)
      (fun t ht {x} {y} hx hRay ↦ by
        rcases ht with ⟨i, rfl⟩
        exact hRayToRecession i hx hRay))

/-- Primitive bridge-layer equality for indexed intersections:
if `⋂ i, C i` is nonempty and each member `C i` has the owner-side bridge property that one
base-point nonnegative ray in direction `y` implies `y ∈ 0⁺[𝕜] (C i)`, then the recession cone of
the intersection is the intersection of the member recession cones. -/
theorem recessionCone_iInter_eq_iInter_recessionCone_of_nonneg_ray
    (hC_nonempty : (⋂ i, C i).Nonempty)
    (hRayToRecession :
      ∀ i, ∀ {x : P} {y : E}, x ∈ C i →
        (∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C i) → y ∈ (0⁺[𝕜] (C i) : Set E)) :
    (0⁺[𝕜] (⋂ i, C i) : Set E) = ⋂ i, (0⁺[𝕜] (C i) : Set E) := by
  simpa [Set.sInter_range] using
    (recessionCone_sInter_eq_sInter_recessionCone_of_nonneg_ray
      (S := Set.range C)
      (by simpa [Set.sInter_range] using hC_nonempty)
      (fun t ht {x} {y} hx hRay ↦ by
        rcases ht with ⟨i, rfl⟩
        exact hRayToRecession i hx hRay))

end

end Set

namespace Convex

section

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable {C : I → Set E}
variable {S : Set (Set E)}

/-- The nontrivial inclusion in Corollary 8.3.3 at the intrinsic set-family layer:
for closed convex members of `S` with nonempty intersection, every direction in
`0⁺[𝕜] (⋂₀ S)` lies in each member recession cone. -/
theorem recessionCone_sInter_subset_sInter_recessionCone
    (hS_convex : ∀ t ∈ S, Convex 𝕜 t) (hS_closed : ∀ t ∈ S, IsClosed t)
    (hS_nonempty : (⋂₀ S).Nonempty) :
    0⁺[𝕜] (⋂₀ S) ⊆ ⋂₀ ((fun t : Set E ↦ 0⁺[𝕜] t) '' S) := by
  exact Set.recessionCone_sInter_subset_sInter_recessionCone_of_nonneg_ray
    (S := S) hS_nonempty
    (fun t ht {x} {y} hx hRay ↦
      (hS_convex t ht).mem_recessionCone_of_nonneg_ray (x := x) (y := y) (hS_closed t ht) hRay)

/-- Corollary 8.3.3 at the intrinsic set-family layer:
for closed convex members of `S` with nonempty intersection, the recession cone of `⋂₀ S` is the
intersection of the member recession cones. -/
theorem recessionCone_sInter_eq_sInter_recessionCone
    (hS_convex : ∀ t ∈ S, Convex 𝕜 t) (hS_closed : ∀ t ∈ S, IsClosed t)
    (hS_nonempty : (⋂₀ S).Nonempty) :
    0⁺[𝕜] (⋂₀ S) = ⋂₀ ((fun t : Set E ↦ 0⁺[𝕜] t) '' S) := by
  exact Set.recessionCone_sInter_eq_sInter_recessionCone_of_nonneg_ray
    (S := S) hS_nonempty
    (fun t ht {x} {y} hx hRay ↦
      (hS_convex t ht).mem_recessionCone_of_nonneg_ray (x := x) (y := y) (hS_closed t ht) hRay)

/-- The nontrivial inclusion in Corollary 8.3.3: for closed convex families with nonempty
intersection, every direction in `0⁺[𝕜] (⋂ i, C i)` lies in each `0⁺[𝕜] (C i)`. -/
theorem recessionCone_iInter_subset_iInter_recessionCone
    (hC_convex : ∀ i, Convex 𝕜 (C i)) (hC_closed : ∀ i, IsClosed (C i))
    (hC_nonempty : (⋂ i, C i).Nonempty) :
    0⁺[𝕜] (⋂ i, C i) ⊆ ⋂ i, 0⁺[𝕜] (C i) := by
  simpa [Set.sInter_range] using
    (recessionCone_sInter_subset_sInter_recessionCone (S := Set.range C)
      (fun t ht ↦ by
        rcases ht with ⟨i, rfl⟩
        exact hC_convex i)
      (fun t ht ↦ by
        rcases ht with ⟨i, rfl⟩
        exact hC_closed i)
      (by simpa [Set.sInter_range] using hC_nonempty))

/-- Corollary 8.3.3: if `(C i)_{i ∈ I}` is a family of closed convex subsets of a topological
module over `𝕜` whose intersection is nonempty, then the recession cone
`0⁺[𝕜] (⋂ i, C i)` is the intersection of the recession cones `0⁺[𝕜] (C i)`.
-/
-- Proof sketch: for `y ∈ 0⁺[𝕜] (⋂ i, C i)`, choose `x ∈ ⋂ i, C i`; then the whole ray
-- `x + a • y` stays in every `C i`, so Theorem 8.3 applied to each closed convex `C i` shows
-- `y ∈ 0⁺[𝕜] (C i)`. Conversely, if `y` lies in every `0⁺[𝕜] (C i)`, then every
-- nonnegative translate of every `x ∈ ⋂ i, C i` stays in each `C i`, hence in their intersection.
theorem recessionCone_iInter_eq_iInter_recessionCone
    (hC_convex : ∀ i, Convex 𝕜 (C i)) (hC_closed : ∀ i, IsClosed (C i))
    (hC_nonempty : (⋂ i, C i).Nonempty) :
    0⁺[𝕜] (⋂ i, C i) = ⋂ i, 0⁺[𝕜] (C i) := by
  simpa [Set.sInter_range] using
    (recessionCone_sInter_eq_sInter_recessionCone (S := Set.range C)
      (fun t ht ↦ by
        rcases ht with ⟨i, rfl⟩
        exact hC_convex i)
      (fun t ht ↦ by
        rcases ht with ⟨i, rfl⟩
        exact hC_closed i)
      (by simpa [Set.sInter_range] using hC_nonempty))

end

end Convex

end

/-! ### Theorem_8_3 (from Chap02) -/
section

open scoped Rockafellar

universe u v

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-
Source/core/bridge triage:

- `source-facing`: Theorem 8.3 says that for a closed convex set, the existence of one forward ray
  in direction `y` forces `y` to be a recession direction for the whole set. Its second clause
  then upgrades recession directions of `C` to recession directions of `ri C`.
- `core/canonical`: the owner-side notions already present in the chapter are the source-facing
  `0⁺[𝕜] C` from Definition 8.0.2, together with mathlib's `Convex 𝕜`, `closure`, and
  `intrinsicInterior 𝕜`. The derived API therefore belongs on the `Convex` owner abstraction
  rather than as parallel flat wrappers.
- `bridge/view`: Rockafellar's `0⁺ C` and `0⁺ (ri C)` are rendered here by the scalar-parameterized
  owner `0⁺[𝕜] C` and `0⁺[𝕜] (ri[𝕜](C))`; the
  textbook real surface is recovered by specializing `𝕜 = ℝ`.
- Domain-style sampling used here: `recessionCone`, `Set.mem_recessionCone_iff`,
  `Set.mem_recessionCone_iff_vadd`,
  `Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone`,
  `Convex.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior`, and the
  chapter owner
  notation `ri[𝕜](C)`.
- Primitive data vs derived API: the primitive inputs are the set `C`, the direction `y`, the
  closed/convex hypotheses, and one chosen base-point ray witness for part (1). The explicit
  base-point theorem is therefore the primitive owner-side API, while the existential source
  formulation is kept as a thin companion. The owner-style content of part (2) is the cone
  inclusion `0⁺ C ⊆ 0⁺ (ri C)`; the pointwise membership implication is derived from that
  inclusion and should not remain the primitive public statement.
- Layer target: this item remains `source-facing`, expressed in the chapter's existing
  recession-cone language but with the derived API placed on the `Convex` owner. The ray criterion
  stays at the general ordered topological-semimodule level, while the `intrinsicInterior`
  clause is stated at the intrinsic-closure topological-vector-space level already canonicalized
  in Chapter 6.
-/

namespace Convex

variable {C : Set E} {x y : E}

/-- Primitive owner-side affine-action form of Theorem 8.3 (1): if a closed convex set `C`
contains the forward nonnegative ray `a • y +ᵥ x` from a chosen base point `x`, then `y` lies in
the recession cone `0⁺[𝕜] C`. The textbook real formulation is recovered by specializing `𝕜 = ℝ`,
while additive `x + a • y` source wording is the companion theorem below. -/
-- Proof sketch: for any `z ∈ C` and `a ≥ 0`, convexity puts
-- `t • y +ᵥ x ∈ C` for all `t ≥ 0`, so the ray produces `y ∈ asymptoticCone 𝕜 C`; then the
-- closed-convex asymptotic-cone ray theorem gives `z + a • y ∈ C` for every `z ∈ C`, `a ≥ 0`.
theorem mem_recessionCone_of_nonneg_vadd_ray (hC : Convex 𝕜 C) (hCclosed : IsClosed C)
    (hRay : ∀ a : 𝕜, 0 ≤ a → a • y +ᵥ x ∈ C) :
    y ∈ 0⁺[𝕜] C := by
  have hy_asymptotic : y ∈ asymptoticCone 𝕜 C := by
    rw [mem_asymptoticCone_iff]
    have hRay_eventually : ∀ᶠ a : 𝕜 in Filter.atTop, a • y + x ∈ C := by
      filter_upwards [Filter.eventually_ge_atTop (0 : 𝕜)] with a ha
      simpa [vadd_eq_add] using hRay a ha
    exact
      ((Filter.Tendsto.atTop_smul_const_tendsto_asymptoticNhds
          (k := 𝕜) (l := Filter.atTop) y Filter.tendsto_id).asymptoticNhds_vadd_const x).frequently
        (Filter.Eventually.frequently <| by simpa [vadd_eq_add] using hRay_eventually)
  rw [Set.mem_recessionCone_iff_vadd]
  intro z hz a ha
  exact hC.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hCclosed ha hy_asymptotic hz

/-- Source-facing additive form of Theorem 8.3 (1): if a closed convex set `C` contains the
forward nonnegative ray `x + a • y` from a chosen base point `x`, then `y ∈ 0⁺[𝕜] C`. -/
theorem mem_recessionCone_of_nonneg_ray (hC : Convex 𝕜 C) (hCclosed : IsClosed C)
    (hRay : ∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C) :
    y ∈ 0⁺[𝕜] C := by
  refine hC.mem_recessionCone_of_nonneg_vadd_ray (x := x) hCclosed ?_
  intro a ha
  simpa [vadd_eq_add, add_comm] using hRay a ha

/-- Owner-level positive-ray form of Theorem 8.3 (1): if `x ∈ C` and all strictly positive
translates `x + a • y` stay in a closed convex set `C`, then `y ∈ 0⁺[𝕜] C`. -/
-- Proof sketch: reduce to the nonnegative-ray criterion by splitting `a ≥ 0` into `a = 0` and
-- `0 < a`.
theorem mem_recessionCone_of_pos_ray (hC : Convex 𝕜 C) (hCclosed : IsClosed C) (hx : x ∈ C)
    (hRay : ∀ a : 𝕜, 0 < a → x + a • y ∈ C) :
    y ∈ 0⁺[𝕜] C := by
  refine hC.mem_recessionCone_of_nonneg_vadd_ray (x := x) hCclosed ?_
  intro a ha
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simpa [vadd_eq_add] using hx
  · simpa [vadd_eq_add, add_comm] using hRay a ha_pos

/-- Theorem 8.3 (1), source-facing form: if a closed convex set `C` contains one forward
strictly-positive ray `{x + a • y | 0 < a}` from a base point `x ∈ C`, then `y` lies in the
recession cone `0⁺[𝕜] C`. The source's real topological-vector-space statement is recovered by
specializing `𝕜 = ℝ`. -/
-- Proof sketch: extract the base point and apply the owner-level positive-ray theorem above.
theorem mem_recessionCone_of_exists_pos_ray (hC : Convex 𝕜 C) (hCclosed : IsClosed C)
    (hRay : ∃ x : E, x ∈ C ∧ ∀ a : 𝕜, 0 < a → x + a • y ∈ C) :
    y ∈ 0⁺[𝕜] C := by
  rcases hRay with ⟨x, hx, hRay⟩
  exact hC.mem_recessionCone_of_pos_ray (x := x) hCclosed hx hRay

end Convex

end

section

open scoped Rockafellar

universe u v

variable {𝕜 : Type v} [Field 𝕜] [PartialOrder 𝕜] [PosMulReflectLT 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

namespace Convex

/-- Theorem 8.3 (2): for a convex set in a topological vector space over an ordered field `𝕜`,
recession direction of `C` is also a recession direction of its relative interior `ri[𝕜](C)`,
formalized here as the owner-level inclusion `0⁺[𝕜] C ⊆ 0⁺[𝕜] (ri[𝕜](C))`. The source's real
statement is recovered by specializing `𝕜 = ℝ`. -/
-- Proof sketch: let `x ∈ ri[𝕜](C)` and `a ≥ 0`. Since `y ∈ 0⁺[𝕜] C`,
-- `x + (a + a) • y ∈ C`. Theorem 6.1 applied to the segment from `x` to `x + (a + a) • y`
-- in intrinsic-closure form shows that its midpoint `x + a • y` lies in `ri[𝕜](C)`. Thus every
-- nonnegative translate of every point of `ri[𝕜](C)` stays in `ri[𝕜](C)`.
theorem recessionCone_subset_ri {C : Set E} (hCconv : Convex 𝕜 C) :
    0⁺[𝕜] C ⊆ 0⁺[𝕜] (ri[𝕜](C)) := by
  intro y hy
  rw [Set.mem_recessionCone_iff]
  intro x hx a ha
  have hxy_mem_C : x + (a + a) • y ∈ C :=
    (Set.mem_recessionCone_iff.mp hy) x (intrinsicInterior_subset hx) (a + a) (add_nonneg ha ha)
  have hxy_mem_cl : x + (a + a) • y ∈ intrinsicClosure 𝕜 C :=
    subset_intrinsicClosure hxy_mem_C
  have hseg : openSegment 𝕜 x (x + (a + a) • y) ⊆ ri[𝕜](C) :=
    hCconv.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hx hxy_mem_cl
  apply hseg
  refine ⟨(1 / 2 : 𝕜), (1 / 2 : 𝕜), ?_, ?_, ?_, ?_⟩
  · exact half_pos zero_lt_one
  · exact half_pos zero_lt_one
  · ring
  · module

end Convex

end

/-! ### Corollary_8_3_4 (from Chap02) -/
section

universe u v w

variable {𝕜 : Type v} [Semiring 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {F : Type w} [AddCommMonoid F] [Module 𝕜 F]

namespace LinearMap

/-- For any linear map, preimages preserve recession directions in the primitive direction:
if `A y` is a recession direction of `C`, then `y` is a recession direction of `A ⁻¹' C`. -/
theorem preimage_recessionCone_subset
    (A : E →ₗ[𝕜] F) (C : Set F) :
    A ⁻¹' (0⁺[𝕜] C) ⊆ 0⁺[𝕜] (A ⁻¹' C) := by
  intro y hy
  change A y ∈ 0⁺[𝕜] C at hy
  rw [Set.mem_recessionCone_iff]
  intro x hx a ha
  change A (x + a • y) ∈ C
  simpa [map_add, map_smul] using (Set.mem_recessionCone_iff.mp hy) (A x) hx a ha

end LinearMap

namespace Set

variable {C : Set F}

/-- Primitive bridge-layer inclusion for linear preimages: if a nonempty preimage `A ⁻¹' C` is
given and one nonnegative ray in `C` implies recession-cone membership in `C`, then every
recession direction of `A ⁻¹' C` maps to a recession direction of `C`. -/
theorem recessionCone_linear_preimage_subset_of_nonneg_ray
    (A : E →ₗ[𝕜] F) (hpre_nonempty : (A ⁻¹' C).Nonempty)
    (hRayToRecession :
      ∀ {x y : F}, x ∈ C →
        (∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C) → y ∈ 0⁺[𝕜] C) :
    0⁺[𝕜] (A ⁻¹' C) ⊆ A ⁻¹' (0⁺[𝕜] C) := by
  rcases hpre_nonempty with ⟨x, hx⟩
  intro y hy
  change A y ∈ 0⁺[𝕜] C
  have hAx : A x ∈ C := hx
  exact hRayToRecession hAx fun a ha ↦ by
    simpa [Set.mem_preimage, map_add, map_smul] using
      (Set.mem_recessionCone_iff.mp hy) x hx a ha

/-- Primitive bridge-layer equality for linear preimages: if `A ⁻¹' C` is nonempty and one
nonnegative ray in `C` implies recession-cone membership in `C`, then the recession cone of the
preimage is exactly the preimage of the recession cone. -/
theorem recessionCone_linear_preimage_eq_preimage_recessionCone_of_nonneg_ray
    (A : E →ₗ[𝕜] F) (hpre_nonempty : (A ⁻¹' C).Nonempty)
    (hRayToRecession :
      ∀ {x y : F}, x ∈ C →
        (∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C) → y ∈ 0⁺[𝕜] C) :
    0⁺[𝕜] (A ⁻¹' C) = A ⁻¹' (0⁺[𝕜] C) := by
  exact Set.Subset.antisymm
    (recessionCone_linear_preimage_subset_of_nonneg_ray
      (A := A) (C := C) hpre_nonempty hRayToRecession)
    (A.preimage_recessionCone_subset C)

end Set

end

section

universe u v w

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {F : Type w} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

namespace Convex

variable {C : Set F}

/-
Source/core/bridge triage:
- `source-facing`: Corollary 8.3.4 identifies the recession cone of a linear preimage with the
  preimage of the recession cone.
- `core/canonical`: the chapter owner object for this notion is `recessionCone`; the primitive
  linear-preimage bridge theorem is owner-level data in `Set`, while the closed-convex upgrade
  remains on the source-facing `Convex` owner namespace.
- `bridge/view`: the closed-convex comparison with mathlib's `asymptoticCone ℝ` already lives
  upstream in `recessionCone_eq_asymptoticCone`, so this file should not keep a second public
  wrapper around that bridge.
- Domain-style sampling: `recessionCone`, `Set.mem_recessionCone_iff`,
  `LinearMap.preimage_recessionCone_subset`,
  `Set.recessionCone_linear_preimage_subset_of_nonneg_ray`,
  `Set.recessionCone_linear_preimage_eq_preimage_recessionCone_of_nonneg_ray`,
  `Convex.mem_recessionCone_of_nonneg_ray`, and `Convex.linear_preimage`.
- Primitive data vs derived API: the primitive preimage inclusion
  `A ⁻¹' (0⁺[𝕜] C) ⊆ 0⁺[𝕜] (A ⁻¹' C)` depends only on linearity and the owner definition. The
  reverse inclusion from `0⁺[𝕜] (A ⁻¹' C)` to `A ⁻¹' (0⁺[𝕜] C)` is split into a primitive
  capability-style bridge in `Set` and the genuinely closed-convex upgrade from Theorem 8.3.
- Ambient minimization: the proof uses only the scalar-generic Chapter 8 ray criterion from
  `Theorem_8_3`, so the theorem should live over the same ordered topological field `𝕜` rather
  than being frozen to `ℝ`.
- Layer target: split owner layers (`Set` primitive bridge, `Convex` source-facing corollary).
-/

/-- Corollary 8.3.4, nontrivial inclusion: when `A ⁻¹' C` is nonempty, every recession direction
of `A ⁻¹' C` maps to a recession direction of `C`. -/
theorem recessionCone_linear_preimage_subset
    (hC_convex : Convex 𝕜 C) (A : E →ₗ[𝕜] F) (hC_closed : IsClosed C)
    (hpre_nonempty : (A ⁻¹' C).Nonempty) :
    0⁺[𝕜] (A ⁻¹' C) ⊆ A ⁻¹' (0⁺[𝕜] C) := by
  exact Set.recessionCone_linear_preimage_subset_of_nonneg_ray
    (A := A) (C := C) hpre_nonempty
    (fun {x y} hx hRay ↦
      hC_convex.mem_recessionCone_of_nonneg_ray (x := x) (y := y) hC_closed hRay)

/-- Corollary 8.3.4: if `A : E →ₗ[𝕜] F` is linear, `C ⊆ F` is closed and convex, and the preimage
`A ⁻¹' C` is nonempty, then the recession cone `0⁺[𝕜] (A⁻¹ C)` is exactly the preimage of
`0⁺[𝕜] C`. The textbook real statement is recovered by specializing `𝕜 = ℝ`. -/
-- Proof sketch: combine the nontrivial closed-convex inclusion
-- `0⁺[𝕜] (A ⁻¹' C) ⊆ A ⁻¹' (0⁺[𝕜] C)` with the primitive linearity inclusion
-- `A ⁻¹' (0⁺[𝕜] C) ⊆ 0⁺[𝕜] (A ⁻¹' C)`.
theorem recessionCone_linear_preimage
    (hC_convex : Convex 𝕜 C) (A : E →ₗ[𝕜] F) (hC_closed : IsClosed C)
    (hpre_nonempty : (A ⁻¹' C).Nonempty) :
    0⁺[𝕜] (A ⁻¹' C) = A ⁻¹' (0⁺[𝕜] C) := by
  exact Set.recessionCone_linear_preimage_eq_preimage_recessionCone_of_nonneg_ray
    (A := A) (C := C) hpre_nonempty
    (fun {x y} hx hRay ↦
      hC_convex.mem_recessionCone_of_nonneg_ray (x := x) (y := y) hC_closed hRay)

end Convex

end
