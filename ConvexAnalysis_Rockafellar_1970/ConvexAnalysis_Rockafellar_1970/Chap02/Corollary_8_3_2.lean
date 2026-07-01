import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_3

-- Declarations for this item will be appended below by the statement pipeline.

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
