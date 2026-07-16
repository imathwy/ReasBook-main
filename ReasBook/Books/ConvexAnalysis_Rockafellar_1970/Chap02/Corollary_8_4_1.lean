import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_4

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

open scoped Affine
open Bornology

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 8.4.1 says that for a closed convex set `C`, boundedness of the
  section `M ∩ C` depends only on the parallel class of the affine set `M`.
- `core/canonical`: the owner abstractions are the chapter recession-cone owner `recessionCone`,
  the affine-set object `AffineSubspace 𝕜 E`, its parallelism relation
  `AffineSubspace.Parallel`, and the bornological boundedness predicate `IsBounded`.
- `bridge/view`: the core owner theorem here is the recession-cone identity for affine sections,
  proved directly via `Set.mem_recessionCone_iff`, affine-direction lemmas, and the owner-level
  positive-ray bridge `Convex.mem_recessionCone_of_pos_ray`. The boundedness corollary is then a
  thin specialization through `Convex.isBounded_iff_recessionCone_eq_singleton_zero`.
- Domain-style sampling used here: `Set.mem_recessionCone_iff`,
  `Convex.mem_recessionCone_of_pos_ray`,
  `AffineSubspace.vadd_mem_iff_mem_direction`,
  `AffineSubspace.vadd_mem_of_mem_direction`, and
  `Convex.isBounded_iff_recessionCone_eq_singleton_zero`.
- Primitive data vs derived API: the primitive inputs are the closed convex set `C` and the affine
  subspaces `M` and `M'`; the triviality of the recession cone of a section and the resulting
  boundedness are derived API.
- Layer target: the recession-cone owner theorem is moved to the weaker ordered topological vector
  space layer (`𝕜`, `E`), while the boundedness transfer is stated at the primitive closed-section
  layer (`IsClosed (M : Set E)`, `IsClosed (M' : Set E)`) over the proper normed scalar/ambient
  assumptions forced by the upstream theorem
  `Convex.isBounded_iff_recessionCone_eq_singleton_zero`.
-/

namespace AffineSubspace

local notation:70 M " ∩ₛ " C => ((M : Set E) ∩ C)

private lemma recessionCone_inter_eq_direction_inter_of_nonempty
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (N : AffineSubspace 𝕜 E)
    (hNC_nonempty : (N ∩ₛ C).Nonempty) :
    0⁺[𝕜] (N ∩ₛ C) = (N.direction : Set E) ∩ 0⁺[𝕜] C := by
  ext y
  constructor
  · intro hy
    rcases hNC_nonempty with ⟨x, hx⟩
    have hxN : x ∈ N := hx.1
    rw [Set.mem_recessionCone_iff] at hy
    have hy_dir : y ∈ N.direction := by
      have hxyN : x + (1 : 𝕜) • y ∈ N := (hy x hx 1 zero_le_one).1
      have hxyv : y +ᵥ x ∈ N := by
        simpa [vadd_eq_add, add_comm, one_smul] using hxyN
      exact (N.vadd_mem_iff_mem_direction y hxN).1 hxyv
    have hy_recession_C : y ∈ 0⁺[𝕜] C := by
      exact hC_convex.mem_recessionCone_of_pos_ray (x := x) hC_closed hx.2
        (fun a ha ↦ (hy x hx a ha.le).2)
    exact ⟨hy_dir, hy_recession_C⟩
  · rintro ⟨hy_dir, hy_recession_C⟩
    rw [Set.mem_recessionCone_iff] at hy_recession_C ⊢
    intro x hx a ha
    have hxyN : x + a • y ∈ N := by
      have hsmul_dir : a • y ∈ N.direction := N.direction.smul_mem a hy_dir
      have hxyv : (a • y) +ᵥ x ∈ N := N.vadd_mem_of_mem_direction hsmul_dir hx.1
      simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using hxyv
    exact ⟨hxyN, hy_recession_C x hx.2 a ha⟩

/-- For a closed convex set `C`, nonempty parallel affine sections have equal recession cones. -/
theorem recessionCone_inter_eq_of_parallel
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (M M' : AffineSubspace 𝕜 E)
    (hMC_nonempty : (M ∩ₛ C).Nonempty)
    (hM'C_nonempty : (M' ∩ₛ C).Nonempty)
    (hparallel : M' ∥ M) :
    0⁺[𝕜] (M' ∩ₛ C) = 0⁺[𝕜] (M ∩ₛ C) := by
  calc
    0⁺[𝕜] (M' ∩ₛ C) = (M'.direction : Set E) ∩ 0⁺[𝕜] C :=
      recessionCone_inter_eq_direction_inter_of_nonempty C hC_closed hC_convex M' hM'C_nonempty
    _ = (M.direction : Set E) ∩ 0⁺[𝕜] C := by
      simp [hparallel.direction_eq]
    _ = 0⁺[𝕜] (M ∩ₛ C) := by
      symm
      exact recessionCone_inter_eq_direction_inter_of_nonempty C hC_closed hC_convex M hMC_nonempty

end AffineSubspace

end

section

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜] [Archimedean 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]

open scoped Affine
open Bornology

namespace AffineSubspace

local notation:70 M " ∩ₛ " C => ((M : Set E) ∩ C)

/-- For a closed convex set `C`, nonempty parallel closed affine sections are bounded
simultaneously. -/
theorem isBounded_inter_iff_of_parallel
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (M M' : AffineSubspace 𝕜 E)
    (hMC_closed : IsClosed (M ∩ₛ C)) (hM'C_closed : IsClosed (M' ∩ₛ C))
    (hMC_nonempty : (M ∩ₛ C).Nonempty) (hM'C_nonempty : (M' ∩ₛ C).Nonempty)
    (hparallel : M' ∥ M) :
    IsBounded (M' ∩ₛ C) ↔ IsBounded (M ∩ₛ C) := by
  have hM_recession :
      IsBounded (M ∩ₛ C) ↔ 0⁺[𝕜] (M ∩ₛ C) = ({0} : Set E) :=
    (M.convex.inter hC_convex).isBounded_iff_recessionCone_eq_singleton_zero
      hMC_closed hMC_nonempty
  have hM'_recession :
      IsBounded (M' ∩ₛ C) ↔ 0⁺[𝕜] (M' ∩ₛ C) = ({0} : Set E) :=
    (M'.convex.inter hC_convex).isBounded_iff_recessionCone_eq_singleton_zero
      hM'C_closed hM'C_nonempty
  have hparallel_recession :
      0⁺[𝕜] (M' ∩ₛ C) = 0⁺[𝕜] (M ∩ₛ C) :=
    AffineSubspace.recessionCone_inter_eq_of_parallel C hC_closed hC_convex M M'
      hMC_nonempty hM'C_nonempty hparallel
  constructor
  · intro hM'_bounded
    have hM'_recession_zero : 0⁺[𝕜] (M' ∩ₛ C) = ({0} : Set E) := hM'_recession.mp hM'_bounded
    have hM_recession_zero : 0⁺[𝕜] (M ∩ₛ C) = ({0} : Set E) := by
      calc
        0⁺[𝕜] (M ∩ₛ C) = 0⁺[𝕜] (M' ∩ₛ C) := hparallel_recession.symm
        _ = ({0} : Set E) := hM'_recession_zero
    exact hM_recession.mpr hM_recession_zero
  · intro hM_bounded
    have hM_recession_zero : 0⁺[𝕜] (M ∩ₛ C) = ({0} : Set E) := hM_recession.mp hM_bounded
    have hM'_recession_zero : 0⁺[𝕜] (M' ∩ₛ C) = ({0} : Set E) := by
      calc
        0⁺[𝕜] (M' ∩ₛ C) = 0⁺[𝕜] (M ∩ₛ C) := hparallel_recession
        _ = ({0} : Set E) := hM_recession_zero
    exact hM'_recession.mpr hM'_recession_zero

-- Proof sketch: if `M' ∩ C` is empty, it is bounded. Otherwise Theorem 8.4 reduces boundedness of
-- both sections to triviality of their recession cones. The owner theorem
-- `AffineSubspace.recessionCone_inter_eq_of_parallel` identifies these two recession cones under
-- parallelism, so boundedness of `M ∩ C` forces boundedness of `M' ∩ C`.
/-- Corollary 8.4.1 (owner form): if `C` is a closed convex set, `M ∩ C` is nonempty and bounded,
and `M'` is parallel to `M`, then `M' ∩ C` is bounded as soon as both affine sections are closed.
The textbook finite-dimensional `ℝ^n` statement is recovered by specializing to that ambient
layer, where affine subspaces are automatically closed. -/
theorem isBounded_inter_of_parallel
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (M M' : AffineSubspace 𝕜 E)
    (hMC_closed : IsClosed (M ∩ₛ C)) (hM'C_closed : IsClosed (M' ∩ₛ C))
    (hMC_nonempty : (M ∩ₛ C).Nonempty)
    (hMC_bdd : IsBounded (M ∩ₛ C)) (hparallel : M' ∥ M) :
    IsBounded (M' ∩ₛ C) := by
  by_cases hM'C_nonempty : (M' ∩ₛ C).Nonempty
  · exact
      (isBounded_inter_iff_of_parallel C hC_closed hC_convex M M' hMC_closed hM'C_closed
        hMC_nonempty hM'C_nonempty hparallel).2 hMC_bdd
  · have hM'C_empty : (M' ∩ₛ C) = ∅ := Set.not_nonempty_iff_eq_empty.mp hM'C_nonempty
    simp [hM'C_empty]

end AffineSubspace

end
