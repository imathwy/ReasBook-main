import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_7_10
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_11_6

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 11.6.1 says that a convex set has a nonzero normal vector at each of
  its boundary points.
- `core/canonical`: the owner notions already present in the project are the relative boundary
  `intrinsicFrontier 𝕜 C`, the normal-cone owner `normalCone C x`, and the
  boundary-point supporting-hyperplane bridge
  `exists_nontrivial_supporting_hyperplane_of_mem_rb`, together with the proper
  separation bridge
  `AffineSubspace.separatesProperly_iff_isNontrivialSupportingHyperplane_and_subset`.
- `bridge/view`: the proof converts the supporting hyperplane supplied by the Chapter 11 bridge
  into a proper separator of `{x}` and `C`, then reads off a separating normal and flips its sign
  to satisfy the normal-cone inequality orientation at `x`.
- Domain-style sampling used here: `intrinsicFrontier`, `normalCone`,
  `exists_nontrivial_supporting_hyperplane_of_mem_rb`,
  `AffineSubspace.IsNontrivialSupportingHyperplane`,
  `AffineSubspace.SeparatesProperly`, and `AffineSubspace.Separates`.
- Primitive data vs derived API: the primitive inputs are the convex set `C`, the point `x`, and
  the witness pair `hx : x ∈ C`, `hxbd : x ∈ rb[𝕜](C)`; the supporting hyperplane
  and the normal vector are derived existential outputs.
- Layer target: `source-facing`, stated directly as existence of a nonzero normal at a boundary
  point, while using the canonical relative-boundary API to represent “boundary”.
- Ambient refinement: the supporting-hyperplane owner API and the normal-cone owner already live
  on arbitrary finite-dimensional pairing spaces over ordered normed fields, so the corollary is
  stated at that canonical ambient layer rather than at the coordinate model
  `EuclideanSpace ℝ (Fin n)`.
-/

namespace Convex

/-- Corollary 11.6.1: a convex set has a non-zero normal at each of its boundary points,
represented here in canonical ambient form by a point `x ∈ C` lying in the relative boundary
`rb[𝕜](C)` of a convex subset of a finite-dimensional pairing space `(V, Y)` over `𝕜`. -/
-- Proof sketch: apply the singleton-specialized owner bridge
-- `exists_nontrivial_supporting_hyperplane_of_mem_rb` to obtain a non-trivial
-- supporting hyperplane to `C` passing through `x`, then unpack the canonical closed-half-space
-- presentation of that supporting hyperplane and verify the normal-cone inequalities directly via
-- `mem_normalCone_iff`.
theorem exists_nonzero_normal_of_mem_rb {C : Set V} (hC : Convex 𝕜 C)
    {x : V} (hx : x ∈ C) (hxbd : x ∈ rb[𝕜](C)) :
    ∃ b : Y, b ≠ 0 ∧ b ∈ N[𝕜](x | C) := by
  rcases exists_nontrivial_supporting_hyperplane_of_mem_rb (Y := Y) hC hx hxbd with
    ⟨H, hH, hxH⟩
  have hsepProper : H.SeparatesProperly (Y := Y) ({x} : Set V) C := by
    refine
      (AffineSubspace.separatesProperly_iff_isNontrivialSupportingHyperplane_and_subset
          (hD_nonempty := Set.singleton_nonempty x)
          (hDC := Set.singleton_subset_iff.2 hx)).2 ?_
    exact ⟨hH, Set.singleton_subset_iff.2 hxH⟩
  rcases hsepProper.separates.symm with ⟨b, β, hb, _hH_eq, hC_le, hx_ge⟩
  have hb0 : b ≠ 0 := by
    intro hb_zero
    apply hb
    ext y
    simp [hb_zero]
  refine ⟨b, hb0, ?_⟩
  rw [mem_normalCone_iff]
  refine ⟨hx, ?_⟩
  intro y hy
  have hy_le_β : (⟪y, b⟫ₚ : 𝕜) ≤ β := by
    exact mem_closedHalfSpaceLE_iff.mp (hC_le hy)
  have hβ_le_x : β ≤ (⟪x, b⟫ₚ : 𝕜) := by
    exact mem_closedHalfSpaceGE_iff.mp (hx_ge (by simp))
  have hyx : (⟪y, b⟫ₚ : 𝕜) ≤ ⟪x, b⟫ₚ := le_trans hy_le_β hβ_le_x
  have hsub_nonneg : (0 : 𝕜) ≤ (⟪x, b⟫ₚ : 𝕜) - ⟪y, b⟫ₚ := sub_nonneg.mpr hyx
  simpa [sub_eq_add_neg, map_add, map_neg, add_assoc, add_left_comm, add_comm] using hsub_nonneg

end Convex

end
