import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_11_6

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar
open AffineMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜]

namespace Convex

/-
Source/core/bridge triage:
- `source-facing`: Corollary 11.6.2 characterizes relative boundary points of a convex set by the
  existence of a nonconstant linear function attaining its maximum at the point.
- `core/canonical`: the owner abstractions are `intrinsicFrontier 𝕜`, `Convex 𝕜`, the
  singleton specialization of the supporting-hyperplane criterion
  `exists_nontrivial_supporting_hyperplane_containing_iff_disjoint_intrinsicInterior`, the
  proper-separation bridge
  `AffineSubspace.separatesProperly_iff_isNontrivialSupportingHyperplane_and_subset`, and the
  relative-interior prolongation criterion
  `Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior`.
- `bridge/view`: the forward implication extracts a maximizing nonconstant linear functional from
  the proper-separation owner data attached to a supporting hyperplane through `x`; the reverse
  implication rules out relative interior points by prolonging a segment past `x` with Theorem
  6.4 and contradicting maximality.
- Primitive data vs derived API: the primitive inputs are the convex set `C`, the point `x`, and
  membership `hx : x ∈ C`; relative-boundary membership and existence of a maximizing
  nonconstant functional are theorem-level content derived from the owner abstractions above.
- Layer target: `source-facing`, with the conclusion stated directly in terms of a linear
  functional rather than introducing a wrapper around supporting hyperplanes.
- Ambient refinement: the proof uses only normed-space and pairing owner APIs (`intrinsicFrontier`,
  proper separation, supporting hyperplanes, and the line-map relative-interior criterion), so
  the public statement is kept on finite-dimensional pairing spaces over ordered
  nontrivially-normed fields rather than an inner-product model.
-/

/-- Corollary 11.6.2, in canonical ambient form: for a convex set `C`, a point `x ∈ C` lies in
its relative boundary iff some linear functional on the ambient space attains a maximum over `C`
at `x` and is nonconstant on `C`. Specializing to `EuclideanSpace ℝ (Fin n)` recovers the
textbook `R^n` statement. -/
-- Proof sketch: for `→`, apply
-- `exists_nontrivial_supporting_hyperplane_of_mem_rb` to get a nontrivial
-- supporting hyperplane `H` through `x`, convert this to proper separation of `{x}` and `C`, and
-- read off a separating normal `b` from `H.Separates`; its negated pairing functional is
-- maximized at `x`, and nontriviality gives a strict witness. For `←`, if `x` were in `ri[𝕜](C)`,
-- Theorem 6.4 would prolong the segment from a strict witness `y` past `x` while staying in `C`,
-- and linearity would force a value strictly larger than `h x`, contradicting maximality.
theorem mem_rb_iff_exists_nonconstant_linearMap_maximizing
    {C : Set E} (hC : Convex 𝕜 C) {x : E} (hx : x ∈ C) :
    x ∈ rb[𝕜](C) ↔
      ∃ h : E →ₗ[𝕜] 𝕜, IsMaxOn h C x ∧ ∃ y ∈ C, h y < h x := by
  constructor
  · intro hxbd
    rcases exists_nontrivial_supporting_hyperplane_of_mem_rb (Y := E) hC hx hxbd with
      ⟨H, hH, hxH⟩
    have hSepProper : H.SeparatesProperly (Y := E) ({x} : Set E) C := by
      refine
        (AffineSubspace.separatesProperly_iff_isNontrivialSupportingHyperplane_and_subset
          (H := H) (C := C) (D := ({x} : Set E))
          (Set.singleton_nonempty x) (Set.singleton_subset_iff.2 hx)).2 ?_
      exact ⟨hH, Set.singleton_subset_iff.2 hxH⟩
    rcases hSepProper.separates with ⟨b, β, _hb, hH_eq, _hxLE, hCGE⟩
    let fb : E →ₗ[𝕜] 𝕜 := HasLinearPairing.pairingLinear.flip b
    have hx_eq : (⟪x, b⟫ₚ : 𝕜) = β := by
      rw [hH_eq] at hxH
      exact mem_affineHyperplane_iff.mp hxH
    have hx_eq' : β = fb x := by
      simpa [fb] using hx_eq.symm
    refine ⟨-fb, ?_, ?_⟩
    · refine isMaxOn_iff.2 ?_
      intro z hzC
      have hz_ge : β ≤ fb z := by
        simpa [fb] using (mem_closedHalfSpaceGE_iff.mp (hCGE hzC))
      have hxz : fb x ≤ fb z := by
        simpa [hx_eq'] using hz_ge
      exact (neg_le_neg hxz : (-fb z) ≤ (-fb x))
    · rcases Set.not_subset.mp hH.not_subset with ⟨y, hyC, hy_notH⟩
      refine ⟨y, hyC, ?_⟩
      have hy_ge : β ≤ fb y := by
        simpa [fb] using (mem_closedHalfSpaceGE_iff.mp (hCGE hyC))
      have hy_ne : fb y ≠ β := by
        intro hy_eq
        apply hy_notH
        rw [hH_eq]
        exact mem_affineHyperplane_iff.mpr (by simpa [fb] using hy_eq)
      have hy_gt : β < fb y := lt_of_le_of_ne hy_ge hy_ne.symm
      have hxy : fb x < fb y := by
        simpa [hx_eq'] using hy_gt
      exact (neg_lt_neg hxy : (-fb y) < (-fb x))
  · rintro ⟨h, hmax, y, hyC, hy_lt⟩
    have h_not_ri : x ∉ ri[𝕜](C) := by
      intro hxri
      rcases
          Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior
            (𝕜 := 𝕜) (C := C) (z := x) hxri y hyC with
        ⟨μ, hμ_gt, hzC⟩
      have hz_le : h (lineMap y x μ) ≤ h x := hmax hzC
      have hz_eq : h (lineMap y x μ) = (1 - μ) * h y + μ * h x := by
        calc
          h (lineMap y x μ) = lineMap (h y) (h x) μ := by
            simpa only [LinearMap.coe_toAffineMap] using h.toAffineMap.apply_lineMap y x μ
          _ = (1 - μ) * h y + μ * h x := by
            simp [lineMap_apply_module, smul_eq_mul]
      have hz_le' : (1 - μ) * h y + μ * h x ≤ h x := by
        simpa [hz_eq] using hz_le
      have hμ : 0 < μ - 1 := sub_pos.mpr hμ_gt
      have hxy : 0 < h x - h y := sub_pos.mpr hy_lt
      have hrewrite : (1 - μ) * h y + μ * h x = h x + (μ - 1) * (h x - h y) := by
        ring
      have hprod_nonpos : (μ - 1) * (h x - h y) ≤ 0 := by
        have hz_le'' : h x + (μ - 1) * (h x - h y) ≤ h x := by
          simpa [hrewrite] using hz_le'
        exact (add_le_add_iff_left (h x)).1 (by simpa [add_zero] using hz_le'')
      have hprod_pos : 0 < (μ - 1) * (h x - h y) := mul_pos hμ hxy
      exact (not_lt_of_ge hprod_nonpos) hprod_pos
    rw [← intrinsicClosure_diff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure hx, h_not_ri⟩

end Convex

end
