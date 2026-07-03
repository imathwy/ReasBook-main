import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_11_6_1 (from Chap03) -/
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

/-! ### Corollary_11_6_2 (from Chap03) -/
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

/-! ### Theorem_11_6 (from Chap03) -/
section

open scoped Rockafellar

variable {𝕜 : Type*} [CommRing 𝕜] [Preorder 𝕜]
variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 11.6 characterizes when a convex set `C` admits a non-trivial
  supporting hyperplane containing a given nonempty convex subset `D ⊆ C`.
- `core/canonical`: the owner abstractions are `Convex 𝕜`, the relative interior operator
  `intrinsicInterior 𝕜`, the Chapter 11 predicate `AffineSubspace.IsNontrivialSupportingHyperplane`,
  and the proper-separation relation `AffineSubspace.SeparatesProperly`.
- `bridge/view`: the textbook phrase "supporting hyperplane to `C` containing `D`" is expressed by
  `H.IsNontrivialSupportingHyperplane Y C ∧ D ⊆ H`, while the proof route factors through Theorem
  11.3 on proper separation.
- Primitive data vs derived API: the primitive inputs are the two sets together with convexity,
  nonemptiness of `D`, and the inclusion `D ⊆ C`; existence of a containing supporting hyperplane
  and the disjointness criterion are theorem-level content.
- Domain-style sampling used here: `AffineSubspace.IsNontrivialSupportingHyperplane` from
  `Text_11_3_4`, `AffineSubspace.SeparatesProperly` from `Text_11_0_2`, the proper-separation
  criterion `exists_separatesProperly_iff_disjoint_ri` from
  `Theorem_11_3`, and the `Convex`-owner relative-interior inclusion theorem
  from `Corollary_6_5_2`.
- Layer target: `source-facing`, with the theorem stated directly in the supporting-hyperplane API
  and the canonical intrinsic-interior language, rather than by introducing a wrapper package.
- Ambient refinement: although Rockafellar states the theorem in `R^n`, the imported owner
  abstractions for proper separation, supporting hyperplanes, and relative interior already live
  on pairing spaces. This local bridge theorem therefore stays at the pairing owner layer rather
  than a real inner-product model.
-/

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 V} {C D : Set V}

/-- A hyperplane properly separates `D` and `C` exactly when it is a non-trivial supporting
hyperplane to `C` containing `D`, provided `D` is nonempty and `D ⊆ C`. -/
-- Proof sketch: if `H` is a non-trivial supporting hyperplane to `C` and `D ⊆ H`, then `C` lies
-- in one supporting closed half-space and `D` lies in the frontier hyperplane, hence in both
-- associated closed half-spaces, so `H` separates `D` and `C`; nontriviality gives properness.
-- Conversely, if `H` properly separates `D` and `C` and `D ⊆ C`, then every point of `D` must
-- lie in the intersection of the two opposite closed half-spaces, hence in `H` itself. Since
-- `D` is nonempty, this yields a contact point of `C` with `H`, so `H` is supporting, and
-- properness shows `C` is not contained in `H`.
theorem separatesProperly_iff_isNontrivialSupportingHyperplane_and_subset
    (hD_nonempty : D.Nonempty) (hDC : D ⊆ C) :
    (H separatesProperly[Y] D and C) ↔
      H.IsNontrivialSupportingHyperplane Y C ∧ D ⊆ H := sorry

end AffineSubspace

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

/-- Theorem 11.6: for a convex set `C` and a nonempty convex subset `D ⊆ C`, there exists a
non-trivial supporting hyperplane to `C` containing `D` if and only if `D` is disjoint from the
relative interior `ri[𝕜](C)`. -/
-- Proof sketch: use
-- `AffineSubspace.separatesProperly_iff_isNontrivialSupportingHyperplane_and_subset` to rewrite
-- the existence of a non-trivial supporting hyperplane containing `D` as the existence of a
-- proper separating hyperplane for `D` and `C`. Theorem 11.3 then shows this is equivalent to
-- disjointness of `ri[𝕜](D)` and `ri[𝕜](C)`. Finally, because `D ⊆ C`, Corollary 6.5.2 turns
-- that condition into `Disjoint D (ri[𝕜](C))`.
theorem exists_nontrivial_supporting_hyperplane_containing_iff_disjoint_intrinsicInterior
    {C D : Set V} (hC_conv : Convex 𝕜 C) (hD_conv : Convex 𝕜 D) (hD_nonempty : D.Nonempty)
    (hDC : D ⊆ C) :
    (∃ H : AffineSubspace 𝕜 V, H.IsNontrivialSupportingHyperplane Y C ∧ D ⊆ H) ↔
      Disjoint D (ri[𝕜](C)) := sorry

/-- A boundary point of a convex set lies on a non-trivial supporting hyperplane. -/
theorem exists_nontrivial_supporting_hyperplane_of_mem_rb
    {C : Set V} (hC_conv : Convex 𝕜 C) {x : V} (hx : x ∈ C)
    (hxbd : x ∈ rb[𝕜](C)) :
    ∃ H : AffineSubspace 𝕜 V, H.IsNontrivialSupportingHyperplane Y C ∧ x ∈ H := by
  have hx_not_ri : x ∉ ri[𝕜](C) := by
    rw [← intrinsicClosure_diff_intrinsicInterior] at hxbd
    exact hxbd.2
  have hdisj : Disjoint ({x} : Set V) (ri[𝕜](C)) := by
    simpa [Set.disjoint_singleton_left] using hx_not_ri
  rcases (exists_nontrivial_supporting_hyperplane_containing_iff_disjoint_intrinsicInterior
      (Y := Y) hC_conv (convex_singleton x) (Set.singleton_nonempty x)
      (Set.singleton_subset_iff.2 hx)).2
      hdisj with
    ⟨H, hH, hxH⟩
  exact ⟨H, hH, hxH (by simp)⟩

end
