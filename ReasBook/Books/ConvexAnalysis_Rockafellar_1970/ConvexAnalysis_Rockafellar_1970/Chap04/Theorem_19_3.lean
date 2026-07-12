import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 19.3 says that linear images and inverse images of polyhedral convex
  sets are again polyhedral convex.
- `core/canonical`: the owner predicate is `Set.IsPolyhedral` on subsets, together with the
  standard set image and preimage operations `A '' C` and `A ⁻¹' D`.
- `bridge/view`: Rockafellar's notations `AC` and `A⁻¹D` are exactly Lean's canonical image and
  preimage under the linear map `A`.
- Domain-style sampling used here: the chapter owner `Set.IsPolyhedral`, the coordinate-free
  finite-generation bridge `Set.IsPolyhedral.isFinitelyGeneratedConvex` from Theorem 19.1,
  its converse `Set.IsFinitelyGeneratedConvex.isPolyhedral`, and the canonical convex-set
  transport lemmas `Convex.linear_image` and `Convex.linear_preimage`.
- Primitive data vs derived API: the primitive inputs are the linear map `A` and the sets `C` and
  `D`; polyhedrality of the image and preimage is theorem-level content.
- Layer target: `source-facing`, stated directly in the canonical image/preimage API.
- Ambient refinement: `Set.IsFinitelyGeneratedConvex` and `Set.IsPolyhedral` themselves live on
  scalar-generic module data. Theorem 19.3(2) is therefore stated directly at that primitive owner
  layer. For part (1), the auxiliary owner theorem is the scalar-generic image theorem on
  `Set.IsFinitelyGeneratedConvex`; Theorem 19.1 then upgrades that result back to
  `Set.IsPolyhedral` in the finite-dimensional Hausdorff topological-module ambient where the
  chapter-level polyhedral/finitely-generated equivalence is available.
-/

namespace Set.IsFinitelyGeneratedConvex

variable {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {F : Type*} [AddCommMonoid F] [Module 𝕜 F]

private theorem sameRay_exists_nonneg_right {x y : F} (h : SameRay 𝕜 x y)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ r : 𝕜, 0 ≤ r ∧ x = r • y := by
  rcases h.exists_pos hx hy with ⟨r₁, r₂, hr₁, hr₂, hxy⟩
  refine ⟨r₁⁻¹ * r₂, mul_nonneg (inv_nonneg.mpr hr₁.le) hr₂.le, ?_⟩
  calc
    x = r₁⁻¹ • (r₁ • x) := by rw [inv_smul_smul₀ hr₁.ne']
    _ = r₁⁻¹ • (r₂ • y) := by rw [hxy]
    _ = (r₁⁻¹ * r₂) • y := by rw [mul_smul]

/-- The image of a finitely generated convex set under a linear map is finitely generated. -/
-- Proof sketch: unpack a mixed-hull presentation of `C` by finitely many generating points and
-- directions. Applying the linear map to the point generators and to the nonzero image directions
-- gives a new finite mixed-hull presentation of `A '' C`.
theorem linear_image {C : Set E} (hC : C.IsFinitelyGeneratedConvex 𝕜) (A : E →ₗ[𝕜] F) :
    (A '' C).IsFinitelyGeneratedConvex 𝕜 := by
  classical
  rcases hC with ⟨points, directions, hpoints_finite, hdirections_finite, rfl⟩
  let C0 : Set E := mixedConvexHull 𝕜 points (ray directions)
  let D0 : Set (Module.Ray 𝕜 E) := {d | d ∈ directions ∧ A d.someVector ≠ 0}
  have hD0_finite : D0.Finite :=
    hdirections_finite.subset (by intro d hd; exact hd.1)
  let directions' : Set (Module.Ray 𝕜 F) :=
    (fun d : D0 ↦ rayOfNeZero 𝕜 (A d.1.someVector) d.2.2) '' Set.univ
  have hdirections'_finite : directions'.Finite := by
    letI : Fintype D0 := hD0_finite.fintype
    exact (Set.toFinite (Set.univ : Set D0)).image _
  let C1 : Set F := mixedConvexHull 𝕜 (A '' points) (ray directions')
  have hC0_sub_preimage : C0 ⊆ A ⁻¹' C1 := by
    refine mixedConvexHull_min 𝕜 ?_ ?_ ?_
    · exact (convex_mixedConvexHull 𝕜 (A '' points) (ray directions')).linear_preimage A
    · intro x hx
      exact subset_mixedConvexHull 𝕜 (A '' points) (ray directions') ⟨x, hx, rfl⟩
    · intro y hy
      rw [Set.mem_recessionCone_iff]
      intro x hx a ha
      change A (x + a • y) ∈ C1
      have hAy_recession : A y ∈ 0⁺[𝕜] C1 := by
        by_cases hAy0 : A y = 0
        · rw [Set.mem_recessionCone_iff]
          intro x hx a ha
          simpa [hAy0]
        · rcases (mem_ray_iff directions y).1 hy with rfl | ⟨hy0, hyd⟩
          · exact (hAy0 (by simp)).elim
          · let d : Module.Ray 𝕜 E := rayOfNeZero 𝕜 y hy0
            have hy_eq_d : rayOfNeZero 𝕜 y hy0 = d := rfl
            have hsame : SameRay 𝕜 y d.someVector := by
              refine (ray_eq_iff hy0 d.someVector_ne_zero).1 ?_
              simp [d]
            have hdA0 : A d.someVector ≠ 0 := by
              intro hdA0
              rcases sameRay_exists_nonneg_right hsame hy0 d.someVector_ne_zero with
                ⟨r, hr, hyr⟩
              apply hAy0
              calc
                A y = A (r • d.someVector) := by
                  simp [hyr]
                _ = r • A d.someVector := by simp
                _ = 0 := by simp [hdA0]
            have hd_mem : d ∈ D0 := by
              refine ⟨?_, hdA0⟩
              simpa [hy_eq_d] using hyd
            have hdir_mem : rayOfNeZero 𝕜 (A d.someVector) hdA0 ∈ directions' := by
              refine ⟨⟨d, hd_mem⟩, by simp, ?_⟩
              simp
            have hsameA : SameRay 𝕜 (A y) (A d.someVector) := hsame.map A
            have hrayAy :
                rayOfNeZero 𝕜 (A y) hAy0 = rayOfNeZero 𝕜 (A d.someVector) hdA0 :=
              (ray_eq_iff hAy0 hdA0).2 hsameA
            have hAy_mem_ray : A y ∈ ray directions' :=
              (mem_ray_iff directions' (A y)).2
                (Or.inr ⟨hAy0, by simpa [hrayAy] using hdir_mem⟩)
            exact directions_subset_recessionCone_mixedConvexHull 𝕜 (A '' points)
              (ray directions') hAy_mem_ray
      have h := (Set.mem_recessionCone_iff.mp hAy_recession) (A x) hx a ha
      simpa [map_add, map_smul] using h
  have himage_subset : A '' C0 ⊆ C1 := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact hC0_sub_preimage hx
  have hC1_subset : C1 ⊆ A '' C0 := by
    refine mixedConvexHull_min 𝕜 ?_ ?_ ?_
    · exact (convex_mixedConvexHull 𝕜 points (ray directions)).linear_image A
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, subset_mixedConvexHull 𝕜 points (ray directions) hx, rfl⟩
    · intro z hz
      rw [Set.mem_recessionCone_iff]
      intro x hx a ha
      rcases hx with ⟨x0, hx0, rfl⟩
      rcases (mem_ray_iff directions' z).1 hz with rfl | ⟨hz0, hzr⟩
      · exact ⟨x0, hx0, by simp⟩
      · rcases hzr with ⟨d, -, hdeq⟩
        have hsame : SameRay 𝕜 z (A d.1.someVector) := by
          exact ((ray_eq_iff d.2.2 hz0).1 hdeq).symm
        rcases sameRay_exists_nonneg_right hsame hz0 d.2.2 with ⟨r, hr, rfl⟩
        have hd_ray : d.1.someVector ∈ ray directions := by
          refine (mem_ray_iff directions d.1.someVector).2 (Or.inr ?_)
          refine ⟨d.1.someVector_ne_zero, ?_⟩
          simpa using d.2.1
        have hd_rec_C0 : d.1.someVector ∈ 0⁺[𝕜] C0 :=
          directions_subset_recessionCone_mixedConvexHull 𝕜 points (ray directions) hd_ray
        have hAd_rec_image : A d.1.someVector ∈ 0⁺[𝕜] (A '' C0) := by
          rw [Set.mem_recessionCone_iff]
          intro u hu b hb
          rcases hu with ⟨u0, hu0, rfl⟩
          refine ⟨u0 + b • d.1.someVector, ?_, by simp [map_add, map_smul]⟩
          exact (Set.mem_recessionCone_iff.mp hd_rec_C0) u0 hu0 b hb
        have hrAd_rec_image : r • A d.1.someVector ∈ 0⁺[𝕜] (A '' C0) := by
          rw [Set.mem_recessionCone_iff] at hAd_rec_image ⊢
          intro u hu b hb
          have hu' := hAd_rec_image u hu (b * r) (mul_nonneg hb hr)
          simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using hu'
        exact (Set.mem_recessionCone_iff.mp hrAd_rec_image) (A x0) ⟨x0, hx0, rfl⟩ a ha
  refine ⟨A '' points, directions', hpoints_finite.image A, hdirections'_finite, ?_⟩
  exact Set.Subset.antisymm himage_subset hC1_subset

end Set.IsFinitelyGeneratedConvex

namespace Set.IsFinitelyGeneratedConvex

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F]

/-- In finite-dimensional topological `𝕜`-modules, a linear image of a finitely
generated convex set is polyhedral. -/
theorem linear_image_isPolyhedral {C : Set E}
    (hC : C.IsFinitelyGeneratedConvex 𝕜) (A : E →ₗ[𝕜] F) :
    (A '' C).IsPolyhedral 𝕜 := by
  exact (hC.linear_image A).isPolyhedral

end Set.IsFinitelyGeneratedConvex

namespace Set.IsPolyhedral

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F]

section ImageFiniteDimensional

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Theorem 19.3 (1): the image of a polyhedral convex set under a linear map between
finite-dimensional topological modules is polyhedral convex. -/
-- Proof sketch: use Theorem 19.1 to rewrite `C` as a finitely generated convex set. Applying `A`
-- to the finitely many generating points and directions gives a finite generating family for
-- `A '' C`, so Theorem 19.1 yields that the image is polyhedral convex.
theorem linear_image {C : Set E} (hC : C.IsPolyhedral 𝕜)
    (A : E →ₗ[𝕜] F) : (A '' C).IsPolyhedral 𝕜 := by
  exact hC.isFinitelyGeneratedConvex.linear_image_isPolyhedral A

end ImageFiniteDimensional

section Preimage

variable {𝕜 : Type*} [Semiring 𝕜] [Preorder 𝕜]
variable {E F : Type*} [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]

/-- Theorem 19.3 (2): the inverse image of a polyhedral convex set under a linear map is
polyhedral convex. -/
-- Proof sketch: choose a finite linear-inequality presentation of `D`. Pulling each defining weak
-- inequality back along `A` just precomposes the defining linear functional with `A`, so `A ⁻¹' D`
-- is again a finite intersection of closed half-spaces.
theorem linear_preimage {D : Set F} (hD : D.IsPolyhedral 𝕜) (A : E →ₗ[𝕜] F) :
    (A ⁻¹' D).IsPolyhedral 𝕜 := by
  classical
  rcases hD with ⟨S, rfl⟩
  refine ⟨S.image fun y ↦ ((y.1).comp A, y.2), ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_iInter]
  constructor
  · intro hx z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    exact hx y hy
  · intro hx y hy
    have hz : ((y.1).comp A, y.2) ∈
        S.image (fun z ↦ ((z.1).comp A, z.2)) :=
      Finset.mem_image.mpr ⟨y, hy, rfl⟩
    exact hx ((y.1).comp A, y.2) hz

/-- Product owner companion to Theorem 19.3: the Cartesian product of two polyhedral sets is
polyhedral. -/
theorem prod {C : Set E} {D : Set F} (hC : C.IsPolyhedral 𝕜) (hD : D.IsPolyhedral 𝕜) :
    (C ×ˢ D).IsPolyhedral 𝕜 := by
  have hfst : (LinearMap.fst 𝕜 E F ⁻¹' C).IsPolyhedral 𝕜 :=
    hC.linear_preimage (LinearMap.fst 𝕜 E F)
  have hsnd : (LinearMap.snd 𝕜 E F ⁻¹' D).IsPolyhedral 𝕜 :=
    hD.linear_preimage (LinearMap.snd 𝕜 E F)
  simpa using Set.IsPolyhedral.inter (𝕜 := 𝕜) hfst hsnd

end Preimage

end Set.IsPolyhedral

end
