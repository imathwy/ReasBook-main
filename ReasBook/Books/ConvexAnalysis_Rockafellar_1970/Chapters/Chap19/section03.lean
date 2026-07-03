import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_19_3_1 (from Chap04) -/
noncomputable section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 19.3.1 says that a linear image of a polyhedral convex function is
  again polyhedral convex, that the fiberwise infimum defining that image is attained whenever it
  is finite, and that precomposition with a linear map preserves polyhedral convexity.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.HasPolyhedralEpigraph` for function-side polyhedrality and `A ◁ f` for the
  textbook image function.
- `bridge/view`: the proof route passes through epigraph images and preimages together with the
  Chapter 2 bridge `Function.linearImageEpigraph_eq_epi_linearImage`.

Domain-style sampling used here:
- `Function.linearImage`;
- `Function.HasPolyhedralEpigraph`;
- `Set.IsPolyhedral.linear_image`;
- `Set.IsPolyhedral.linear_preimage`;
- `Function.linearImageEpigraph_eq_epi_linearImage`;
- `Function.linearImage_attains_of_closed_imageEpigraph_of_ne_bot_of_mem_dom`.

Primitive data vs derived API:
- primitive inputs: a linear map `A` and a function with polyhedral epigraph;
- derived API: polyhedrality of `A ◁ f`, attainment of the finite value `(A ◁ f) y`, and
  polyhedrality of `g ∘ A`.

Ambient refinement:
- the image clauses only use the set-side owners `Set.IsPolyhedral.linear_image` and
  `Set.IsPolyhedral.isClosed` on epigraphs, so their public assumptions reduce to finite-
  dimensional Hausdorff topological modules over an ordered scalar field, not inner-product
  spaces;
- the preimage clause only uses `Set.IsPolyhedral.linear_preimage`, so it lives on ordinary scalar
  modules with no topological or finite-dimensional hypotheses.

Layer target: `source-facing` owner lemmas for `Function.HasPolyhedralEpigraph`,
stated directly in the chapter owners `A ◁ f` and `g ∘ A`.
-/

section LinearImage

namespace Function.HasPolyhedralEpigraph

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E] [T2Space E]
variable {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F] [T2Space F]

private theorem linearImageEpigraph_isPolyhedral
    {f : E → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) (A : E →ₗ[𝕜] F) :
    (Function.linearImageEpigraph A f).IsPolyhedral 𝕜 := by
  rw [Function.linearImageEpigraph_eq_image_epi]
  simpa using
    Set.IsPolyhedral.linear_image hf (A.prodMap LinearMap.id)

private theorem linearImageEpigraph_isClosed
    {f : E → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) (A : E →ₗ[𝕜] F) :
    IsClosed (Function.linearImageEpigraph A f) :=
  (linearImageEpigraph_isPolyhedral hf A).isClosed_of_finiteDimensional

/-- Corollary 19.3.1 (1): if `f` has polyhedral epigraph, then its image function `A ◁ f`
under a linear map `A : E → F` again has polyhedral epigraph. The textbook `R^n → R^m`
statement is the finite-dimensional Euclidean specialization of this owner-level theorem. -/
theorem linearImage
    {f : E → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) (A : E →ₗ[𝕜] F) :
    (A ◁ f).HasPolyhedralEpigraph := by
  have hImage : (Function.linearImageEpigraph A f).IsPolyhedral 𝕜 :=
    linearImageEpigraph_isPolyhedral hf A
  have hImage_closed : IsClosed (Function.linearImageEpigraph A f) :=
    linearImageEpigraph_isClosed hf A
  change (epi (A ◁ f)).IsPolyhedral 𝕜
  simpa [Function.linearImageEpigraph_eq_epi_linearImage A f hImage_closed] using hImage

/-- Corollary 19.3.1 (2): whenever the value of `A ◁ f` at `y` is finite, the infimum defining
`(A ◁ f) y` is attained by some `x` with `A x = y`. -/
theorem linearImage_attains_of_ne_bot_of_mem_dom
    {f : E → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) (A : E →ₗ[𝕜] F) (y : F)
    (hy_dom : y ∈ dom (A ◁ f)) (hy_ne_bot : (A ◁ f) y ≠ ⊥) :
    ∃ x : E, A x = y ∧ f x = (A ◁ f) y := by
  have hImage_closed : IsClosed (Function.linearImageEpigraph A f) :=
    linearImageEpigraph_isClosed hf A
  exact
    Function.linearImage_attains_of_closed_imageEpigraph_of_ne_bot_of_mem_dom
      A f y hImage_closed hy_dom hy_ne_bot

end Function.HasPolyhedralEpigraph

end LinearImage

section LinearPreimage

namespace Function.HasPolyhedralEpigraph

variable {𝕜 : Type*} [Semiring 𝕜] [Preorder 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {F : Type*} [AddCommMonoid F] [Module 𝕜 F]

/-- Corollary 19.3.1 (3): if `g` has polyhedral epigraph, then the pullback `g ∘ A` along a
linear map `A : E → F` again has polyhedral epigraph. This preimage clause lives already on
the scalar-module owner layer, with no topological or finite-dimensional hypotheses. -/
theorem comp_linearMap
    {g : F → WithTopBot 𝕜} (hg : g.HasPolyhedralEpigraph) (A : E →ₗ[𝕜] F) :
    (g ∘ A).HasPolyhedralEpigraph := by
  change (epi (g ∘ A)).IsPolyhedral 𝕜
  simpa [epi_univ_eq_setOf_le, Function.comp, LinearMap.prodMap_apply] using
    Set.IsPolyhedral.linear_preimage hg (A.prodMap LinearMap.id)

end Function.HasPolyhedralEpigraph

end LinearPreimage

/-! ### Corollary_19_3_2 (from Chap04) -/
noncomputable section

open scoped Pointwise

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 19.3.2 says that the Minkowski sum of two polyhedral convex subsets
  of a finite-dimensional topological `𝕜`-module is again polyhedral.
- `core/canonical`: the owner abstraction is the pairing-parametric `Set.IsPolyhedral 𝕜 Y`,
  together with the canonical product-space owner `E × E`, the product theorem
  `Set.IsPolyhedral.prod`, and the image theorem `Set.IsPolyhedral.linear_image` from
  Theorem 19.3.
- `bridge/view`: the textbook sum is exactly Lean's pointwise-set addition. The pair-space points
  whose first and second coordinates lie in `C₁` and `C₂` form the product set `C₁ ×ˢ C₂`, and
  the addition map on that product owner has image `C₁ + C₂`.

Domain-style sampling used here:
- `Set.IsPolyhedral`;
- `Set.IsPolyhedral.prod`;
- `Set.IsPolyhedral.linear_image`;
- `LinearMap.fst`;
- `LinearMap.snd`;
- `Set.add_image_prod`.

Primitive data vs derived API:
- primitive inputs: the two polyhedral convex sets `C₁` and `C₂`;
- derived API: polyhedrality of their pointwise sum `C₁ + C₂`.

Layer target: `source-facing`, stated directly on the canonical owner `Set.IsPolyhedral`.
-/

namespace Set.IsPolyhedral

section Add

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable {Y : Type*} [HasPairing E Y 𝕜]

/-- Corollary 19.3.2: the Minkowski sum of two polyhedral convex sets is polyhedral. -/
theorem add {C₁ C₂ : Set E} (hC₁ : C₁.IsPolyhedral 𝕜 Y)
    (hC₂ : C₂.IsPolyhedral 𝕜 Y) : (C₁ + C₂).IsPolyhedral 𝕜 Y := by
  let addMap : E × E →ₗ[𝕜] E := LinearMap.fst 𝕜 E E + LinearMap.snd 𝕜 E E
  have hprod : (C₁ ×ˢ C₂).IsPolyhedral 𝕜 (Y × Y) := hC₁.prod hC₂
  simpa [Set.add_image_prod, addMap, LinearMap.add_apply] using hprod.linear_image addMap

/-- Corollary 19.3.2, difference form: the pointwise difference of two polyhedral convex sets is
polyhedral. -/
theorem sub {C₁ C₂ : Set E} (hC₁ : C₁.IsPolyhedral 𝕜 Y)
    (hC₂ : C₂.IsPolyhedral 𝕜 Y) : (C₁ - C₂).IsPolyhedral 𝕜 Y := by
  simpa [sub_eq_add_neg] using
    hC₁.add (hC₂.linear_image (LinearMap.lsmul 𝕜 E (-1 : 𝕜)))

end Add

end Set.IsPolyhedral

end

/-! ### Corollary_19_3_3 (from Chap04) -/
section

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 19.3.3 asserts that two nonempty disjoint polyhedral convex sets in
  a finite-dimensional normed space with a linear pairing into `Y` admit a strongly separating
  hyperplane.
- `core/canonical`: the owner predicates already available in the project are
  `Set.IsPolyhedral` for the two sets and the strong-separation owner
  `H stronglySeparates[Y] C1 and C2` for the separating hyperplane.
- Domain-style sampling used here: `Set.IsPolyhedral`, `Set.IsPolyhedral.sub`,
  `Set.IsPolyhedral.isClosed_hasFiniteFaces`,
  `AffineSubspace.StronglySeparates` / `stronglySeparates[Y]`, and
  `exists_hyperplane_strongly_separating_of_disjoint_convex_of_isClosed_sub`.
- Primitive data vs derived API: the polyhedrality and nonemptiness hypotheses on `C1`, `C2`
  are the source-facing inputs, while existence of a strongly separating hyperplane is theorem-
  level output. The nonemptiness assumptions are semantically essential here: the statement fails
  for `C1 = ∅` and `C2 = Set.univ`, even though both are polyhedral convex and disjoint.
- Layer target: `source-facing`, stated directly with the chapter owners for polyhedrality and
  strong separation.
- Ambient refinement: the proof uses only the generic owner APIs from Corollary 19.3.2 and
  Corollary 11.4.1, so the public theorem stays on the common ordered normed-
  field plus pairing-codomain layer rather than collapsing to a concrete self-pairing model.
  The explicit scalar assumptions are kept minimal here: `IsStrictOrderedRing` and
  `OrderTopology` are inferred from the remaining ambient layer and therefore are not exposed on
  the theorem surface.
-/

namespace Set.IsPolyhedral

/-- Corollary 19.3.3: if `C1` and `C2` are nonempty disjoint polyhedral convex sets in a
finite-dimensional normed pairing space over an ordered normed field `𝕜`,
then some hyperplane strongly separates `C1` and `C2`. -/
-- Proof sketch: polyhedrality is stable under linear images and Minkowski sums, so
-- `C1 - C2 = C1 + (-1) • C2` is polyhedral and hence closed. Then apply the Chapter 11
-- primitive bridge from disjointness, convexity, nonemptiness, and closed difference.
theorem exists_hyperplane_strongly_separating_of_disjoint_nonempty
    {C1 C2 : Set E} (hC1 : C1.IsPolyhedral 𝕜 Y) (hC1_nonempty : C1.Nonempty)
    (hC2 : C2.IsPolyhedral 𝕜 Y) (hC2_nonempty : C2.Nonempty)
    (hdisj : Disjoint C1 C2) :
    ∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2 := by
  have hsub_poly : (C1 - C2).IsPolyhedral 𝕜 Y := hC1.sub hC2
  have hsub_closed : IsClosed (C1 - C2) := hsub_poly.isClosed_hasFiniteFaces.1
  exact
    exists_hyperplane_strongly_separating_of_disjoint_convex_of_isClosed_sub
      hC1_nonempty hC1.convex hC2_nonempty hC2.convex hdisj hsub_closed

end Set.IsPolyhedral

end

/-! ### Theorem_19_3 (from Chap04) -/
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

/-! ### Corollary_19_3_4 (from Chap04) -/
noncomputable section

section PairSumPrimitive

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

variable {f₁ f₂ : E → WithTopBot 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 19.3.4 states that the infimal convolution of two proper polyhedral
  convex functions on `R^n` is again polyhedral convex, and that when this infimal convolution is
  proper its defining infimum is attained pointwise.
- `core/canonical`: the existing owner declarations are `infimal_convolution`,
  `Function.linearImage` and `Function.HasPolyhedralEpigraph` at
  codomain `WithTopBot 𝕜`.
- `bridge/view`: the textbook infimal convolution is the linear image of the pair-space sum
  `(u, v) ↦ f₁ u + f₂ v` on the intrinsic product space `E × E` under the canonical addition map
  `(u, v) ↦ u + v`. The attainment clause is then the owner-side linear-image attainment theorem,
  rewritten in the textbook variable order `f₁ (x - y) + f₂ y`.

Domain-style sampling used here:
- `infimal_convolution`;
- `Function.linearImage`;
- `infimal_convolution_eq_sInf_decompositions`;
- `Function.HasPolyhedralEpigraph.comp_linearMap`;
- `Function.HasPolyhedralEpigraph`;
- `Function.HasPolyhedralEpigraph.add_of_ne_bot`.

Primitive data vs derived API:
- primitive owner inputs: the two functions `f₁`, `f₂`;
- source hypotheses: each input has polyhedral epigraph and never takes the value `⊥`; the
  separate textbook convexity adjective is not kept as primitive data because the Chapter 19 owner
  `Function.HasPolyhedralEpigraph` already encodes the relevant epigraph-side convexity;
- derived API: the pair-space sum function on `E × E`, the linear-image
  identification of `f₁ □ f₂`, polyhedrality of `f₁ □ f₂`, and its pointwise attainment under the
  primitive output-side assumption that `f₁ □ f₂` never takes `⊥`.

Layer target: `source-facing`, expressed directly with the Chapter 19 owners
`Function.HasPolyhedralEpigraph` and `infimal_convolution` on an arbitrary finite-dimensional
Hausdorff topological module over an ordered topological field. The textbook
`R^n`
formulation is recovered by specialization, and the pair-space `Function.linearImage`
presentation is kept internal as the canonical bridge via the intrinsic product owner rather than
through Euclidean coordinates.
-/

/-- Pulling back along the two product-coordinate projections and then adding gives the pair-space
sum function `(u, v) ↦ f₁ u + f₂ v` a polyhedral epigraph. -/
private theorem hasPolyhedralEpigraph_pairSum
    (hf₁ : f₁.HasPolyhedralEpigraph)
    (hf₁_ne_bot : ∀ x : E, f₁ x ≠ ⊥)
    (hf₂ : f₂.HasPolyhedralEpigraph)
    (hf₂_ne_bot : ∀ x : E, f₂ x ≠ ⊥) :
    (fun p : E × E ↦ f₁ p.1 + f₂ p.2).HasPolyhedralEpigraph := by
  have hfst : (fun p : E × E ↦ f₁ p.1).HasPolyhedralEpigraph := by
    simpa [Function.comp] using hf₁.comp_linearMap (LinearMap.fst 𝕜 E E)
  have hsnd : (fun p : E × E ↦ f₂ p.2).HasPolyhedralEpigraph := by
    simpa [Function.comp] using hf₂.comp_linearMap (LinearMap.snd 𝕜 E E)
  exact
    Function.HasPolyhedralEpigraph.add_of_ne_bot hfst hsnd
      (fun p ↦ hf₁_ne_bot p.1)
      (fun p ↦ hf₂_ne_bot p.2)

end PairSumPrimitive

section Main

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E] [T2Space E]

variable {f₁ f₂ : E → WithTopBot 𝕜}

namespace Function.HasPolyhedralEpigraph

-- Proof sketch: pull `f₁` and `f₂` back along the two product-coordinate projections on
-- `E × E`, use `Function.HasPolyhedralEpigraph.add_of_ne_bot` on those pullbacks to show that the
-- pair-space sum has polyhedral epigraph, and then apply Corollary 19.3.1 (1) to the
-- addition map `(u, v) ↦ u + v`.
/-- The infimal convolution of two functions with polyhedral epigraphs and no `⊥` values
again has polyhedral epigraph. -/
theorem infimal_convolution
    (hf₁ : f₁.HasPolyhedralEpigraph)
    (hf₁_ne_bot : ∀ x : E, f₁ x ≠ ⊥)
    (hf₂ : f₂.HasPolyhedralEpigraph)
    (hf₂_ne_bot : ∀ x : E, f₂ x ≠ ⊥) :
    (f₁ □ f₂).HasPolyhedralEpigraph := by
  let A : E × E →ₗ[𝕜] E := LinearMap.fst 𝕜 E E + LinearMap.snd 𝕜 E E
  have hpair :
      (fun p : E × E ↦ f₁ p.1 + f₂ p.2).HasPolyhedralEpigraph :=
    hasPolyhedralEpigraph_pairSum hf₁ hf₁_ne_bot hf₂ hf₂_ne_bot
  exact Function.HasPolyhedralEpigraph.linearImage hpair A

-- Proof sketch: apply Corollary 19.3.1 (2) to the pair-space sum function under the addition
-- map `(u, v) ↦ u + v`. The output-side hypothesis `∀ x, (f₁ □ f₂) x ≠ ⊥` rules out the value
-- `⊥`; when
-- `(f₁ □ f₂) x = ⊤`, the decomposition `(x, 0)` already forces the value `f₁ x + f₂ 0` to be
-- `⊤`, so the infimum is attained trivially. Otherwise Corollary 19.3.1 (2) gives a minimizing
-- decomposition in pair form.
/-- If `f₁` and `f₂` have polyhedral epigraphs and no `⊥` values, and if `(f₁ □ f₂)` is nowhere
`⊥`, then for each `x` there is an attained minimizing decomposition in intrinsic pair form. -/
theorem exists_pair_eq_infimal_convolution_of_ne_bot
    (hf₁ : f₁.HasPolyhedralEpigraph)
    (hf₁_ne_bot : ∀ x : E, f₁ x ≠ ⊥)
    (hf₂ : f₂.HasPolyhedralEpigraph)
    (hf₂_ne_bot : ∀ x : E, f₂ x ≠ ⊥)
    (hconv_ne_bot : ∀ x : E, (f₁ □ f₂) x ≠ ⊥) :
    ∀ x : E, ∃ p : E × E, p.1 + p.2 = x ∧ (f₁ □ f₂) x = f₁ p.1 + f₂ p.2 := by
  let A : E × E →ₗ[𝕜] E := LinearMap.fst 𝕜 E E + LinearMap.snd 𝕜 E E
  have hpair :
      (fun p : E × E ↦ f₁ p.1 + f₂ p.2).HasPolyhedralEpigraph :=
    hasPolyhedralEpigraph_pairSum hf₁ hf₁_ne_bot hf₂ hf₂_ne_bot
  intro x
  by_cases htop : (f₁ □ f₂) x = ⊤
  · refine ⟨(x, 0), by simp, ?_⟩
    have hx_le : (f₁ □ f₂) x ≤ f₁ x + f₂ 0 := by
      rw [infimal_convolution_eq_sInf_decompositions]
      exact sInf_le ⟨(x, 0), by simp, rfl⟩
    have htop_le_sum : (⊤ : WithTopBot 𝕜) ≤ f₁ x + f₂ 0 := by
      exact htop ▸ hx_le
    have hsum_top : f₁ x + f₂ 0 = ⊤ := by
      exact top_le_iff.mp htop_le_sum
    simpa [htop, hsum_top]
  · have hfinite : ⊥ < (f₁ □ f₂) x ∧ (f₁ □ f₂) x < ⊤ := by
      exact ⟨WithTopBot.bot_lt_iff_ne_bot.mpr (hconv_ne_bot x), lt_of_le_of_ne le_top htop⟩
    have hlinear_dom :
        x ∈ dom(Function.linearImage A (fun p : E × E ↦ f₁ p.1 + f₂ p.2)) := by
      change (f₁ □ f₂) x < ⊤
      exact hfinite.2
    have hlinear_ne_bot :
        Function.linearImage A (fun p : E × E ↦ f₁ p.1 + f₂ p.2) x ≠ ⊥ := by
      change (f₁ □ f₂) x ≠ ⊥
      exact ne_of_gt hfinite.1
    rcases
      Function.HasPolyhedralEpigraph.linearImage_attains_of_ne_bot_of_mem_dom
        hpair A x hlinear_dom hlinear_ne_bot with ⟨p, hp, hpval⟩
    have hsum : p.1 + p.2 = x := by
      simpa [A, LinearMap.add_apply] using hp
    have hvalue : (f₁ □ f₂) x = f₁ p.1 + f₂ p.2 := by
      change Function.linearImage A (fun p : E × E ↦ f₁ p.1 + f₂ p.2) x = f₁ p.1 + f₂ p.2
      exact hpval.symm
    exact ⟨p, hsum, hvalue⟩

/-- Bridge form of attainment in the textbook variable order `f₁ (x - y) + f₂ y`. -/
theorem exists_argmin_infimal_convolution_of_ne_bot
    (hf₁ : f₁.HasPolyhedralEpigraph)
    (hf₁_ne_bot : ∀ x : E, f₁ x ≠ ⊥)
    (hf₂ : f₂.HasPolyhedralEpigraph)
    (hf₂_ne_bot : ∀ x : E, f₂ x ≠ ⊥)
    (hconv_ne_bot : ∀ x : E, (f₁ □ f₂) x ≠ ⊥) :
    ∀ x : E, ∃ y : E, (f₁ □ f₂) x = f₁ (x - y) + f₂ y := by
  intro x
  rcases
    hf₁.exists_pair_eq_infimal_convolution_of_ne_bot
      hf₁_ne_bot hf₂ hf₂_ne_bot hconv_ne_bot x with
    ⟨p, hp_sum, hp_value⟩
  refine ⟨p.2, ?_⟩
  have hp₁ : x - p.2 = p.1 := by
    rw [sub_eq_iff_eq_add]
    simpa [add_comm, add_left_comm, add_assoc] using hp_sum.symm
  simpa [hp₁] using hp_value

end Function.HasPolyhedralEpigraph

/-- Corollary 19.3.4: if `f₁` and `f₂` have polyhedral epigraphs and never take the value
`⊥`, then their infimal convolution `f₁ □ f₂` has polyhedral epigraph; moreover, if
`f₁ □ f₂` is nowhere `⊥`, then for each `x` the infimum in the definition of `(f₁ □ f₂) x` is
attained. This keeps the attainment side on primitive codomain data rather than a stronger derived
owner. -/
theorem polyhedral_infimalConvolution_and_attainment_of_hasPolyhedralEpigraph
    (hf₁_poly : f₁.HasPolyhedralEpigraph)
    (hf₁_ne_bot : ∀ x : E, f₁ x ≠ ⊥)
    (hf₂_poly : f₂.HasPolyhedralEpigraph)
    (hf₂_ne_bot : ∀ x : E, f₂ x ≠ ⊥) :
    (f₁ □ f₂).HasPolyhedralEpigraph ∧
      ((∀ x : E, (f₁ □ f₂) x ≠ ⊥) →
        ∀ x : E, ∃ y : E, (f₁ □ f₂) x = f₁ (x - y) + f₂ y) := by
  constructor
  · exact hf₁_poly.infimal_convolution hf₁_ne_bot hf₂_poly hf₂_ne_bot
  · intro hconv_ne_bot x
    exact
      hf₁_poly.exists_argmin_infimal_convolution_of_ne_bot
        hf₁_ne_bot hf₂_poly hf₂_ne_bot hconv_ne_bot x

end Main
