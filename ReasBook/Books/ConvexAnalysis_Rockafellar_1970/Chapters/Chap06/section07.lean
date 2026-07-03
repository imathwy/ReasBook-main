import Mathlib.Analysis.Normed.Module.FiniteDimension

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_6_7 (from Chap02) -/
open Metric
open scoped Pointwise Rockafellar

/-- Membership in the interior of a subset of a pseudo-metric space is equivalent to containing a
positive-radius closed ball around the point. -/
theorem Metric.mem_interior_iff_exists_pos_closedBall_subset
    {P : Type*} [PseudoMetricSpace P] {C : Set P} {x : P} :
    x ∈ interior C ↔ ∃ ε : ℝ, 0 < ε ∧ closedBall x ε ⊆ C := by
  rw [mem_interior_iff_mem_nhds, Metric.nhds_basis_closedBall.mem_iff]

-- Proof sketch: start from the canonical owner theorem
-- `Metric.closure_eq_iInter_thickening`, rewrite each thickening as the existential witness set
-- `{x | ∃ y ∈ C, dist x y < ε}` via `Metric.mem_thickening_iff`, and then pass from `< ε` to
-- `≤ ε` inside the intersection using the standard halving argument.
theorem Metric.closure_eq_iInter_points_within_distance_le
    {P : Type*} [PseudoMetricSpace P] (C : Set P) :
    closure C = ⋂ (ε : ℝ) (_ : 0 < ε), {x : P | ∃ y ∈ C, dist x y ≤ ε} := by
  rw [Set.ext_iff]
  intro x
  rw [Metric.closure_eq_iInter_thickening]
  simp only [Set.mem_iInter, Metric.mem_thickening_iff]
  constructor
  · intro hx ε hε
    rcases hx ε hε with ⟨y, hyC, hxy⟩
    exact ⟨y, hyC, hxy.le⟩
  · intro hx ε hε
    rcases hx (ε / 2) (half_pos hε) with ⟨y, hyC, hxy⟩
    exact ⟨y, hyC, hxy.trans_lt (half_lt_self hε)⟩

section

variable {E : Type*} [PseudoMetricSpace E] [AddGroup E] [IsIsometricVAdd E E]

/-- Intrinsic Text 6.7 (1): the closure of a subset is the intersection of all translates
`C + closedBall 0 ε` with `ε > 0`. -/
theorem closure_eq_iInter_add_closedBall_zero (C : Set E) :
    closure C = ⋂ (ε : ℝ) (_ : 0 < ε), C + closedBall (0 : E) ε := by
  rw [Metric.closure_eq_iInter_points_within_distance_le]
  ext x
  simp only [Set.mem_iInter]
  constructor <;> intro hx ε hε <;>
    simpa [← points_within_distance_le_eq_add_closedBall_zero (C := C) (ε := ε)] using
      hx ε hε

/-- Intrinsic Text 6.7 (2): a point lies in the interior of `C` iff some positive-radius translate
`{x} + closedBall 0 ε` is contained in `C`. -/
theorem mem_interior_iff_exists_pos_add_closedBall_zero_subset {C : Set E} {x : E} :
    x ∈ interior C ↔ ∃ ε : ℝ, 0 < ε ∧ {x} + closedBall (0 : E) ε ⊆ C := by
  rw [Metric.mem_interior_iff_exists_pos_closedBall_subset]
  constructor <;> rintro ⟨ε, hε, hεC⟩ <;> refine ⟨ε, hε, ?_⟩
  · have hEq : {x} + closedBall (0 : E) ε = closedBall x ε := by
      simpa [← vadd_eq_add, Set.singleton_vadd] using
        (closedBall_eq_vadd_closedBall_zero (a := x) (ε := ε)).symm
    exact hEq.symm ▸ hεC
  · have hEq : {x} + closedBall (0 : E) ε = closedBall x ε := by
      simpa [← vadd_eq_add, Set.singleton_vadd] using
        (closedBall_eq_vadd_closedBall_zero (a := x) (ε := ε)).symm
    exact hEq ▸ hεC

/-- Intrinsic Text 6.7 (2): interior as the set of points admitting a positive-radius translate
`{x} + closedBall 0 ε` inside `C`. -/
theorem interior_eq_setOf_exists_add_closedBall_zero_subset (C : Set E) :
    interior C = {x : E | ∃ ε : ℝ, 0 < ε ∧ {x} + closedBall (0 : E) ε ⊆ C} := by
  ext x
  simpa using
    (mem_interior_iff_exists_pos_add_closedBall_zero_subset (C := C) (x := x))

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Text 6.7 gives formulas for the closure and interior of a subset, written
  through the closed unit ball `B`.
- `core/canonical`: this file first records the intrinsic owner layer using translates
  `C + closedBall 0 ε` and `{x} + closedBall 0 ε`.
- `bridge/view`: this section rewrites those intrinsic owners into the scalar-generic textbook view
  `C + c • B` and `{x} + c • B`, with primitive nonzero scalar witnesses `c ≠ 0`.
- Primitive data vs derived API: this item introduces no new data, only source-facing
  reformulations of the existing topological operators.
- Domain-style sampling used here: `points_within_distance_le_eq_iUnion_closedBall`,
  `closedBall_eq_add_smul_unitClosedBall_of_ne_zero`, `mem_closure_iff`,
  `nhds_basis_closedBall.mem_iff`, and mathlib's `Metric.closure_eq_iInter_cthickening`, sampled
  as the canonical closure owner but not adopted because the source-facing formula keeps the
  explicit Minkowski-sum neighborhoods.
- Layer target: both declarations are `source-facing` bridge theorems on the owner operators
  `closure` and `interior`.
- Ambient-space refinement: the formulas only use seminormed additive structure together with the
  scalar action assumptions needed for `c • B`, so the public API is stated at that owner level
  rather than concrete finite-coordinate Euclidean models.
-/

/-- Text 6.7 (1): the closure of a subset is the intersection of all sets
`C + c • B` with primitive nonzero radius witness `c ≠ 0`,
where `B` is the closed unit ball centered at the origin. -/
theorem closure_eq_iInter_add_smul_B (C : Set E) :
    closure C = ⋂ (c : 𝕜) (_ : c ≠ 0), C + c • B := by
  rw [closure_eq_iInter_add_closedBall_zero (C := C)]
  ext x
  simp only [Set.mem_iInter]
  constructor
  · intro hx c hc
    have h0 : closedBall (0 : E) ‖c‖ = c • B := by
      simpa using
        (closedBall_eq_add_smul_unitClosedBall_of_ne_zero
          (a := (0 : E)) (c := c) hc)
    have hcNorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
    simpa [h0] using hx ‖c‖ hcNorm
  · intro hx ε hε
    obtain ⟨c, hc, hcε⟩ := NormedField.exists_norm_lt 𝕜 hε
    have hc0 : c ≠ 0 := norm_pos_iff.mp hc
    have h0 : closedBall (0 : E) ‖c‖ = c • B := by
      simpa using
        (closedBall_eq_add_smul_unitClosedBall_of_ne_zero (a := (0 : E)) (c := c) hc0)
    have hx' : x ∈ C + c • B := by
      exact hx c hc0
    have hx'' : x ∈ C + closedBall (0 : E) ‖c‖ := by
      simpa [h0] using hx'
    have hsubset_ball : closedBall (0 : E) ‖c‖ ⊆ closedBall (0 : E) ε := by
      intro y hy
      exact Metric.mem_closedBall.2 ((Metric.mem_closedBall.1 hy).trans hcε.le)
    exact (Set.add_subset_add subset_rfl hsubset_ball) hx''

/-- Text 6.7 (2): the interior of a subset consists of the points `x` for which some translate
`x + c • B` with primitive nonzero witness `c ≠ 0` is contained in `C`, where `B` is the closed unit
ball. -/
theorem mem_interior_iff_exists_add_smul_B_subset {C : Set E} {x : E} :
    x ∈ interior C ↔ ∃ c : 𝕜, c ≠ 0 ∧ {x} + c • B ⊆ C := by
  rw [mem_interior_iff_exists_pos_add_closedBall_zero_subset]
  constructor
  · rintro ⟨ε, hε, hεC⟩
    obtain ⟨c, hc, hcε⟩ := NormedField.exists_norm_lt 𝕜 hε
    have hc0 : c ≠ 0 := norm_pos_iff.mp hc
    have h0 : closedBall (0 : E) ‖c‖ = c • B := by
      simpa using
        (closedBall_eq_add_smul_unitClosedBall_of_ne_zero (a := (0 : E)) (c := c) hc0)
    have hsubset_ball : c • (B : Set E) ⊆ closedBall (0 : E) ε := by
      intro y hy
      have hy' : y ∈ closedBall (0 : E) ‖c‖ := by simpa [h0] using hy
      exact Metric.mem_closedBall.2 ((Metric.mem_closedBall.1 hy').trans hcε.le)
    have hsubset : {x} + c • B ⊆ C :=
      (Set.add_subset_add subset_rfl hsubset_ball).trans hεC
    exact ⟨c, hc0, hsubset⟩
  · rintro ⟨c, hc0, hcC⟩
    refine ⟨‖c‖, norm_pos_iff.mpr hc0, ?_⟩
    have h0 : closedBall (0 : E) ‖c‖ = c • B := by
      simpa using
        (closedBall_eq_add_smul_unitClosedBall_of_ne_zero
          (a := (0 : E)) (c := c) hc0)
    have hεx : ({x} : Set E) + closedBall (0 : E) ‖c‖ = {x} + c • B :=
      congrArg (fun s : Set E => ({x} : Set E) + s) h0
    exact hεx ▸ hcC

/-- Text 6.7 (2): the interior of a subset consists of the points `x` for which some translate
`x + c • B` with primitive nonzero witness `c ≠ 0` is contained in `C`, where `B` is the closed unit
ball. -/
theorem interior_eq_setOf_exists_add_smul_B_subset (C : Set E) :
    interior C = {x : E | ∃ c : 𝕜, c ≠ 0 ∧ {x} + c • B ⊆ C} := by
  ext x
  simpa using
    (mem_interior_iff_exists_add_smul_B_subset (C := C) (x := x))

end

/-! ### Theorem_6_7 (from Chap02) -/
section

/-
Source/core/bridge triage:
- `source-facing`: Theorem 6.7 states that inverse images of convex sets under a linear map
  preserve relative interior and intrinsic closure, provided the inverse image of the relative
  interior is nonempty. The ordinary-closure clause is a finite-dimensional bridge corollary.
- `core/canonical`: the owner abstractions are `Convex 𝕜`, `intrinsicInterior 𝕜`,
  `intrinsicClosure 𝕜`, `closure`,
  `Set.preimage`, the affine-section owner theorems on `AffineSubspace`, and the linear-image
  owner theorem `Convex.intrinsicInterior_linear_image`.
- `bridge/view`: Rockafellar's `ri C` is represented by `intrinsicInterior 𝕜 C`, the textbook
  inverse image `A⁻¹ C` is `A ⁻¹' C`, and the graph section is expressed canonically by the graph
  submodule `LinearMap.graph A` viewed as an affine subspace.
- Domain-style sampling used here: `AffineSubspace.intrinsicInterior_inter_eq`,
  `AffineSubspace.intrinsicClosure_inter_eq`, `Convex.intrinsicInterior_linear_image`,
  `AffineEquiv.image_intrinsicClosure`, `ri_prod_eq`, and
  `intrinsicClosure_prod_eq`.
- Primitive data vs derived API: the primitive owner data is only the convexity proof `hC` and the
  linear map `A`; the relative-interior and closure identities for inverse images are derived API
  and belong on the existing `Convex` owner surface rather than in a new graph wrapper.
- Best owner abstraction: the file stays `source-facing` in `namespace Convex`, but the proofs are
  refined to the existing graph/image/intersection owner abstractions instead of any new public
  graph-packaged declaration.
-/

namespace Convex

open Topology
open scoped Rockafellar

section Helpers

variable
    {𝕜 E F : Type*}
    [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {C : Set F}

private theorem intrinsicInterior_univ_eq_univ :
    ri[𝕜]((Set.univ : Set E)) = Set.univ := by
  refine subset_antisymm intrinsicInterior_subset ?_
  simpa using
    (interior_subset_intrinsicInterior :
      interior (Set.univ : Set E) ⊆ ri[𝕜]((Set.univ : Set E)))

private abbrev graphEmbedding (A : E →ₗ[𝕜] F) : E →ₗ[𝕜] E × F :=
  LinearMap.id.prod A

private abbrev graphAffineSubspace (A : E →ₗ[𝕜] F) : AffineSubspace 𝕜 (E × F) :=
  (LinearMap.graph A).toAffineSubspace

private abbrev graphStrip (E : Type*) (S : Set F) : Set (E × F) :=
  Set.univ ×ˢ S

private theorem graphEmbedding_injective (A : E →ₗ[𝕜] F) :
    Function.Injective (graphEmbedding A) := by
  intro x y hxy
  exact congrArg Prod.fst hxy

private theorem graphEmbedding_image_preimage (A : E →ₗ[𝕜] F) (S : Set F) :
    graphEmbedding A '' (A ⁻¹' S) =
      ((graphAffineSubspace A : AffineSubspace 𝕜 (E × F)) : Set (E × F)) ∩ graphStrip E S := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · simp [graphEmbedding, graphAffineSubspace, Submodule.mem_toAffineSubspace,
        LinearMap.mem_graph_iff]
    · simpa [graphStrip] using hx
  · rintro ⟨hpM, hpS⟩
    have hpgraph : p.2 = A p.1 := by
      simpa [graphAffineSubspace, Submodule.mem_toAffineSubspace, LinearMap.mem_graph_iff] using hpM
    refine ⟨p.1, ?_, ?_⟩
    · simpa [graphStrip, hpgraph] using hpS.2
    · ext <;> simp [graphEmbedding, hpgraph]

private theorem graphSection_intrinsicInterior_nonempty (A : E →ₗ[𝕜] F)
    (hri : (A ⁻¹' (ri[𝕜](C))).Nonempty) :
    ((graphAffineSubspace A : Set (E × F)) ∩ ri[𝕜](graphStrip E C)).Nonempty := by
  rcases hri with ⟨x, hx⟩
  refine ⟨graphEmbedding A x, ?_, ?_⟩
  · simp [graphEmbedding, graphAffineSubspace, Submodule.mem_toAffineSubspace,
      LinearMap.mem_graph_iff]
  · simpa
      [graphEmbedding, graphStrip, intrinsicInterior_univ_eq_univ, ri_prod_eq] using
      show (x, A x) ∈ ri[𝕜]((Set.univ : Set E)) ×ˢ ri[𝕜](C) from
        ⟨by simp [intrinsicInterior_univ_eq_univ], hx⟩

private theorem eq_of_graphEmbedding_image_eq (A : E →ₗ[𝕜] F) {s t : Set E}
    (h : graphEmbedding A '' s = graphEmbedding A '' t) :
    s = t := by
  ext x
  constructor
  · intro hx
    have hx' : graphEmbedding A x ∈ graphEmbedding A '' t := by
      rw [← h]
      exact ⟨x, hx, rfl⟩
    rcases hx' with ⟨y, hy, hyx⟩
    exact graphEmbedding_injective A hyx ▸ hy
  · intro hx
    have hx' : graphEmbedding A x ∈ graphEmbedding A '' s := by
      rw [h]
      exact ⟨x, hx, rfl⟩
    rcases hx' with ⟨y, hy, hyx⟩
    exact graphEmbedding_injective A hyx ▸ hy

end Helpers

section Main

section RelativeInteriorPreimage

variable
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

variable {C : Set F}

/-- Theorem 6.7 (1): if `A : E →ₗ[𝕜] F` is linear, `C ⊆ F` is convex, and the preimage of the
relative interior of `C` is nonempty, then the relative interior of `A ⁻¹' C` is exactly the
preimage of `ri[𝕜](C)`. -/
-- Proof sketch: embed `E` into `E × F` by the graph map `x ↦ (x, A x)`, so that the image of
-- `A ⁻¹' C` is the affine section of `Set.univ ×ˢ C` cut out by the graph of `A`. Apply
-- Corollary 6.5.1 to that affine section, use Text 6.18 to simplify the product relative
-- interior, and then pull the resulting equality back along the injective graph embedding.
theorem intrinsicInterior_linear_preimage (hC : Convex 𝕜 C) (A : E →ₗ[𝕜] F)
    (hri : (A ⁻¹' (ri[𝕜](C))).Nonempty) :
    ri[𝕜](A ⁻¹' C) = A ⁻¹' (ri[𝕜](C)) := by
  let b := graphEmbedding A
  let m := graphAffineSubspace A
  let d : Set (E × F) := graphStrip E C
  have himage (S : Set F) : b '' (A ⁻¹' S) = (m : Set (E × F)) ∩ graphStrip E S := by
    simpa [b, m] using graphEmbedding_image_preimage A S
  have hdri : ((m : Set (E × F)) ∩ ri[𝕜](d)).Nonempty := by
    simpa [d] using
      graphSection_intrinsicInterior_nonempty A hri
  have hsection :
      ri[𝕜]((m : Set (E × F)) ∩ d) = (m : Set (E × F)) ∩ ri[𝕜](d) :=
    m.intrinsicInterior_inter_eq ((convex_univ : Convex 𝕜 (Set.univ : Set E)).prod hC) hdri
  have himage_eq :
      b '' (ri[𝕜](A ⁻¹' C)) = b '' (A ⁻¹' (ri[𝕜](C))) := by
    calc
      b '' (ri[𝕜](A ⁻¹' C)) = ri[𝕜](b '' (A ⁻¹' C)) := by
        symm
        simpa using (hC.linear_preimage A).intrinsicInterior_linear_image b
      _ = ri[𝕜]((m : Set (E × F)) ∩ d) := by
        rw [himage C]
      _ = (m : Set (E × F)) ∩ ri[𝕜](d) := hsection
      _ = (m : Set (E × F)) ∩ graphStrip E (ri[𝕜](C)) := by
        simp [d, graphStrip, intrinsicInterior_univ_eq_univ]
      _ = b '' (A ⁻¹' (ri[𝕜](C))) :=
        (himage (ri[𝕜](C))).symm
  exact eq_of_graphEmbedding_image_eq A <| by
    simpa [b] using himage_eq

end RelativeInteriorPreimage

section ClosurePreimage

variable
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

variable {C : Set F}

/-- Theorem 6.7 (2), intrinsic owner form: inverse images of convex sets under a linear map
preserve intrinsic closure when the preimage of the relative interior is nonempty. -/
theorem intrinsicClosure_linear_preimage (hC : Convex 𝕜 C) (A : E →ₗ[𝕜] F)
    (hri : (A ⁻¹' (ri[𝕜](C))).Nonempty) :
    cl[𝕜](A ⁻¹' C) = A ⁻¹' cl[𝕜](C) := by
  let b := graphEmbedding A
  let m := graphAffineSubspace A
  let d : Set (E × F) := graphStrip E C
  have hb_inj : Function.Injective b := by
    simpa [b] using graphEmbedding_injective A
  have hb_closed := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hb_inj)
  have himage (S : Set F) : b '' (A ⁻¹' S) = (m : Set (E × F)) ∩ graphStrip E S := by
    simpa [b, m] using graphEmbedding_image_preimage A S
  have hdri : ((m : Set (E × F)) ∩ ri[𝕜](d)).Nonempty := by
    simpa [d] using
      graphSection_intrinsicInterior_nonempty A hri
  have hsection :
      closure ((m : Set (E × F)) ∩ d) = (m : Set (E × F)) ∩ closure d :=
    m.closure_inter_eq ((convex_univ : Convex 𝕜 (Set.univ : Set E)).prod hC) hdri
  have himage_eq :
      b '' closure (A ⁻¹' C) = b '' (A ⁻¹' closure C) := by
    calc
      b '' closure (A ⁻¹' C) = closure (b '' (A ⁻¹' C)) := by
        symm
        simpa using hb_closed.isClosedMap.closure_image_eq_of_continuous hb_closed.continuous
          (A ⁻¹' C)
      _ = closure ((m : Set (E × F)) ∩ d) := by
        rw [himage C]
      _ = (m : Set (E × F)) ∩ closure d := hsection
      _ = (m : Set (E × F)) ∩ graphStrip E (closure C) := by
        simp [d, graphStrip, closure_prod_eq]
      _ = b '' (A ⁻¹' closure C) := (himage (closure C)).symm
  have hclosure :
      closure (A ⁻¹' C) = A ⁻¹' closure C :=
    eq_of_graphEmbedding_image_eq A <| by
      simpa [b] using himage_eq
  simpa [intrinsicClosure_eq_closure 𝕜] using hclosure

/-- Theorem 6.7 (2), ambient-closure bridge core: in finite-dimensional spaces, inverse images of
convex sets under a linear map preserve ordinary closure. -/
theorem closure_linear_preimage (hC : Convex 𝕜 C) (A : E →ₗ[𝕜] F)
    (hri : (A ⁻¹' (ri[𝕜](C))).Nonempty) :
    closure (A ⁻¹' C) = A ⁻¹' closure C := by
  simpa [intrinsicClosure_eq_closure 𝕜] using
    intrinsicClosure_linear_preimage hC A hri

end ClosurePreimage

end Main

end Convex

end
