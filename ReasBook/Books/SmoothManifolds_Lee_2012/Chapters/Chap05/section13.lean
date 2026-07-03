import Mathlib
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Homeomorph.TransferInstance

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_5_13 (from Chap05/Sec05_30) -/
open scoped ContDiff Manifold

section SubmersionLevelSets

universe uE uE' uH uH' uM uN

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]

-- Semantic search note: the owner abstraction here is the chapter-level constant-rank level-set
-- theorem `constant_rank_level_set_has_embedded_submanifold_structure`, specialized to the
-- source-facing smooth-submersion hypothesis.
-- Proof sketch: a smooth submersion has full rank at every point, hence constant rank equal to the
-- target dimension; apply Theorem 5.12 to the fiber `Φ ⁻¹' {y}`.
/-- Corollary 5.13 (1): the level set of a smooth submersion carries a smooth embedded submanifold
structure whose codimension is the dimension of the target manifold. -/
theorem smooth_submersion_level_set_has_embedded_submanifold_structure {Φ : M → N}
    (hΦ : Manifold.IsSmoothSubmersion I J Φ) (y : N) :
    let k : ℕ := Module.finrank ℝ E - Module.finrank ℝ E'
    let S : Set M := Φ ⁻¹' {y}
    let K := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) S,
        ∃ hs : IsManifold K ∞ S,
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := cs
        let _ : IsManifold K ∞ S := hs
        ∃ hS : IsEmbeddedSubmanifold I K S,
          hS.codimension = Module.finrank ℝ E' := by
  simpa using
    (constant_rank_level_set_has_embedded_submanifold_structure
      hΦ.contMDiff hΦ.hasConstantRank y)

-- Proof sketch: specialize the proper-embedding part of Theorem 5.12 to the constant-rank value
-- `Module.finrank ℝ E'` furnished by the smooth-submersion hypothesis.
/-- Corollary 5.13 (2): each level set of a smooth submersion is properly embedded in the ambient
manifold. -/
theorem smooth_submersion_level_set_isProperlyEmbedded [T1Space N] {Φ : M → N}
    (hΦ : Manifold.IsSmoothSubmersion I J Φ) (y : N) :
    (Φ ⁻¹' {y}).IsProperlyEmbedded := by
  simpa using
    (constant_rank_level_set_isProperlyEmbedded
      hΦ.contMDiff hΦ.hasConstantRank y)

end SubmersionLevelSets

/-! ### Problem_5_13 (from Chap05/Sec05_37) -/
open scoped Manifold Matrix Torus ContDiff

local notation "T2Model" => ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)
local notation "R2Model" => ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓘(ℝ))

noncomputable section

/-- Source-facing owner for Problem 5-13: the subset `S` is allowed to carry a topology different
from the ambient subtype topology, together with a one-dimensional smooth structure for which the
inclusion is weakly embedded. The existing `IsWeaklyEmbeddedSubmanifold` class is intentionally not
used here because it is tied to the ambient subtype topology on `S`. -/
def AdmitsWeaklyEmbeddedDenseCurveStructure (S : Set 𝕋^{2}) : Prop :=
  ∃ t : TopologicalSpace S,
    letI : TopologicalSpace S := t
    ∃ cs : ChartedSpace ℝ S,
      letI : ChartedSpace ℝ S := cs
      ∃ hs : IsManifold 𝓘(ℝ) ∞ S,
        letI : IsManifold 𝓘(ℝ) ∞ S := hs
        BoundarylessManifold 𝓘(ℝ) S ∧
          Manifold.IsImmersion 𝓘(ℝ) T2Model ∞ (Subtype.val : S → 𝕋^{2}) ∧
            ∀ {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
              {H'' : Type*} [TopologicalSpace H''] {N : Type*} [TopologicalSpace N]
              [ChartedSpace H'' N] (K : ModelWithCorners ℝ E'' H'') [IsManifold K ∞ N]
              {F : N → 𝕋^{2}} (_hF : ContMDiff K T2Model ∞ F) (hFS : ∀ x, F x ∈ S),
              ContMDiff K 𝓘(ℝ) ∞ (Set.codRestrict F S hFS)

-- Owner/bridge note: the chapter-level owner for an injective immersion is
-- `Manifold.IsImmersion.toImmersedSubmanifold`. This problem stays at the bridge/view layer,
-- because the source asks for a smooth structure on the actual image subset
-- `Set.range (denseTorusCurve α)`, not just for an immersed-submanifold owner with the same
-- carrier.

/-- Helper for Problem 5-13: the range of `denseTorusCurve α` is nonempty. -/
instance dense_torus_curve_range_nonempty (α : ℝ) :
    Nonempty (Set.range (denseTorusCurve α)) :=
  ⟨⟨denseTorusCurve α 0, ⟨0, rfl⟩⟩⟩

/-- Helper for Problem 5-13: the injective dense torus curve identifies `ℝ` with its image. -/
noncomputable def dense_torus_curve_range_equiv (α : ℝ) (hα : Irrational α) :
    ℝ ≃ Set.range (denseTorusCurve α) :=
  Equiv.ofInjective (denseTorusCurve α) (denseTorusCurve_injective α hα)

/-- Helper for Problem 5-13: transport the standard topology on `ℝ` to the image of the dense
torus curve. -/
abbrev dense_torus_curve_range_topologicalSpace (α : ℝ) (hα : Irrational α) :
    TopologicalSpace (Set.range (denseTorusCurve α)) :=
  (dense_torus_curve_range_equiv α hα).symm.topologicalSpace

/-- Helper for Problem 5-13: after transporting the topology, the image of the dense torus curve
is homeomorphic to `ℝ`. -/
noncomputable abbrev dense_torus_curve_range_homeomorph (α : ℝ) (hα : Irrational α) :
    let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_topologicalSpace α hα
    ℝ ≃ₜ Set.range (denseTorusCurve α) :=
  let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_topologicalSpace α hα
  ((dense_torus_curve_range_equiv α hα).symm.homeomorph).symm

/-- Helper for Problem 5-13: the transported range structure uses the single chart
`e.symm : Set.range (denseTorusCurve α) → ℝ`. -/
noncomputable abbrev dense_torus_curve_range_chartedSpace (α : ℝ) (hα : Irrational α) :
    let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_topologicalSpace α hα
    ChartedSpace ℝ (Set.range (denseTorusCurve α)) :=
  let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_topologicalSpace α hα
  (dense_torus_curve_range_homeomorph α hα).symm.isOpenEmbedding.singletonChartedSpace

/-- Helper for Problem 5-13: the transported singleton chart on the dense torus curve image is the
global coordinate map `e.symm : Set.range (denseTorusCurve α) → ℝ`. -/
noncomputable abbrev dense_torus_curve_range_chart (α : ℝ) (hα : Irrational α) :
    let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_topologicalSpace α hα
    Set.range (denseTorusCurve α) → ℝ :=
  let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_topologicalSpace α hα
  (dense_torus_curve_range_homeomorph α hα).symm

/-- Helper for Problem 5-13: the transported singleton chart makes the image subset a smooth
boundaryless `1`-manifold. -/
lemma dense_torus_curve_range_isManifold_top (α : ℝ) (hα : Irrational α) :
    let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_topologicalSpace α hα
    let _ : ChartedSpace ℝ (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_chartedSpace α hα
    IsManifold 𝓘(ℝ) ∞ (Set.range (denseTorusCurve α)) := by
  let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_topologicalSpace α hα
  let _ : ChartedSpace ℝ (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_chartedSpace α hα
  -- The transported atlas is literally the singleton chart coming from the homeomorphism to `ℝ`.
  exact
    (dense_torus_curve_range_homeomorph α hα).symm.isOpenEmbedding.isManifold_singleton
      (I := 𝓘(ℝ)) (n := (∞ : ℕ∞ω))

/-- Helper for Problem 5-13: the subtype inclusion factors through the inverse of the transported
homeomorphism by the original dense torus curve. -/
lemma dense_torus_curve_range_subtype_val_eq_comp_symm (α : ℝ) (hα : Irrational α) :
    let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_topologicalSpace α hα
    (Subtype.val : Set.range (denseTorusCurve α) → 𝕋^{2}) =
      denseTorusCurve α ∘ (dense_torus_curve_range_homeomorph α hα).symm := by
  let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_topologicalSpace α hα
  -- Evaluate at a point of the range and rewrite it using `e (e.symm x) = x`.
  funext x
  exact
    (congrArg Subtype.val
      ((dense_torus_curve_range_homeomorph α hα).apply_symm_apply x)).symm

/-- Helper for Problem 5-13: the dense torus curve is an immersion at top differentiability. -/
lemma dense_torus_curve_isImmersion_top (α : ℝ) :
    Manifold.IsImmersion 𝓘(ℝ) T2Model ∞ (denseTorusCurve α) := by
  -- The Chapter 4 source proof already builds the immersion through the affine-line factorization
  -- and the torus covering map, so we reuse that owner directly here.
  exact denseTorusCurve_isImmersion α

/-- Helper for Problem 5-13: once the transported topology and atlas on the dense torus curve
image are fixed definitionally, the subtype inclusion uses the same immersion charts as the
original curve. -/
lemma dense_torus_curve_range_subtype_val_isImmersionAt_explicit (α : ℝ) (hα : Irrational α)
    (x : Set.range (denseTorusCurve α)) :
    let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_topologicalSpace α hα
    let _ : ChartedSpace ℝ (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_chartedSpace α hα
    let _ : IsManifold 𝓘(ℝ) ∞ (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_isManifold_top α hα
    Manifold.IsImmersionAtOfComplement (dense_torus_curve_isImmersion_top α).complement
      𝓘(ℝ) T2Model ∞
      (Subtype.val : Set.range (denseTorusCurve α) → 𝕋^{2}) x := by
  sorry

/-- Helper for Problem 5-13: in the transported smooth structure, the inclusion of the dense torus
curve image into `𝕋²` is still an immersion. -/
lemma dense_torus_curve_range_subtype_val_isImmersion (α : ℝ) (hα : Irrational α) :
    let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_topologicalSpace α hα
    let _ : ChartedSpace ℝ (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_chartedSpace α hα
    let _ : IsManifold 𝓘(ℝ) ∞ (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_isManifold_top α hα
    Manifold.IsImmersion 𝓘(ℝ) T2Model ∞
      (Subtype.val : Set.range (denseTorusCurve α) → 𝕋^{2}) := by
  let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_topologicalSpace α hα
  let _ : ChartedSpace ℝ (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_chartedSpace α hα
  let _ : IsManifold 𝓘(ℝ) ∞ (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_isManifold_top α hα
  -- Route correction: this transported-range step is already formal once the top immersion of the
  -- original curve is available; the only real blocker lives upstream in that top witness.
  refine ⟨(dense_torus_curve_isImmersion_top α).complement, inferInstance, inferInstance, ?_⟩
  intro x
  simpa using dense_torus_curve_range_subtype_val_isImmersionAt_explicit α hα x

/-- Helper for Problem 5-13: after composing with the transported range chart
`e.symm : Set.range (denseTorusCurve α) → ℝ`, proving smoothness into the image reduces to
ordinary smoothness of the lifted real-valued map. -/
lemma dense_torus_curve_range_contMDiff_of_comp_homeomorph_symm
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {N : Type*} [TopologicalSpace N]
    [ChartedSpace H'' N] (K : ModelWithCorners ℝ E'' H'') [IsManifold K ∞ N]
    (α : ℝ) (hα : Irrational α)
    {f : N → Set.range (denseTorusCurve α)}
    (hf :
      ContMDiff K 𝓘(ℝ) ∞
        (dense_torus_curve_range_chart α hα ∘ f)) :
    let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_topologicalSpace α hα
    let _ : ChartedSpace ℝ (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_chartedSpace α hα
    ContMDiff K 𝓘(ℝ) ∞ f := by
  let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_topologicalSpace α hα
  let _ : ChartedSpace ℝ (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_chartedSpace α hα
  let hOpen : Topology.IsOpenEmbedding (dense_torus_curve_range_chart α hα) :=
    (dense_torus_curve_range_homeomorph α hα).symm.isOpenEmbedding
  -- The codomain charted-space structure was defined from this open embedding, so `of_comp` is
  -- exactly the desired transport step.
  simpa using
    (ContMDiff.of_comp_isOpenEmbedding
      (I := K) (I' := 𝓘(ℝ)) (n := (∞ : ℕ∞ω)) (h' := hOpen) hf)

/-- Helper for Problem 5-13: the transported range chart recovers the ambient map by composing the
lifted parameter map with the original dense torus curve. -/
lemma dense_torus_curve_range_chart_codRestrict_factorization
    {N : Type*} (α : ℝ) (hα : Irrational α) {F : N → 𝕋^{2}}
    (hFS : ∀ x, F x ∈ Set.range (denseTorusCurve α)) :
    F =
      denseTorusCurve α ∘
        (dense_torus_curve_range_chart α hα ∘
          Set.codRestrict F (Set.range (denseTorusCurve α)) hFS) := by
  -- Evaluate the range factorization at each point and rewrite the codomain restriction by
  -- `Subtype.val`.
  funext x
  have hfactor := dense_torus_curve_range_subtype_val_eq_comp_symm α hα
  have hx := congrArg (fun k : Set.range (denseTorusCurve α) → 𝕋^{2} ↦
      k (Set.codRestrict F (Set.range (denseTorusCurve α)) hFS x)) hfactor
  simpa [Function.comp] using hx

/-- Helper for Problem 5-13: charted manifolds over real models with corners are locally
connected. -/
private lemma dense_torus_curve_manifold_locallyConnectedSpace
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] (K : ModelWithCorners ℝ E'' H'')
    {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N] :
    LocallyConnectedSpace N := by
  -- Pull the model-space local path connectedness of `range K` through `K`, then through the
  -- charted-space atlas on `N`.
  letI : LocPathConnectedSpace H'' := by
    letI : LocPathConnectedSpace (Set.range K) := K.convex_range.locPathConnectedSpace
    exact K.isClosedEmbedding.toHomeomorph.isOpenEmbedding.locPathConnectedSpace
  letI : LocPathConnectedSpace N := ChartedSpace.locPathConnectedSpace H'' N
  infer_instance

/-- Helper for Problem 5-13: the discrepancy set `n - α m` coming from two torus-covering lifts
is countable. -/
private lemma dense_torus_curve_branch_discrepancy_countable (α : ℝ) :
    Set.Countable (Set.range fun p : ℤ × ℤ ↦ (p.2 : ℝ) - α * (p.1 : ℝ)) := by
  -- This is just the range of a map out of the countable lattice `ℤ × ℤ`.
  exact Set.countable_range _

/-- Helper for Problem 5-13: once the ambient map factors through the dense torus curve, the
pointwise torus-covering lift identifies the parameter map as a smooth local branch. -/
lemma dense_torus_curve_range_lift_contMDiffAt
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {N : Type*} [TopologicalSpace N]
    [ChartedSpace H'' N] (K : ModelWithCorners ℝ E'' H'') [IsManifold K ∞ N]
    (α : ℝ) (hα : Irrational α) {F : N → 𝕋^{2}} {g : N → ℝ}
  (hF : ContMDiff K T2Model ∞ F) (hFg : F = denseTorusCurve α ∘ g) (x : N) :
    ContMDiffAt K 𝓘(ℝ) ∞ g x := by
  sorry

/-- Helper for Problem 5-13: if a smooth ambient map lands in the dense torus curve image, then
its lifted real-valued parameter map is smooth. -/
lemma dense_torus_curve_range_lift_contMDiff
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {N : Type*} [TopologicalSpace N]
    [ChartedSpace H'' N] (K : ModelWithCorners ℝ E'' H'') [IsManifold K ∞ N]
    (α : ℝ) (hα : Irrational α) {F : N → 𝕋^{2}}
    (hF : ContMDiff K T2Model ∞ F)
    (hFS : ∀ x, F x ∈ Set.range (denseTorusCurve α)) :
    ContMDiff K 𝓘(ℝ) ∞
      (dense_torus_curve_range_chart α hα ∘
        Set.codRestrict F (Set.range (denseTorusCurve α)) hFS) := by
  let g : N → ℝ :=
    dense_torus_curve_range_chart α hα ∘ Set.codRestrict F (Set.range (denseTorusCurve α)) hFS
  have hFg : F = denseTorusCurve α ∘ g :=
    dense_torus_curve_range_chart_codRestrict_factorization (α := α) (hα := hα) hFS
  -- Verify smoothness pointwise by lifting `F` through the torus covering and using irrationality
  -- to show the local lift agrees with the transported parameter.
  intro x
  exact dense_torus_curve_range_lift_contMDiffAt (K := K) (α := α) hα hF hFg x

/-- Helper for Problem 5-13: every smooth ambient map with image in the dense torus curve image is
smooth as a map into the transported image manifold. -/
lemma dense_torus_curve_range_contMDiff_toSubtype
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {N : Type*} [TopologicalSpace N]
    [ChartedSpace H'' N] (K : ModelWithCorners ℝ E'' H'') [IsManifold K ∞ N]
    (α : ℝ) (hα : Irrational α) {F : N → 𝕋^{2}}
    (hF : ContMDiff K T2Model ∞ F)
    (hFS : ∀ x, F x ∈ Set.range (denseTorusCurve α)) :
    let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_topologicalSpace α hα
    let _ : ChartedSpace ℝ (Set.range (denseTorusCurve α)) :=
      dense_torus_curve_range_chartedSpace α hα
    ContMDiff K 𝓘(ℝ) ∞
      (Set.codRestrict F (Set.range (denseTorusCurve α)) hFS) := by
  let _ : TopologicalSpace (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_topologicalSpace α hα
  let _ : ChartedSpace ℝ (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_chartedSpace α hα
  -- First prove smoothness after applying the transported global chart `e.symm`, then transport
  -- it back to the image manifold.
  exact dense_torus_curve_range_contMDiff_of_comp_homeomorph_symm
    (K := K) (α := α) (hα := hα)
    (f := Set.codRestrict F (Set.range (denseTorusCurve α)) hFS)
    (dense_torus_curve_range_lift_contMDiff (K := K) α hα hF hFS)

-- Proof sketch: use the injective immersion from Example 4.20,
-- `t ↦ (e^{2π i t}, e^{2π i α t}) : ℝ → 𝕋²`, to transport the standard smooth `1`-manifold
-- structure on `ℝ` to its image. Then identify the subtype inclusion of that image with the
-- factorization of the curve through its range and verify the defining lift property of weak
-- embeddedness.
/-- Problem 5-13: for irrational `α`, the image of the dense torus curve from Example 4.20 admits
a smooth `1`-manifold structure for which it is a weakly embedded submanifold of `𝕋²`. -/
theorem denseTorusCurve_range_admits_weaklyEmbeddedSubmanifoldStructure
    (α : ℝ) (hα : Irrational α) :
    AdmitsWeaklyEmbeddedDenseCurveStructure (Set.range (denseTorusCurve α)) := by
  let t : TopologicalSpace (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_topologicalSpace α hα
  refine ⟨t, ?_⟩
  let cs : ChartedSpace ℝ (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_chartedSpace α hα
  refine ⟨cs, ?_⟩
  let hs : IsManifold 𝓘(ℝ) ∞ (Set.range (denseTorusCurve α)) :=
    dense_torus_curve_range_isManifold_top α hα
  refine ⟨hs, ?_⟩
  let _ : TopologicalSpace (Set.range (denseTorusCurve α)) := t
  let _ : ChartedSpace ℝ (Set.range (denseTorusCurve α)) := cs
  let _ : IsManifold 𝓘(ℝ) ∞ (Set.range (denseTorusCurve α)) := hs
  -- The transported chart is modeled on `ℝ`, so boundarylessness is inherited from the real model.
  refine ⟨inferInstance, ?_, ?_⟩
  · -- The subtype inclusion uses the same local normal form as the original dense torus curve.
    exact dense_torus_curve_range_subtype_val_isImmersion α hα
  · -- The weakly embedded lifting axiom is exactly the transported smoothness statement.
    intro E'' _ _ H'' _ N _ _ K _ F hF hFS
    exact dense_torus_curve_range_contMDiff_toSubtype (K := K) α hα hF hFS
