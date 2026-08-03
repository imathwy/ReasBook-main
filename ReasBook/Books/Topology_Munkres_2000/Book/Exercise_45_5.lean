module

public import Topology_Munkres_2000.Book.Definition_45_3.PointwiseBounded
public import Topology_Munkres_2000.Book.Exercise_45_5.VanishingAtInfinity
public import Topology_Munkres_2000.Book.Theorem_45_4.ProperTarget
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.MetricSpace.Equicontinuity

public section

open scoped BoundedContinuousFunction OnePoint ZeroAtInfty

open Topology

universe u w

/-- Helper for Exercise 45.5: a real-valued family vanishes uniformly at infinity exactly when,
outside one compact set depending only on `ε`, every member has absolute value less than `ε`. -/
theorem uniformlyVanishesAtInfinity_iff {ι : Type w} {X : Type u} [TopologicalSpace X]
    (F : ι → X → ℝ) :
    UniformlyVanishesAtInfinity F ↔
      ∀ ε > 0, ∃ K : Set X, IsCompact K ∧ ∀ i x, x ∉ K → |F i x| < ε := by
  -- Rewrite uniform vanishing into metric convergence on the product filter.
  rw [uniformlyVanishesAtInfinity_iff_tendstoUniformlyOnFilter,
    Metric.tendstoUniformlyOnFilter_iff]
  constructor
  · intro h ε hε
    obtain ⟨pi, hpi, px, hpx, hprod⟩ := Filter.eventually_prod_iff.mp (h ε hε)
    rw [Filter.eventually_top] at hpi
    obtain ⟨K, hK, hKpx⟩ := Filter.hasBasis_cocompact.mem_iff.mp hpx
    refine ⟨K, hK, ?_⟩
    intro i x hx
    have hdist := hprod (hpi i) (hKpx hx)
    simpa only [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs] using hdist
  · intro h ε hε
    obtain ⟨K, hK, h_out⟩ := h ε hε
    apply Filter.eventually_prod_iff.mpr
    refine ⟨fun _ ↦ True, Filter.Eventually.of_forall fun _ ↦ trivial,
      fun x ↦ x ∉ K, hK.compl_mem_cocompact, ?_⟩
    intro i _ x hx
    simpa only [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs] using h_out i x hx

/-- Helper for Exercise 45.5: uniform vanishing in the source's set-of-functions formulation. -/
theorem Set.uniformlyVanishesAtInfinity_iff {X : Type u} [TopologicalSpace X]
    (𝓕 : Set (X → ℝ)) :
    𝓕.UniformlyVanishesAtInfinity ↔
      ∀ ε > 0, ∃ K : Set X, IsCompact K ∧
        ∀ f ∈ 𝓕, ∀ x, x ∉ K → |f x| < ε := by
  change UniformlyVanishesAtInfinity ((↑) : 𝓕 → X → ℝ) ↔ _
  constructor
  · intro h ε hε
    obtain ⟨K, hK, h_out⟩ :=
      (_root_.uniformlyVanishesAtInfinity_iff ((↑) : 𝓕 → X → ℝ)).1 h ε hε
    exact ⟨K, hK, fun f hf x hx ↦ h_out ⟨f, hf⟩ x hx⟩
  · intro h
    apply (_root_.uniformlyVanishesAtInfinity_iff ((↑) : 𝓕 → X → ℝ)).2
    intro ε hε
    obtain ⟨K, hK, h_out⟩ := h ε hε
    exact ⟨K, hK, fun f x hx ↦ h_out f f.property x hx⟩

section

variable (X : Type u) [TopologicalSpace X]

/- Exercise 45.5 (2). Here `C₀(X, ℝ)` is mathlib's canonical type of continuous
real-valued functions tending to zero along the cocompact filter. -/
#check C₀(X, ℝ)

end

namespace ZeroAtInftyContinuousMap

/-- Helper for Exercise 45.5: a function in `C₀(X, ℝ)` tends to zero along the closed-compact
filter used by the one-point compactification. -/
lemma tendsto_coclosedCompact_zero {X : Type u} [TopologicalSpace X] [T2Space X]
    (f : C₀(X, ℝ)) : Filter.Tendsto f (Filter.coclosedCompact X) (𝓝 0) := by
  -- In a Hausdorff space compact sets are closed, so the two filters coincide.
  simpa only [Filter.coclosedCompact_eq_cocompact] using zero_at_infty f

/-- Helper for Exercise 45.5: extend a function vanishing at infinity by zero on `OnePoint X`. -/
def zeroExtension {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (f : C₀(X, ℝ)) : OnePoint X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    (OnePoint.continuousMapMk f.toContinuousMap 0 (tendsto_coclosedCompact_zero f))

/-- Helper for Exercise 45.5: zero extension agrees with the original function on `X`. -/
@[simp] lemma zeroExtension_coe {X : Type u} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (f : C₀(X, ℝ)) (x : X) : zeroExtension f x = f x := by
  -- Both constructors evaluate definitionally through `OnePoint.elim` at a coerced point.
  rfl

/-- Helper for Exercise 45.5: zero extension takes the value zero at infinity. -/
@[simp] lemma zeroExtension_infty {X : Type u} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (f : C₀(X, ℝ)) : zeroExtension f ∞ = 0 := by
  -- The added point is assigned the chosen limiting value.
  rfl


/-- Helper for Exercise 45.5: zero extension preserves the uniform distance. -/
lemma isometry_zeroExtension {X : Type u} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] :
    Isometry (zeroExtension : C₀(X, ℝ) → OnePoint X →ᵇ ℝ) := by
  -- Compare the two sup metrics pointwise, with the empty-domain case separated explicitly.
  apply Isometry.of_dist_eq
  intro f g
  apply le_antisymm
  · rw [BoundedContinuousFunction.dist_le_iff_of_nonempty]
    intro p
    induction p using OnePoint.rec with
    | infty => simp only [zeroExtension_infty, dist_self, dist_nonneg]
    | coe x =>
        exact (BoundedContinuousFunction.dist_coe_le_dist (f := f.toBCF) (g := g.toBCF) x).trans_eq
          ZeroAtInftyContinuousMap.dist_toBCF_eq_dist
  · cases isEmpty_or_nonempty X with
    | inl hX =>
        letI : IsEmpty X := hX
        rw [ZeroAtInftyContinuousMap.eq_of_empty f g, dist_self]
        exact dist_nonneg
    | inr hX =>
        letI : Nonempty X := hX
        rw [← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist,
          BoundedContinuousFunction.dist_le_iff_of_nonempty]
        intro x
        exact BoundedContinuousFunction.dist_coe_le_dist (f := zeroExtension f)
          (g := zeroExtension g) (x : OnePoint X)

/-- Helper for Exercise 45.5: zero extension preserves equicontinuity at ordinary points. -/
lemma equicontinuousAt_zeroExtension_coe_iff {ι : Type w} {X : Type u}
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] (F : ι → C₀(X, ℝ)) (x : X) :
    EquicontinuousAt (fun i p ↦ zeroExtension (F i) p) (x : OnePoint X) ↔
      EquicontinuousAt (fun i y ↦ F i y) x := by
  -- Pull the metric neighborhood criterion back through the open embedding of `X`.
  rw [Metric.equicontinuousAt_iff_right, Metric.equicontinuousAt_iff_right,
    OnePoint.nhds_coe_eq]
  simp only [Filter.eventually_map, zeroExtension_coe]

/-- Helper for Exercise 45.5: equicontinuity of zero extensions at `∞` is uniform vanishing. -/
lemma equicontinuousAt_zeroExtension_infty_iff {ι : Type w} {X : Type u}
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] (F : ι → C₀(X, ℝ)) :
    EquicontinuousAt (fun i p ↦ zeroExtension (F i) p) (∞ : OnePoint X) ↔
      UniformlyVanishesAtInfinity (fun i x ↦ F i x) := by
  -- A common neighborhood of `∞` is the complement of one closed compact exceptional set.
  rw [Metric.equicontinuousAt_iff_right, uniformlyVanishesAtInfinity_iff]
  constructor
  · intro h ε hε
    obtain ⟨K, ⟨hK_closed, hK_compact⟩, h_near⟩ :=
      OnePoint.hasBasis_nhds_infty.eventually_iff.mp (h ε hε)
    refine ⟨K, hK_compact, ?_⟩
    intro i x hx
    have hx_mem : (x : OnePoint X) ∈ (fun y : X ↦ (y : OnePoint X)) '' Kᶜ ∪ {∞} :=
      Set.mem_union_left _ ⟨x, hx, rfl⟩
    simpa only [zeroExtension_infty, zeroExtension_coe, dist_zero_left,
      Real.norm_eq_abs] using h_near hx_mem i
  · intro h ε hε
    obtain ⟨K, hK_compact, h_out⟩ := h ε hε
    apply OnePoint.hasBasis_nhds_infty.eventually_iff.mpr
    refine ⟨K, ⟨hK_compact.isClosed, hK_compact⟩, ?_⟩
    intro p hp i
    rcases hp with hp | hp
    · obtain ⟨x, hx, rfl⟩ := hp
      simpa only [zeroExtension_infty, zeroExtension_coe, dist_zero_left,
        Real.norm_eq_abs] using h_out i x hx
    · have hp_infty : p = (∞ : OnePoint X) := Set.mem_singleton_iff.mp hp
      rw [hp_infty, zeroExtension_infty, dist_self]
      exact hε

/-- Helper for Exercise 45.5: globally, zero extension is equicontinuous exactly when the
original family is equicontinuous and vanishes uniformly at infinity. -/
lemma equicontinuous_zeroExtension_iff {ι : Type w} {X : Type u}
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] (F : ι → C₀(X, ℝ)) :
    Equicontinuous (fun i p ↦ zeroExtension (F i) p) ↔
      Equicontinuous (fun i x ↦ F i x) ∧
        UniformlyVanishesAtInfinity (fun i x ↦ F i x) := by
  -- Split the one-point compactification into its ordinary points and the added point.
  constructor
  · intro h
    refine ⟨fun x ↦ (equicontinuousAt_zeroExtension_coe_iff F x).1 (h x),
      (equicontinuousAt_zeroExtension_infty_iff F).1 (h ∞)⟩
  · rintro ⟨h_equicontinuous, h_vanishes⟩ p
    induction p using OnePoint.rec with
    | infty => exact (equicontinuousAt_zeroExtension_infty_iff F).2 h_vanishes
    | coe x => exact (equicontinuousAt_zeroExtension_coe_iff F x).2 (h_equicontinuous x)

/-- Helper for Exercise 45.5: zero extension preserves pointwise boundedness. -/
lemma pointwiseBounded_zeroExtension_iff {ι : Type w} {X : Type u}
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] (F : ι → C₀(X, ℝ)) :
    PointwiseBounded (fun i p ↦ zeroExtension (F i) p) ↔
      PointwiseBounded (fun i x ↦ F i x) := by
  -- At ordinary points the ranges agree, while the range at `∞` is the singleton `{0}`.
  rw [pointwiseBounded_iff, pointwiseBounded_iff]
  constructor
  · intro h x
    simpa only [zeroExtension_coe] using h (x : OnePoint X)
  · intro h p
    induction p using OnePoint.rec with
    | infty =>
        exact Set.finite_range_const.isBounded
    | coe x => simpa only [zeroExtension_coe] using h x

/-- Helper for Exercise 45.5: equicontinuity of the zero-extension image is equivalent to
equicontinuity of the subtype-indexed zero extensions. -/
lemma equicontinuous_zeroExtension_image_iff {X : Type u} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (𝓕 : Set C₀(X, ℝ)) :
    Equicontinuous
        (fun g : zeroExtension '' 𝓕 ↦ (g : OnePoint X → ℝ)) ↔
      Equicontinuous (fun f : 𝓕 ↦ (zeroExtension f : OnePoint X → ℝ)) := by
  -- The image subtype and the original subtype index the same functions, possibly with repeats.
  constructor
  · intro h
    have h_comp := h.comp (fun f : 𝓕 ↦
      ⟨zeroExtension f, ⟨f, f.property, rfl⟩⟩)
    have h_family :
        (fun g : zeroExtension '' 𝓕 ↦ (g : OnePoint X → ℝ)) ∘
            (fun f : 𝓕 ↦ ⟨zeroExtension f, ⟨f, f.property, rfl⟩⟩) =
          fun f : 𝓕 ↦ (zeroExtension f : OnePoint X → ℝ) := by
      funext f p
      rfl
    rw [h_family] at h_comp
    exact h_comp
  · intro h p U hU
    filter_upwards [h p U hU] with q hq
    intro g
    obtain ⟨f, hf, hfg⟩ := g.property
    rw [← hfg]
    exact hq ⟨f, hf⟩

/-- Helper for Exercise 45.5: pointwise boundedness of the zero-extension image is equivalent to
pointwise boundedness of the subtype-indexed zero extensions. -/
lemma pointwiseBounded_zeroExtension_image_iff {X : Type u} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (𝓕 : Set C₀(X, ℝ)) :
    PointwiseBounded
        (fun g : zeroExtension '' 𝓕 ↦ (g : OnePoint X → ℝ)) ↔
      PointwiseBounded (fun f : 𝓕 ↦ (zeroExtension f : OnePoint X → ℝ)) := by
  -- At every point, the two evaluation ranges are equal.
  rw [pointwiseBounded_iff, pointwiseBounded_iff]
  apply forall_congr'
  intro p
  have h_range :
      Set.range (fun g : zeroExtension '' 𝓕 ↦ (g : OnePoint X → ℝ) p) =
        Set.range (fun f : 𝓕 ↦ zeroExtension f p) := by
    ext y
    constructor
    · rintro ⟨g, hgy⟩
      obtain ⟨f, hf, hfg⟩ := g.property
      refine ⟨⟨f, hf⟩, ?_⟩
      calc
        zeroExtension f p = (g : OnePoint X →ᵇ ℝ) p :=
          congrArg (fun k : OnePoint X →ᵇ ℝ ↦ k p) hfg
        _ = y := hgy
    · rintro ⟨f, hfy⟩
      refine ⟨⟨zeroExtension f, ⟨f, f.property, rfl⟩⟩, ?_⟩
      exact hfy
  rw [h_range]


/-- Exercise 45.5. On a locally compact Hausdorff space, a subset of `C₀(X, ℝ)` has
compact closure exactly when it is pointwise bounded, equicontinuous, and vanishes uniformly
at infinity. -/
theorem isCompact_closure_iff {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X]
    [T2Space X] (𝓕 : Set C₀(X, ℝ)) :
    IsCompact (closure 𝓕) ↔
      PointwiseBounded (fun f : 𝓕 ↦ (f : X → ℝ)) ∧
        Equicontinuous (fun f : 𝓕 ↦ (f : X → ℝ)) ∧
          UniformlyVanishesAtInfinity (fun f : 𝓕 ↦ (f : X → ℝ)) := by
  -- Transport compactness through the closed isometric zero-extension embedding.
  rw [isometry_zeroExtension.isEmbedding.isCompact_iff,
    ← isometry_zeroExtension.isClosedEmbedding.closure_image_eq,
    BoundedContinuousFunction.isCompact_closure_iff_equicontinuous_and_pointwiseBounded]
  -- Replace the image subtype by the original subtype-indexed zero-extension family.
  rw [equicontinuous_zeroExtension_image_iff, pointwiseBounded_zeroExtension_image_iff,
    equicontinuous_zeroExtension_iff, pointwiseBounded_zeroExtension_iff]
  tauto

end ZeroAtInftyContinuousMap
