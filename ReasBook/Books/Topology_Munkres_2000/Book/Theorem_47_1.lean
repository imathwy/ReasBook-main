module

public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.Basic

public section

universe u v

namespace ContinuousMap

/-- Helper for Theorem 47.1: set equicontinuity of the underlying functions is
equivalent to equicontinuity of the family indexed by the original set. -/
private lemma equicontinuous_toFun_image_iff
    {X : Type u} {Y : Type v} [TopologicalSpace X] [UniformSpace Y]
    (𝓕 : Set C(X, Y)) :
    (ContinuousMap.toFun '' 𝓕).Equicontinuous ↔
      Equicontinuous (fun f : 𝓕 ↦ (f : X → Y)) := by
  -- Identify the image with the range used by the family/set equicontinuity bridge.
  have h_range :
      Set.range (fun f : 𝓕 ↦ (f : X → Y)) = ContinuousMap.toFun '' 𝓕 := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.property, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [← h_range]
  exact equicontinuous_iff_range.symm

/-- Helper for Theorem 47.1: the continuous members of a compact equicontinuous
set of functions form a compact subset of `C(X, Y)`. -/
private lemma isCompact_preimage_toFun_of_isCompact_of_equicontinuous
    {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (K : Set (X → Y)) (hK_compact : IsCompact K) (hK_equicontinuous : K.Equicontinuous) :
    IsCompact (ContinuousMap.toFun ⁻¹' K) := by
  -- Equicontinuity makes every pointwise-limit function continuous, so the pullback maps onto `K`.
  have h_image :
      ContinuousMap.toFun '' (ContinuousMap.toFun ⁻¹' K) = K := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      let g : C(X, Y) := ⟨f, hK_equicontinuous.continuous_of_mem hf⟩
      exact ⟨g, hf, rfl⟩
  -- The compact-open Ascoli theorem now applies to this continuous realization of `K`.
  refine ArzelaAscoli.isCompact_of_equicontinuous
    (ContinuousMap.toFun ⁻¹' K) ?_ ?_
  · rwa [h_image]
  · rw [← equicontinuous_toFun_image_iff, h_image]
    exact hK_equicontinuous

/-- Helper for Theorem 47.1: a compact family of continuous maps on a locally compact
domain is equicontinuous. -/
private lemma equicontinuous_coe_of_isCompact
    {X : Type u} {Y : Type v} [TopologicalSpace X] [LocallyCompactSpace X] [MetricSpace Y]
    (K : Set C(X, Y)) (hK : IsCompact K) :
    Equicontinuous (fun f : K ↦ (f : X → Y)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  -- Joint continuity of evaluation supplies the uncurried form of the transpose.
  have h_eval_const (x : X) : Continuous (fun f : K ↦ (f : C(X, Y)) x) :=
    (continuous_eval_const x).comp continuous_subtype_val
  have h_joint : Continuous (fun p : X × K ↦ (p.2 : C(X, Y)) p.1) :=
    continuous_eval.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
  -- Curry evaluation into `C(K, Y)`, then use compactness of `K` to pass to uniform convergence.
  have h_compactOpen :
      Continuous (fun x : X ↦
        (⟨fun f : K ↦ (f : C(X, Y)) x, h_eval_const x⟩ : C(K, Y))) :=
    ContinuousMap.continuous_of_continuous_uncurry _ h_joint
  have h_uniform :
      Continuous (fun x : X ↦ UniformFun.ofFun (fun f : K ↦ (f : C(X, Y)) x)) :=
    (ContinuousMap.continuous_iff_continuous_uniformFun _).mp h_compactOpen
  -- This transpose is exactly the characterization of equicontinuity by uniform functions.
  have h_transpose :
      (UniformFun.ofFun ∘ Function.swap (fun f : K ↦ (f : X → Y))) =
        (fun x : X ↦ UniformFun.ofFun (fun f : K ↦ (f : C(X, Y)) x)) := rfl
  rw [equicontinuous_iff_continuous]
  rw [h_transpose]
  exact h_uniform

/-- Helper for Theorem 47.1: compact closure of a family gives compact closure of
each pointwise evaluation image. -/
private lemma isCompact_closure_image_apply_of_isCompact_closure
    {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (𝓕 : Set C(X, Y)) (h_compact : IsCompact (closure 𝓕)) (x : X) :
    IsCompact (closure ((fun f : C(X, Y) ↦ f x) '' 𝓕)) := by
  -- Continuous evaluation carries the compact closure onto the closure of the pointwise image.
  have h_image := image_closure_of_isCompact h_compact
    (continuous_eval_const x).continuousOn
  rw [← h_image]
  exact h_compact.image (continuous_eval_const x)

/-- The forward implication of Theorem 47.1: if a family of continuous maps is
equicontinuous and each
pointwise value set has compact closure, then the family has compact closure in
`C(X, Y)` with the compact-open topology. -/
theorem isCompact_closure_of_equicontinuous_of_pointwiseCompact
    {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (𝓕 : Set C(X, Y))
    (h_equicontinuous : Equicontinuous (fun f : 𝓕 ↦ (f : X → Y)))
    (h_pointwise : ∀ x : X, IsCompact (closure ((fun f : C(X, Y) ↦ f x) '' 𝓕))) :
    IsCompact (closure 𝓕) := by
  -- Control the family by its closure in the pointwise function space.
  let K : Set (X → Y) := closure (ContinuousMap.toFun '' 𝓕)
  have hK_compact : IsCompact K := by
    rw [Pi.isCompact_closure_iff]
    intro x
    simpa only [Set.image_image, Function.comp_apply, ContinuousMap.toFun_eq_coe] using
      h_pointwise x
  have hK_equicontinuous : K.Equicontinuous := by
    exact (equicontinuous_toFun_image_iff 𝓕).mpr h_equicontinuous |>.closure
  have h_preimage_compact : IsCompact (ContinuousMap.toFun ⁻¹' K) :=
    isCompact_preimage_toFun_of_isCompact_of_equicontinuous K hK_compact hK_equicontinuous
  -- The pullback is a closed compact superspace of `𝓕`, hence also of its closure.
  have h_preimage_closed : IsClosed (ContinuousMap.toFun ⁻¹' K) :=
    isClosed_closure.preimage continuous_coeFun
  have h_closure_subset : closure 𝓕 ⊆ ContinuousMap.toFun ⁻¹' K := by
    refine closure_minimal ?_ h_preimage_closed
    intro f hf
    exact subset_closure ⟨f, hf, rfl⟩
  exact h_preimage_compact.of_isClosed_subset isClosed_closure h_closure_subset

/-- The converse implication of Theorem 47.1: if `X` is locally compact Hausdorff
and a family of continuous
maps has compact closure, then it is equicontinuous and each pointwise value set has
compact closure. -/
theorem equicontinuous_and_pointwiseCompact_of_isCompact_closure
    {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MetricSpace Y] (𝓕 : Set C(X, Y))
    (h_compact : IsCompact (closure 𝓕)) :
    Equicontinuous (fun f : 𝓕 ↦ (f : X → Y)) ∧
      ∀ x : X, IsCompact (closure ((fun f : C(X, Y) ↦ f x) '' 𝓕)) := by
  constructor
  · -- Equicontinuity descends from the compact closure to the original family.
    have h_closure_equicontinuous := equicontinuous_coe_of_isCompact (closure 𝓕) h_compact
    have h_image_closure : (ContinuousMap.toFun '' closure 𝓕).Equicontinuous :=
      (equicontinuous_toFun_image_iff (closure 𝓕)).mpr h_closure_equicontinuous
    have h_image_family : (ContinuousMap.toFun '' 𝓕).Equicontinuous :=
      h_image_closure.mono (Set.image_mono subset_closure)
    exact (equicontinuous_toFun_image_iff 𝓕).mp h_image_family
  · -- Each evaluation image is compact because evaluation is continuous.
    exact isCompact_closure_image_apply_of_isCompact_closure 𝓕 h_compact

/-- Theorem 47.1 (Ascoli's theorem). For a locally compact Hausdorff domain, compact
closure is characterized by equicontinuity and compact closure of every pointwise
value set. -/
theorem isCompact_closure_iff_equicontinuous_and_pointwiseCompact
    {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MetricSpace Y] (𝓕 : Set C(X, Y)) :
    IsCompact (closure 𝓕) ↔
      Equicontinuous (fun f : 𝓕 ↦ (f : X → Y)) ∧
        ∀ x : X, IsCompact (closure ((fun f : C(X, Y) ↦ f x) '' 𝓕)) := by
  constructor
  · exact equicontinuous_and_pointwiseCompact_of_isCompact_closure 𝓕
  · rintro ⟨h_equicontinuous, h_pointwise⟩
    exact isCompact_closure_of_equicontinuous_of_pointwiseCompact 𝓕 h_equicontinuous h_pointwise

end ContinuousMap
