module

public import Topology_Munkres_2000.Book.Example_38_1
public import Topology_Munkres_2000.Book.Example_38_2.Compactification
public import Topology_Munkres_2000.Book.Example_38_4.Extension
public import Topology_Munkres_2000.Book.Example_38_4.OscillatingExtension
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Order.ExtendFrom

@[expose] public section

open Filter Set
open scoped BoundedContinuousFunction ContinuousMap
open OpenUnitInterval

namespace Compactification

universe u v w z

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Example 38.4: equivalent compactifications admit extensions of exactly the
same maps. -/
private lemma extends_iff_of_equivalent (C : Compactification.{u, v} X)
    (D : Compactification.{u, w} X) {Y : Type z} [TopologicalSpace Y]
    (h : Equivalent C D) (f : X → Y) :
    C.Extends f ↔ D.Extends f := by
  rw [C.extends_iff, D.extends_iff]
  constructor
  · rintro ⟨g, hg⟩
    rcases h with ⟨e⟩
    let inverse : ContinuousMap D C :=
      ⟨e.toHomeomorph.symm, e.toHomeomorph.symm.continuous⟩
    -- Precompose the extension with the inverse equivalence and use its commuting square.
    refine ⟨g.comp inverse, ?_⟩
    intro x
    rw [ContinuousMap.comp_apply]
    dsimp only [inverse, ContinuousMap.coe_mk]
    rw [e.symm_commutes, hg]
  · rintro ⟨g, hg⟩
    rcases h with ⟨e⟩
    let forward : ContinuousMap C D :=
      ⟨e.toHomeomorph, e.toHomeomorph.continuous⟩
    -- Precompose in the other direction and use the original commuting square.
    refine ⟨g.comp forward, ?_⟩
    intro x
    rw [ContinuousMap.comp_apply]
    dsimp only [forward, ContinuousMap.coe_mk]
    rw [e.commutes, hg]

end Compactification

namespace OpenUnitInterval

/-- Helper for Example 38.4: closed order intervals inside `(0, 1)` are compact. -/
private lemma openUnitIntervalCompactIccSpace :
    CompactIccSpace (Ioo (0 : ℝ) 1) := by
  apply CompactIccSpace.mk'
  intro a b _
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have himage :
      Subtype.val '' Icc a b = Icc (a : ℝ) (b : ℝ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨y, ⟨hay, hyb⟩, rfl⟩
      exact ⟨hay, hyb⟩
    · rintro ⟨hax, hxb⟩
      have hx : x ∈ Ioo (0 : ℝ) 1 := by
        exact ⟨a.property.1.trans_le hax, hxb.trans_lt b.property.2⟩
      exact ⟨⟨x, hx⟩, ⟨hax, hxb⟩, rfl⟩
  rw [himage]
  exact isCompact_Icc

/-- Helper for Example 38.4: extension to the one-point compactification is equivalent to
a common limit at the two order ends of `(0, 1)`. -/
private lemma onePointCompactification_extends_iff_atBot_atTop
    (f : Ioo (0 : ℝ) 1 →ᵇ ℝ) :
    onePointCompactification.Extends f ↔
      ∃ l : ℝ, Tendsto f atBot (nhds l) ∧ Tendsto f atTop (nhds l) := by
  letI : CompactIccSpace (Ioo (0 : ℝ) 1) := openUnitIntervalCompactIccSpace
  have hcocompact_eq :
      cocompact (Ioo (0 : ℝ) 1) = atBot ⊔ atTop :=
    cocompact_eq_atBot_atTop
  rw [onePointCompactification.extends_iff]
  constructor
  · rintro ⟨g, hg⟩
    have hcontinuous : Continuous (fun y : OnePoint (Ioo (0 : ℝ) 1) ↦ g y) :=
      g.continuous
    have hrestriction :
        (fun x : Ioo (0 : ℝ) 1 ↦ g (OnePoint.some x)) = f := by
      funext x
      rw [← onePointCompactification_apply x]
      exact hg x
    -- Continuity at the added point is convergence along the cocompact filter.
    rw [OnePoint.continuous_iff] at hcontinuous
    refine ⟨g OnePoint.infty, ?_⟩
    simpa only [Filter.coclosedCompact_eq_cocompact, hcocompact_eq,
      Filter.tendsto_sup, hrestriction] using hcontinuous.1
  · rintro ⟨l, hbot, htop⟩
    have hcocompact : Tendsto f (Filter.coclosedCompact (Ioo (0 : ℝ) 1)) (nhds l) := by
      -- The cocompact filter is the supremum of the two endpoint filters.
      simpa only [Filter.coclosedCompact_eq_cocompact, hcocompact_eq,
        Filter.tendsto_sup] using And.intro hbot htop
    let g : ContinuousMap (OnePoint (Ioo (0 : ℝ) 1)) ℝ :=
      OnePoint.continuousMapMk f.toContinuousMap l hcocompact
    refine ⟨g, ?_⟩
    intro x
    -- The one-point constructor agrees with `f` at every ordinary point.
    rw [onePointCompactification_apply]
    rfl

/-- Helper for Example 38.4: independent limits at the two ends produce a continuous map
on the closed unit interval agreeing with the original function on `(0, 1)`. -/
private lemma exists_closedUnitIntervalExtension_of_endpointLimits
    (f : Ioo (0 : ℝ) 1 →ᵇ ℝ) {l₀ l₁ : ℝ}
    (h₀ : Tendsto f atBot (nhds l₀)) (h₁ : Tendsto f atTop (nhds l₁)) :
    ∃ g : ContinuousMap (Icc (0 : ℝ) 1) ℝ,
      ∀ x, g (UnitInterval.openInClosed x) = f x := by
  classical
  let ambient : ℝ → ℝ := Function.extend Subtype.val f (fun _ ↦ 0)
  have hzero_lt_one : (0 : ℝ) < 1 := by norm_num
  have hambient_restrict : ambient ∘ Subtype.val = f := by
    exact Function.extend_comp Subtype.val_injective f (fun _ ↦ 0)
  have hambient_continuous : ContinuousOn ambient (Ioo (0 : ℝ) 1) := by
    -- On the open interval, the ambient extension is exactly the continuous function `f`.
    rw [continuousOn_iff_continuous_restrict]
    simpa only [Set.restrict_def, ← Function.comp_def, hambient_restrict] using f.continuous
  have hambient_atBot : Tendsto ambient (nhdsWithin 0 (Ioi 0)) (nhds l₀) := by
    -- Transfer the left endpoint limit from the subtype to the ambient function.
    rw [← tendsto_comp_coe_Ioo_atBot hzero_lt_one]
    simpa only [← Function.comp_def, hambient_restrict] using h₀
  have hambient_atTop : Tendsto ambient (nhdsWithin 1 (Iio 1)) (nhds l₁) := by
    -- Transfer the right endpoint limit in the same way.
    rw [← tendsto_comp_coe_Ioo_atTop hzero_lt_one]
    simpa only [← Function.comp_def, hambient_restrict] using h₁
  have hextend :
      ContinuousOn (extendFrom (Ioo (0 : ℝ) 1) ambient) (Icc (0 : ℝ) 1) :=
    continuousOn_Icc_extendFrom_Ioo hambient_continuous hambient_atBot hambient_atTop
  let g : ContinuousMap (Icc (0 : ℝ) 1) ℝ :=
    ⟨fun x ↦ extendFrom (Ioo (0 : ℝ) 1) ambient x.1,
      continuousOn_iff_continuous_restrict.mp hextend⟩
  refine ⟨g, ?_⟩
  intro x
  -- Inside the open interval, `extendFrom` and then `ambient` both recover `f`.
  dsimp only [g, ContinuousMap.coe_mk]
  have hopen_value : (UnitInterval.openInClosed x).1 = x.1 := rfl
  rw [hopen_value]
  rw [extendFrom_extends hambient_continuous x.1 x.property]
  exact Function.Injective.extend_apply Subtype.val_injective f (fun _ ↦ 0) x

end OpenUnitInterval

/-- Example 38.4 (1): A bounded continuous real function on `(0, 1)` extends to the
circle compactification exactly when its one-sided endpoint limits exist and are equal. -/
theorem circleCompactification_extendable_iff (f : Ioo (0 : ℝ) 1 →ᵇ ℝ) :
    circleCompactification.Extends f ↔
      ∃ l : ℝ,
        Tendsto f (comap Subtype.val (nhdsWithin 0 (Ioi 0))) (nhds l) ∧
          Tendsto f (comap Subtype.val (nhdsWithin 1 (Iio 1))) (nhds l) := by
  -- Transport to the canonical one-point model, then identify its two order-end filters.
  rw [Compactification.extends_iff_of_equivalent circleCompactification
    onePointCompactification circleCompactification_equivalent_onePoint]
  rw [OpenUnitInterval.onePointCompactification_extends_iff_atBot_atTop]
  rw [comap_coe_Ioo_nhdsGT (0 : ℝ) 1, comap_coe_Ioo_nhdsLT (0 : ℝ) 1]

/-- Companion to Example 38.4 (2): A bounded continuous real function on `(0, 1)` extends to the
closed-interval compactification exactly when both one-sided endpoint limits exist. -/
theorem closedIntervalCompactification_extendable_iff (f : Ioo (0 : ℝ) 1 →ᵇ ℝ) :
    closedUnitIntervalCompactification.Extends f ↔
      ∃ l₀ l₁ : ℝ,
        Tendsto f (comap Subtype.val (nhdsWithin 0 (Ioi 0))) (nhds l₀) ∧
          Tendsto f (comap Subtype.val (nhdsWithin 1 (Iio 1))) (nhds l₁) := by
  rw [comap_coe_Ioo_nhdsGT (0 : ℝ) 1, comap_coe_Ioo_nhdsLT (0 : ℝ) 1]
  rw [closedUnitIntervalCompactification.extends_iff]
  constructor
  · rintro ⟨g, hg⟩
    have hzero_lt_one : (0 : ℝ) < 1 := by norm_num
    have hzero_mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have hone_mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    let zeroPoint : Icc (0 : ℝ) 1 := ⟨0, hzero_mem⟩
    let onePoint : Icc (0 : ℝ) 1 := ⟨1, hone_mem⟩
    have hcoe_zero :
        Tendsto ((↑) : Ioo (0 : ℝ) 1 → ℝ) atBot (nhds (0 : ℝ)) := by
      have hwithin :
          Tendsto ((↑) : Ioo (0 : ℝ) 1 → ℝ) atBot (nhdsWithin 0 (Ioi 0)) := by
        rw [← map_coe_Ioo_atBot hzero_lt_one]
        exact tendsto_map
      exact hwithin.mono_right nhdsWithin_le_nhds
    have hcoe_one :
        Tendsto ((↑) : Ioo (0 : ℝ) 1 → ℝ) atTop (nhds (1 : ℝ)) := by
      have hwithin :
          Tendsto ((↑) : Ioo (0 : ℝ) 1 → ℝ) atTop (nhdsWithin 1 (Iio 1)) := by
        rw [← map_coe_Ioo_atTop hzero_lt_one]
        exact tendsto_map
      exact hwithin.mono_right nhdsWithin_le_nhds
    have hopen_zero : Tendsto UnitInterval.openInClosed atBot (nhds zeroPoint) := by
      -- Bundle ambient convergence at `0` into convergence in the closed-interval subtype.
      rw [tendsto_subtype_rng]
      simpa only [UnitInterval.openInClosed, zeroPoint] using hcoe_zero
    have hopen_one : Tendsto UnitInterval.openInClosed atTop (nhds onePoint) := by
      -- Bundle ambient convergence at `1` into convergence in the closed-interval subtype.
      rw [tendsto_subtype_rng]
      simpa only [UnitInterval.openInClosed, onePoint] using hcoe_one
    have hrestriction :
        (g : Icc (0 : ℝ) 1 → ℝ) ∘ UnitInterval.openInClosed = f := by
      funext x
      rw [Function.comp_apply]
      rw [← closedUnitIntervalCompactification_apply x]
      exact hg x
    -- Compose continuity of the extension with convergence of the two inclusions.
    refine ⟨g zeroPoint, g onePoint, ?_, ?_⟩
    · have hg_zero : Tendsto g (nhds zeroPoint) (nhds (g zeroPoint)) :=
        g.continuous.continuousAt
      simpa only [hrestriction] using hg_zero.comp hopen_zero
    · have hg_one : Tendsto g (nhds onePoint) (nhds (g onePoint)) :=
        g.continuous.continuousAt
      simpa only [hrestriction] using hg_one.comp hopen_one
  · rintro ⟨l₀, l₁, h₀, h₁⟩
    rcases OpenUnitInterval.exists_closedUnitIntervalExtension_of_endpointLimits f h₀ h₁ with
      ⟨g, hg⟩
    refine ⟨g, ?_⟩
    intro x
    -- The constructed map agrees with `f` after identifying the compactification embedding.
    rw [closedUnitIntervalCompactification_apply]
    exact hg x

namespace TopologistsSineCurve

/-- Helper for Example 38.4: the ambient inclusion evaluates on an ordinary point as the
original sine-curve embedding. -/
private lemma inclusion_compactification_apply (x : Ioo (0 : ℝ) 1) :
    InducedCompactification.inclusion squareEmbedding (compactification x) =
      squareEmbedding x := by
  -- Expose the item-owned abbreviation once, then use the induced compactification API.
  unfold compactification
  exact InducedCompactification.inclusion_compactification
    squareEmbedding isEmbedding_squareEmbedding x

/-- Helper for Example 38.4: every point of the sine-curve compactification has first
coordinate in the closed unit interval. -/
private lemma sineCurveFirstCoordinate_mem (y : compactification) :
    (InducedCompactification.inclusion squareEmbedding y).1.1 ∈ Icc (0 : ℝ) 1 := by
  have hcoordinate : Continuous (fun p : Square ↦ p.1.1) :=
    continuous_subtype_val.comp continuous_fst
  have hclosed : IsClosed {p : Square | p.1.1 ∈ Icc (0 : ℝ) 1} :=
    isClosed_Icc.preimage hcoordinate
  have hrange : Set.range squareEmbedding ⊆ {p : Square | p.1.1 ∈ Icc (0 : ℝ) 1} := by
    rintro _ ⟨x, rfl⟩
    have hplane := squareInclusion_squareEmbedding x
    rw [squareInclusion_apply] at hplane
    have hfirst : (squareEmbedding x).1.1 = x.1 := by
      simpa only using congrArg Prod.fst hplane
    rw [Set.mem_setOf_eq]
    rw [hfirst]
    exact ⟨le_of_lt x.property.1, le_of_lt x.property.2⟩
  -- The closed coordinate condition persists on the closure defining the compactification.
  have hclosure := closure_minimal hrange hclosed
  simpa only [InducedCompactification.inclusion, Set.mem_setOf_eq] using hclosure y.property

/-- Helper for Example 38.4: the first-coordinate projection from the sine-curve
compactification to `[0, 1]` is continuous. -/
private lemma continuous_sineCurveFirstCoordinate :
    Continuous (fun y : compactification ↦
      (⟨(InducedCompactification.inclusion squareEmbedding y).1.1,
        sineCurveFirstCoordinate_mem y⟩ : Icc (0 : ℝ) 1)) := by
  have hinclusion : Continuous (InducedCompactification.inclusion squareEmbedding) :=
    (InducedCompactification.isEmbedding_inclusion squareEmbedding).continuous
  have hcoordinate : Continuous
      (fun y : compactification ↦
        (InducedCompactification.inclusion squareEmbedding y).1.1) :=
    (continuous_subtype_val.comp continuous_fst).comp hinclusion
  -- Restrict the continuous ambient coordinate map to its proved interval-valued range.
  exact Continuous.subtype_mk hcoordinate sineCurveFirstCoordinate_mem

end TopologistsSineCurve

/-- Companion to Example 38.4 (3): Endpoint limits suffice for a bounded continuous real function on
`(0, 1)` to extend to the topologist's-sine-curve compactification. -/
theorem endpointLimits_extendable_toSineCurve (f : Ioo (0 : ℝ) 1 →ᵇ ℝ)
    (h₀ : ∃ l₀ : ℝ, Tendsto f (comap Subtype.val (nhdsWithin 0 (Ioi 0))) (nhds l₀))
    (h₁ : ∃ l₁ : ℝ, Tendsto f (comap Subtype.val (nhdsWithin 1 (Iio 1))) (nhds l₁)) :
    TopologistsSineCurve.compactification.Extends f := by
  rcases h₀ with ⟨l₀, h₀⟩
  rcases h₁ with ⟨l₁, h₁⟩
  have hclosed : closedUnitIntervalCompactification.Extends f :=
    (closedIntervalCompactification_extendable_iff f).mpr ⟨l₀, l₁, h₀, h₁⟩
  rw [Compactification.extends_iff] at hclosed
  rcases hclosed with ⟨g, hg⟩
  let firstCoordinate :
      ContinuousMap TopologistsSineCurve.compactification (Icc (0 : ℝ) 1) :=
    ⟨fun y ↦
        ⟨(InducedCompactification.inclusion TopologistsSineCurve.squareEmbedding y).1.1,
          TopologistsSineCurve.sineCurveFirstCoordinate_mem y⟩,
      TopologistsSineCurve.continuous_sineCurveFirstCoordinate⟩
  rw [Compactification.extends_iff]
  refine ⟨g.comp firstCoordinate, ?_⟩
  intro x
  have hcoordinate :
      firstCoordinate (TopologistsSineCurve.compactification x) =
        UnitInterval.openInClosed x := by
    apply Subtype.ext
    -- The induced compactification inclusion computes to the original square embedding.
    dsimp only [firstCoordinate, ContinuousMap.coe_mk]
    rw [TopologistsSineCurve.inclusion_compactification_apply]
    have hplane := TopologistsSineCurve.squareInclusion_squareEmbedding x
    rw [TopologistsSineCurve.squareInclusion_apply] at hplane
    exact congrArg Prod.fst hplane
  -- The first coordinate lands on `x`, where the closed-interval extension agrees with `f`.
  rw [ContinuousMap.comp_apply]
  have hg_open : g (UnitInterval.openInClosed x) = f x := by
    rw [← closedUnitIntervalCompactification_apply x]
    exact hg x
  calc
    g (firstCoordinate (TopologistsSineCurve.compactification x)) =
        g (UnitInterval.openInClosed x) := congrArg g hcoordinate
    _ = f x := hg_open

namespace TopologistsSineCurve

/-- Companion to Example 38.4 (4): The second-coordinate map extends `x ↦ sin (1 / x)` to the
topologist's-sine-curve compactification. -/
theorem oscillatingExtension_apply (x : Ioo (0 : ℝ) 1) :
    oscillatingExtension (compactification x) = Real.sin (1 / x.1) := by
  -- The ambient inclusion recovers `squareEmbedding`; its second coordinate is the sine term.
  rw [oscillatingExtension_eq, inclusion_compactification_apply]
  have hplane := squareInclusion_squareEmbedding x
  rw [squareInclusion_apply] at hplane
  exact congrArg Prod.snd hplane

end TopologistsSineCurve

end
