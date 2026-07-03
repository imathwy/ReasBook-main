import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.MetricSpace.Polish

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_1 (from Items/Chap13) -/
/- Definition 13.1: a Polish space is the canonical owner class `PolishSpace`. Its primitive
ingredients are `SecondCountableTopology` and
`TopologicalSpace.IsCompletelyMetrizableSpace`, so the textbook description of a separable space
admitting a compatible complete metric is already packaged by this owner abstraction. -/
recall PolishSpace

/-! ### Exercise_13_1_1 (from Items/Chap13) -/
open scoped BoundedContinuousFunction CompactlySupported

/-- Exercise 13.1.1 (1): the supremum-norm space `C([0,1], ℝ)` is separable. -/
-- This is the canonical owner instance for continuous maps on a locally compact second-countable
-- domain.
theorem continuousMap_Icc_zero_one_separable :
    TopologicalSpace.SeparableSpace (C(Set.Icc (0 : ℝ) 1, ℝ)) := by
  infer_instance

/-- Exercise 13.1.1 (2): the supremum-norm space of bounded continuous real-valued functions on
`[0, ∞)` is not separable. -/
-- Proof sketch: produce an uncountable family of bounded continuous functions that are pairwise
-- separated by a fixed positive distance in the supremum norm.
theorem boundedContinuousFunction_Ici_not_separable :
    ¬ TopologicalSpace.SeparableSpace ((Set.Ici (0 : ℝ)) →ᵇ ℝ) := sorry

/-- Exercise 13.1.1 (3): the supremum-norm space `C_c([0, ∞), ℝ)` is separable. -/
-- This is the canonical owner instance for compactly supported continuous maps on a locally
-- compact second-countable domain.
theorem compactlySupportedContinuousMap_Ici_separable :
    TopologicalSpace.SeparableSpace (C_c(Set.Ici (0 : ℝ), ℝ)) := by
  infer_instance

/-! ### Exercise_13_1_2 (from Items/Chap13) -/
/- Exercise 13.1.2: a locally finite measure is canonically finite on compact sets via the owner
instance `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`. -/
recall isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure

/- The source-facing compact-set consequence is then the canonical theorem
`IsCompact.measure_lt_top`. -/
recall IsCompact.measure_lt_top

/-! ### Exercise_13_1_3 (from Items/Chap13) -/
open MeasureTheory

universe u

variable {Ω : Type u} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [PolishSpace Ω]

/- Exercise 13.1.3 is source-facing in the measurability/regularity domain. Its core owner
abstraction for clause `(i)` is `AEMeasurable`; bridge facts such as `AEMeasurable.mk`,
`ContinuousOn.aemeasurable`, and the `σ`-finite exhaustion `spanningSets μ` support the proof
strategy without changing the main public statement. -/
/-- Exercise 13.1.3 (Lusin's theorem): for a map `f : Ω → ℝ` on a Polish space with a `σ`-finite
Borel measure `μ`, the following are equivalent: (i) `f` is `μ`-almost everywhere measurable;
(ii) for every `ε > 0` there is a compact set `K` with `μ Kᶜ < ENNReal.ofReal ε` such that `f` is
continuous on `K`. -/
-- Proof sketch: for `(i) → (ii)`, use `AEMeasurable` to choose a measurable representative and
-- apply the finite-measure Lusin/tightness API on the members of a `σ`-finite exhaustion by
-- `spanningSets μ`, patching the exceptional sets so that the total discarded mass is `< ε`. For
-- `(ii) → (i)`, continuity on each compact set gives measurable restrictions, and the hypothesis
-- that the complements have arbitrarily small measure implies that `f` agrees almost everywhere
-- with a Borel measurable map.
theorem aemeasurable_iff_forall_exists_isCompact_continuousOn_compl_lt
    (μ : Measure Ω) [SigmaFinite μ] (f : Ω → ℝ) :
    AEMeasurable f μ ↔
      ∀ ε > 0, ∃ K : Set Ω,
        IsCompact K ∧ μ Kᶜ < ENNReal.ofReal ε ∧ ContinuousOn f K := sorry

omit [TopologicalSpace Ω] [BorelSpace Ω] [PolishSpace Ω] in
/- Almost-everywhere measurability is the canonical owner notion for the existence of a
measurable representative. -/
recall AEMeasurable

/-! ### Exercise_13_1_4 (from Items/Chap13) -/
open MeasureTheory Set
open scoped BigOperators

/-- Exercise 13.1.4: if a family of positive-length intervals in `ℝ` has union of finite Lebesgue
measure, then for every `ε > 0` there is a finite pairwise disjoint subfamily whose total
Lebesgue measure is strictly larger than `((1 - ε) / 3)` times the measure of the whole union. -/
-- Proof sketch: first choose a finite subfamily whose union captures all but an `ε`-fraction of
-- `⋃₀ 𝓤`. Then apply the Vitali covering theorem to this finite interval family. The resulting
-- disjoint subfamily has the property that every interval in the finite approximation is contained
-- in the triple expansion of one selected interval, so the union measure is controlled by `3`
-- times the total measure of the disjoint family.
theorem exists_pairwiseDisjoint_interval_subfamily_large_measure
    (𝓤 : Set (Set ℝ))
    (h𝓤 : ∀ U ∈ 𝓤, U.OrdConnected ∧ 0 < volume.real U)
    (hfinite : volume (⋃₀ 𝓤) < ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (Set ℝ),
      (↑s : Set (Set ℝ)) ⊆ 𝓤 ∧
      (↑s : Set (Set ℝ)).PairwiseDisjoint id ∧
      ((1 - ε) / 3) * volume.real (⋃₀ 𝓤) < ∑ U ∈ s, volume.real U :=
  sorry

/-! ### Exercise_13_1_5 (from Items/Chap13) -/
open scoped BigOperators Pointwise
open MeasureTheory Set

/-- Exercise 13.1.5 (1): from a family of positive homothetic copies of a fixed open bounded convex
set in `ℝ^d`, modeled as `(Fin d → ℝ)`, whose union has finite Lebesgue measure, one can extract
finitely many pairwise disjoint members whose total measure is larger than
`((1 - ε) / 3^d) * λ^d(⋃₀ 𝒰)`. -/
-- Proof sketch: apply a Vitali-type covering argument to the family of translated dilates
-- `{x} + r • C`,
-- extract a disjoint subfamily covering almost all of the union, and then truncate the countable
-- disjoint family to a finite subfamily while losing only an `ε`-fraction of the total measure.
theorem exists_pairwiseDisjoint_homothetic_subfamily_large_measure
    (d : ℕ) (C : Set (Fin d → ℝ)) (𝒰 : Set (Set (Fin d → ℝ)))
    (hC_open : IsOpen C) (hC_convex : Convex ℝ C) (hC_bounded : Bornology.IsBounded C)
    (h𝒰 :
      ∀ U ∈ 𝒰,
        ∃ x : Fin d → ℝ, ∃ r > 0, U = ({x} : Set (Fin d → ℝ)) + r • C)
    (h_union_finite : volume (⋃₀ 𝒰) < ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (Set (Fin d → ℝ)),
      (↑s : Set (Set (Fin d → ℝ))) ⊆ 𝒰 ∧
      (↑s : Set (Set (Fin d → ℝ))).PairwiseDisjoint id ∧
      ((1 - ε) / (3 : ℝ) ^ d) * volume.real (⋃₀ 𝒰) < ∑ U ∈ s, volume.real U := sorry

/-- Exercise 13.1.5 (2): there is a family of open bounded convex sets in `ℝ²` with finite union
measure, modeled as `(Fin 2 → ℝ)`, for which the same positive-measure finite disjoint selection
lower bound fails, showing that the common similarity hypothesis in part (1) is essential. -/
-- Proof sketch: take a classical counterexample built from nonsimilar thin convex sets with large
-- overlap so that the union has finite measure but every finite pairwise disjoint subfamily carries
-- too little total measure compared with the union.
theorem exists_open_bounded_convex_counterexample_without_similarity :
    ∃ 𝒰 : Set (Set (Fin 2 → ℝ)), ∃ ε : ℝ,
      0 < ε ∧
      (∀ U ∈ 𝒰, IsOpen U ∧ Bornology.IsBounded U ∧ Convex ℝ U) ∧
      0 < volume.real (⋃₀ 𝒰) ∧
      volume (⋃₀ 𝒰) < ⊤ ∧
      ¬ ∃ s : Finset (Set (Fin 2 → ℝ)),
          (↑s : Set (Set (Fin 2 → ℝ))) ⊆ 𝒰 ∧
          (↑s : Set (Set (Fin 2 → ℝ))).PairwiseDisjoint id ∧
          ((1 - ε) / (3 : ℝ) ^ 2) * volume.real (⋃₀ 𝒰) < ∑ U ∈ s, volume.real U := sorry

/-! ### Exercise_13_1_6 (from Items/Chap13) -/
open MeasureTheory Set Filter
open scoped Pointwise Topology

-- Proof sketch: apply the owner theorem `VitaliFamily.ae_tendsto_rnDeriv` to the Vitali family
-- generated by the translated dilates `x + r • C`; since `A` is `μ`-null, the
-- Radon--Nikodym derivative of `μ` with respect to Lebesgue vanishes Lebesgue-almost everywhere on
-- `A`, so the normalized masses tend to `0` there. Only local finiteness of `μ` is used.
/-- Exercise 13.1.6 (1): For a locally finite measure on `ℝ^d`, the normalized masses of the translated
dilates of a bounded open convex set `C` containing `0` converge to `0` at Lebesgue-almost every
point of a `μ`-null set. -/
theorem ae_tendsto_zero_scaled_set_density_of_null
    {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsLocallyFiniteMeasure μ]
    {A C : Set (Fin d → ℝ)}
    (hA_null : μ A = 0) (hC_bounded : Bornology.IsBounded C)
    (hC_convex : Convex ℝ C) (hC_open : IsOpen C) (h0C : (0 : Fin d → ℝ) ∈ C) :
    ∀ᵐ x ∂(volume.restrict A),
      Tendsto
        (fun r : ℝ ↦ μ.real (({x} : Set (Fin d → ℝ)) + r • C) / r ^ d)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := sorry

-- Proof sketch: use part (1) for the Stieltjes measure `F.measure` on `ℝ` with a one-dimensional
-- convex neighborhood of `0`; then combine the resulting density limit with the owner theorem
-- `StieltjesFunction.ae_hasDerivAt` to identify the derivative as `0` on the `F.measure`-null set.
/-- Exercise 13.1.6 (2): If `F` is the distribution function of a Stieltjes measure and `A` is
`F.measure`-null, then `F` has derivative `0` Lebesgue-almost everywhere on `A`. -/
theorem ae_hasDerivAt_zero_on_stieltjes_null_set
    (F : StieltjesFunction ℝ) {A : Set ℝ} (hA_null : F.measure A = 0) :
    ∀ᵐ x ∂(volume.restrict A), HasDerivAt F 0 x := sorry

/-! ### Exercise_13_1_7 (from Items/Chap13) -/
open MeasureTheory Set Filter intervalIntegral
open scoped Pointwise Topology

/-- Exercise 13.1.7: for a locally integrable function on `ℝ^d`, the averages over the dilates
`x + r C` of an open bounded convex set `C` containing `0` converge almost everywhere to the value
`f x` as `r ↓ 0`. -/
-- Proof sketch: this is the source-facing specialization of the owner theorem
-- `VitaliFamily.ae_tendsto_average` to the Vitali family generated by the translated dilates
-- `{x} + r • C`, as suggested by Exercise 13.1.6.
theorem ae_tendsto_average_over_convex_dilates {d : ℕ}
    {f : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    {C : Set (Fin d → ℝ)} (hC_open : IsOpen C) (hC_convex : Convex ℝ C)
    (hC_bounded : Bornology.IsBounded C) (hC_zero : (0 : Fin d → ℝ) ∈ C) :
    ∀ᵐ x ∂volume,
      Tendsto
        (fun r : ℝ ↦ ⨍ y in ({x} + r • C), f y ∂volume)
        (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := sorry

/-- The one-dimensional primitive `x ↦ ∫ t in 0..x, f t` has derivative `f x` almost everywhere
for locally integrable `f`. -/
-- Proof sketch: apply `LocallyIntegrable.ae_hasDerivAt_integral` to `hf` with
-- base point `c = 0`, then pass from `HasDerivAt` to `deriv`.
theorem ae_deriv_intervalIntegral_from_zero_eq {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume, deriv (fun x ↦ ∫ t in (0 : ℝ)..x, f t) x = f x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf] with x hx
  simpa using (hx 0).deriv

/-! ### Exercise_13_1_8 (from Items/Chap13) -/
universe u

open MeasureTheory

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace.PseudoMetrizableSpace E] [SigmaCompactSpace E]

-- Proof sketch: the forward implication extracts local finiteness from `IsRadonMeasure μ` and
-- then uses the owner instance `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`.
-- Conversely, the explicit source-facing local finiteness hypothesis combines with
-- `IsFiniteMeasureOnCompacts μ` to give `σ`-finiteness and, via the owner regularity API
-- `Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`, inner regularity.
/-- Exercise 13.1.8: on a `σ`-compact pseudometrizable Borel space, a locally finite Borel measure
is Radon exactly when it is finite on compact sets, i.e. exactly when it satisfies
`IsFiniteMeasureOnCompacts`. -/
theorem isRadonMeasure_iff_isFiniteMeasureOnCompacts (μ : Measure E)
    (hμloc : IsLocallyFiniteMeasure μ) :
    IsRadonMeasure μ ↔ IsFiniteMeasureOnCompacts μ := by
  constructor
  · intro hμ
    letI : IsLocallyFiniteMeasure μ := hμ.locallyFinite
    infer_instance
  · intro hμ
    letI : IsLocallyFiniteMeasure μ := hμloc
    letI : IsFiniteMeasureOnCompacts μ := hμ
    exact IsRadonMeasure.of_owner μ
