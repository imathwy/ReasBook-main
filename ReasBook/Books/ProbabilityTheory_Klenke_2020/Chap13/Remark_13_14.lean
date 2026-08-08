import ProbabilityTheory_Klenke_2020.Chap13.Definition_13_4
import ProbabilityTheory_Klenke_2020.Chap13.Definition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction CompactlySupported Topology

universe u v

namespace MeasureTheory
namespace FiniteMeasure

/-- Remark 13.14 (i): convergence of finite measures on every measurable set is stronger than the
chapter's weak convergence on `FiniteMeasure E`. This is the positive-measure specialization of
the functional-analytic criterion for finite signed measures discussed in the remark. -/
theorem tendsto_of_setwise_tendsto
    {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (h :
      ∀ A : Set E, MeasurableSet A →
        Tendsto (fun n ↦ (μs n : Measure E) A) atTop (𝓝 ((μ : Measure E) A))) :
    Tendsto μs atTop (𝓝 μ) := sorry

end FiniteMeasure
end MeasureTheory

section

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

/- Remark 13.14 (ii): for finite measures, the weak topology is the canonical topology on
`MeasureTheory.FiniteMeasure E` characterized by continuity of the integral against every bounded
continuous real-valued test function. This is the theorem
`MeasureTheory.FiniteMeasure.continuous_iff_forall_continuous_integral`. -/
recall MeasureTheory.FiniteMeasure.continuous_iff_forall_continuous_integral

-- Proof sketch: unfold the definition of the topology on `FiniteMeasure E`; mathlib defines it as
-- the topology induced by `FiniteMeasure.toWeakDualBCNN`, so this is exactly the weak-* trace
-- statement for finite measures.
/-- The weak topology on finite measures is induced from the weak-dual embedding
`FiniteMeasure.toWeakDualBCNN`, matching the weak-* trace description from the remark. -/
theorem finiteMeasure_weakTopology_eq_induced_toWeakDualBCNN :
    (inferInstance : TopologicalSpace (FiniteMeasure E)) =
      TopologicalSpace.induced
        (FiniteMeasure.toWeakDualBCNN : FiniteMeasure E → WeakDual NNReal (E →ᵇ NNReal))
        inferInstance :=
  rfl

-- Proof sketch: one metrizes the weak topology by a Lévy-Prokhorov-type metric on finite measures;
-- on a separable pseudometrizable base space this yields a metrizable topology.
/-- On a separable pseudometrizable base space, the weak topology on finite measures is
metrizable; the Lévy-Prokhorov metric is the standard metrization route. -/
theorem finiteMeasure_weakTopology_metrizable_of_separable
    [TopologicalSpace.PseudoMetrizableSpace E] [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.MetrizableSpace (FiniteMeasure E) := sorry

-- Proof sketch: combine local compactness and Polishness of the base space with the standard
-- regularity and tightness theory for finite measures to obtain a Polish weak topology.
/-- On a locally compact Polish base space, finite measures equipped with their weak topology form a
Polish space. -/
theorem finiteMeasure_weakTopology_polish_of_locallyCompact
    [LocallyCompactSpace E] [BorelSpace E] [PolishSpace E] :
    PolishSpace (FiniteMeasure E) := sorry

end

section RadonTopology

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E]

private abbrev RadonMeasureSubtype (E : Type u) [TopologicalSpace E] [MeasurableSpace E] :=
  { μ : Measure E // IsRadonMeasure μ }

instance instIsRadonMeasure (μ : RadonMeasureSubtype E) : IsRadonMeasure (μ : Measure E) :=
  μ.2

instance instIsLocallyFiniteMeasureRadonMeasureSubtype (μ : RadonMeasureSubtype E) :
    IsLocallyFiniteMeasure (μ : Measure E) :=
  IsRadonMeasure.locallyFinite μ.2

/-- Integration against a compactly supported continuous real-valued test function on `𝓜(E)`. -/
def radonVagueIntegral (f : C_c(E, ℝ)) : RadonMeasureSubtype E → ℝ :=
  fun μ ↦ ∫ x, f x ∂(μ : Measure E)

@[simp] theorem radonVagueIntegral_apply (f : C_c(E, ℝ)) (μ : RadonMeasureSubtype E) :
    radonVagueIntegral f μ = ∫ x, f x ∂(μ : Measure E) :=
  rfl

namespace MeasureTheory
namespace FiniteMeasure

/-- A finite Borel measure on a `σ`-compact pseudometrizable space is a Radon measure. -/
theorem isRadonMeasure_of_sigmaCompact
    {E : Type u} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [SigmaCompactSpace E] [MeasurableSpace E] [BorelSpace E] (μ : FiniteMeasure E) :
    IsRadonMeasure (μ : Measure E) :=
  IsRadonMeasure.of_owner (μ : Measure E)

/-- Bridge map from finite measures to the Radon-measure subtype on a `σ`-compact
pseudometrizable Borel space. -/
def toRadonMeasure
    {E : Type u} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [SigmaCompactSpace E] [MeasurableSpace E] [BorelSpace E] (μ : FiniteMeasure E) :
    { ν : Measure E // IsRadonMeasure ν } :=
  ⟨μ, isRadonMeasure_of_sigmaCompact μ⟩

@[simp] theorem coe_toRadonMeasure
    {E : Type u} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [SigmaCompactSpace E] [MeasurableSpace E] [BorelSpace E] (μ : FiniteMeasure E) :
    (toRadonMeasure μ : Measure E) = μ :=
  rfl

end FiniteMeasure
end MeasureTheory

/-- Bridge/view topology on the Radon-measure subtype realizing the source-facing vague
convergence notion by `Tendsto`; compare
`tendsto_iff_radonMeasureVaguelyConvergesTo`. -/
@[reducible] def vagueTopology (E : Type u) [TopologicalSpace E] [MeasurableSpace E] :
    TopologicalSpace (RadonMeasureSubtype E) :=
  ⨅ f : C_c(E, ℝ),
    TopologicalSpace.induced (radonVagueIntegral f) inferInstance

instance instTopologicalSpaceRadonMeasureSubtype :
    TopologicalSpace (RadonMeasureSubtype E) :=
  vagueTopology E

variable {X : Type v} [TopologicalSpace X]

-- Proof sketch: unfold `vagueTopology`; continuity into an infimum of induced topologies is
-- equivalent to continuity of each component map `μ ↦ ∫ f dμ`.
/-- A map into `𝓜(E)` is continuous for the vague topology exactly when every compactly supported
continuous test-function integral is continuous. -/
theorem continuous_iff_continuous_vague_integral
    {μs : X → RadonMeasureSubtype E} :
    Continuous μs ↔
      ∀ f : C_c(E, ℝ), Continuous (radonVagueIntegral f ∘ μs) := by
  simp [continuous_iInf_rng, continuous_induced_rng]

variable {μ : RadonMeasureSubtype E} {μs : ℕ → RadonMeasureSubtype E}

-- Proof sketch: `vagueTopology` is the infimum of the induced topologies from the integral maps
-- `μ ↦ ∫ f dμ`, so convergence is equivalent to convergence of every such coordinate map.
/-- Convergence in the vague topology on the Radon-measure subtype is exactly convergence of all
compactly supported continuous test-function integrals. -/
theorem tendsto_iff_forall_vagueIntegral_tendsto :
    Tendsto μs atTop (𝓝 μ) ↔
      ∀ f : C_c(E, ℝ),
        Tendsto (fun n ↦ radonVagueIntegral f (μs n)) atTop
          (𝓝 (radonVagueIntegral f μ)) := by
  rw [show 𝓝 μ = ⨅ f : C_c(E, ℝ), comap (radonVagueIntegral f)
      (𝓝 (radonVagueIntegral f μ)) by
        simp [nhds_iInf, nhds_induced]]
  rw [tendsto_iInf]
  simp [Filter.tendsto_comap_iff, Function.comp_def, radonVagueIntegral]

-- Proof sketch: use local compactness to separate Radon measures by compactly supported
-- continuous test functions, so the induced topology is Hausdorff.
/-- On a locally compact Hausdorff space, the vague topology on `𝓜(E)` is Hausdorff. -/
theorem vagueTopology_t2Space_of_locallyCompact
    [LocallyCompactSpace E] [T2Space E] :
    T2Space (RadonMeasureSubtype E) := sorry

-- Proof sketch: for a locally compact Polish base space, the standard description of the vague
-- topology yields a complete separable metric on Radon measures.
/-- On a locally compact Polish base space, the vague topology on `𝓜(E)` is Polish. -/
theorem vagueTopology_polish_of_locallyCompact
    [LocallyCompactSpace E] [BorelSpace E] [PolishSpace E] :
    PolishSpace (RadonMeasureSubtype E) := sorry

end RadonTopology

section Metric

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

variable {μ : RadonMeasureSubtype E} {μs : ℕ → RadonMeasureSubtype E}

-- Proof sketch: the subtype hypotheses supply the ambient Radon-measure assumptions from
-- Definition 13.12, and `tendsto_iff_forall_vagueIntegral_tendsto` identifies the remaining
-- content with convergence of all compactly supported continuous test-function integrals.
/-- The subtype-based vague topology is a bridge/view realization of the source-facing predicate
`radonMeasureVaguelyConvergesTo`. -/
theorem tendsto_iff_radonMeasureVaguelyConvergesTo :
    Tendsto μs atTop (𝓝 μ) ↔
      radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) := sorry

namespace MeasureTheory
namespace FiniteMeasure

/-- On a `σ`-compact metric Borel space, convergence of the canonical images of finite measures in
the vague topology is exactly the source-facing vague convergence of the underlying measures. -/
theorem tendsto_toRadonMeasure_iff
    {E : Type u} [MetricSpace E] [SigmaCompactSpace E] [MeasurableSpace E] [BorelSpace E]
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E} :
    Tendsto (fun n ↦ toRadonMeasure (μs n)) atTop (𝓝 (toRadonMeasure μ)) ↔
      radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) := by
  simpa using
    (show
        Tendsto (fun n ↦ toRadonMeasure (μs n)) atTop (𝓝 (toRadonMeasure μ)) ↔
          radonMeasureVaguelyConvergesTo
            (fun n ↦ (toRadonMeasure (μs n) : Measure E))
            (toRadonMeasure μ : Measure E) from
      tendsto_iff_radonMeasureVaguelyConvergesTo)

end FiniteMeasure
end MeasureTheory

end Metric
