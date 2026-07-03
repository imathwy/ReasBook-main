import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_13_2_1 (from Items/Chap13) -/
/- Exercise 13.2.1: the textbook metric `d_P` on `𝓜_1(E)` is the canonical distance on
`MeasureTheory.LevyProkhorov (ProbabilityMeasure E)`, and mathlib identifies it with the
auxiliary quantity `levyProkhorovDist` on the underlying probability measures. Together with the
next recall, this yields `d_P(μ, ν) = d_P'(μ, ν) = d_P'(ν, μ)` for all `μ, ν ∈ 𝓜_1(E)`. -/
recall MeasureTheory.LevyProkhorov.dist_probabilityMeasure_def

/- Symmetry of the auxiliary quantity `d_P'` is the canonical theorem
`MeasureTheory.levyProkhorovDist_comm`, specialized to probability measures. -/
recall MeasureTheory.levyProkhorovDist_comm

/-! ### Exercise_13_2_2 (from Items/Chap13) -/
open Filter MeasureTheory
open scoped Topology

noncomputable section

universe u

namespace MeasureTheory.FiniteMeasure

section

variable {E : Type u} [MeasurableSpace E]

variable [MetricSpace E] [BorelSpace E]

omit [MetricSpace E] [BorelSpace E] in
private theorem abs_apply_le_totalVariationNorm {A : Set E} (hA : MeasurableSet A)
    (s : SignedMeasure E) :
    |s A| ≤ SignedMeasure.totalVariationNorm E s := by
  let j := s.toJordanDecomposition
  have hsA : s A = j.posPart.real A - j.negPart.real A := by
    simpa [j, JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hA] using
      (congrArg (fun t : SignedMeasure E ↦ t A)
        (SignedMeasure.toSignedMeasure_toJordanDecomposition s)).symm
  calc
    |s A| = |j.posPart.real A - j.negPart.real A| := by rw [hsA]
    _ ≤ j.posPart.real A + j.negPart.real A := by
      refine abs_sub_le_iff.2 ?_
      constructor <;> linarith [show 0 ≤ j.posPart.real A by positivity,
        show 0 ≤ j.negPart.real A by positivity]
    _ ≤ j.posPart.real Set.univ + j.negPart.real Set.univ := by
      exact add_le_add
        (measureReal_mono (Set.subset_univ A) (by finiteness))
        (measureReal_mono (Set.subset_univ A) (by finiteness))
    _ = SignedMeasure.totalVariationNorm E s := by
      simpa [j] using (SignedMeasure.totalVariation_real_univ_eq_jordan s).symm

-- Proof sketch: first derive setwise convergence on every measurable set from the total-variation
-- bound `|μₙ(A) - μ(A)| ≤ ‖μₙ - μ‖TV`, then invoke the chapter owner theorem
-- `FiniteMeasure.tendsto_of_setwise_tendsto`.
/-- Exercise 13.2.2: convergence to zero in the canonical total-variation norm of signed
differences implies weak convergence in the canonical weak topology on `FiniteMeasure E`. -/
theorem tendsto_of_tendsto_totalVariationNorm_zero
    (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E)
    (h_tv : Tendsto
      (fun n ↦
        SignedMeasure.totalVariationNorm E
          ((μs n : Measure E).toSignedMeasure - (μ : Measure E).toSignedMeasure))
      atTop (𝓝 0)) :
    Tendsto μs atTop (𝓝 μ) := by
  apply tendsto_of_setwise_tendsto
  intro A hA
  have hA_dist :
      Tendsto (fun n ↦ dist ((μs n) A) (μ A)) atTop (𝓝 0) := by
    have hA_le :
        ∀ n,
          dist ((μs n) A) (μ A) ≤
            SignedMeasure.totalVariationNorm E
              ((μs n : Measure E).toSignedMeasure - (μ : Measure E).toSignedMeasure) := by
      intro n
      simpa [NNReal.dist_eq, FiniteMeasure.measureReal_eq_coe_coeFn,
        Measure.toSignedMeasure_sub_apply hA] using
        abs_apply_le_totalVariationNorm hA
          ((μs n : Measure E).toSignedMeasure - (μ : Measure E).toSignedMeasure)
    exact squeeze_zero (fun n ↦ dist_nonneg) hA_le h_tv
  have hA' :
      Tendsto (fun n ↦ ENNReal.ofNNReal ((μs n) A)) atTop
        (𝓝 (ENNReal.ofNNReal (μ A))) :=
    (ENNReal.continuous_coe.tendsto (μ A)).comp (tendsto_iff_dist_tendsto_zero.2 hA_dist)
  simpa [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hA'

end

end MeasureTheory.FiniteMeasure

/-! ### Lemma_13_2 (from Items/Chap13) -/
open Set

universe u

/-- Lemma 13.2: for a subset of a complete metric space realizing the Polish topology, total
boundedness with respect to the metric is equivalent to relative compactness, formalized as
compactness of the closure. -/
-- Proof sketch: If `A` is totally bounded, then `closure A` is again totally bounded; since it is
-- closed in a complete metric space, it is compact. Conversely, a compact closure is totally
-- bounded, and every subset of a totally bounded set is totally bounded.
lemma totallyBounded_iff_isCompact_closure {E : Type u} [MetricSpace E] [CompleteSpace E]
    {A : Set E} : TotallyBounded A ↔ IsCompact (closure A) := by
  rw [← totallyBounded_closure]
  exact ⟨fun hA ↦ hA.isCompact_of_isClosed isClosed_closure, IsCompact.totallyBounded⟩

/-! ### Exercise_13_2_3 (from Items/Chap13) -/
open Filter MeasureTheory
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- The finite measure obtained by restricting Lebesgue measure to the unit interval. -/
def unit_interval_restrict_volume : FiniteMeasure ℝ :=
  ⟨volume.restrict (Set.Icc (0 : ℝ) 1), inferInstance⟩

/-- The canonical uniform empirical distribution on the mesh
`{k / (n + 1) | 0 ≤ k ≤ n + 1}`. -/
noncomputable def unit_interval_mesh_distribution (n : ℕ) : ProbabilityMeasure ℝ :=
  empiricalDistributionTuple (fun k : Fin (Nat.succPNat (n + 1)) ↦ (k : ℝ) / (n + 1 : ℝ))

/-- The empirical finite-measure sequence on the uniform mesh `{k / (n + 1) | 0 ≤ k ≤ n + 1}`.
This keeps the textbook weights `1 / (n + 1)` while deriving the mesh data from the Chapter 12
owner abstraction `empiricalDistributionTuple`. -/
def unit_interval_dirac_riemann_sequence (n : ℕ) : FiniteMeasure ℝ :=
  ((n + 2 : ℝ≥0) / (n + 1 : ℝ≥0)) • (unit_interval_mesh_distribution n).toFiniteMeasure

-- Proof sketch: use `FiniteMeasure.tendsto_iff_forall_integral_tendsto` to test weak convergence
-- against bounded continuous real-valued functions. The resulting integrals are the Riemann sums
-- `(1 / (n + 1)) * ∑_{k=0}^{n+1} f (k / (n + 1))`, which converge to `∫_[0,1] f dλ`; the extra
-- endpoint term is of order `(n + 1)⁻¹` and therefore does not change the limit.
/-- Exercise 13.2.3: after the harmless reindexing `n ↦ n + 1` needed to avoid the undefined term
`1 / 0`, the empirical measures `μₙ = (1 / n) ∑_{k=0}^n δ_{k / n}` converge weakly to Lebesgue
measure restricted to `[0,1]`. -/
theorem unit_interval_dirac_riemann_sequence_tendsto_restrict_volume :
    Tendsto unit_interval_dirac_riemann_sequence atTop (𝓝 unit_interval_restrict_volume) := sorry

/-! ### Exercise_13_2_4 (from Items/Chap13) -/
open Filter MeasureTheory
open scoped CompactlySupported Topology

noncomputable section

/-- The `n`-th truncated Lebesgue measure on `ℝ`, obtained by restricting `volume` to `[-n, n]`. -/
def truncatedLebesgueMeasure (n : ℕ) : Measure ℝ :=
  volume.restrict (Set.Icc (-(n : ℝ)) n)

private theorem isFiniteMeasure_truncatedLebesgueMeasure (n : ℕ) :
    IsFiniteMeasure (truncatedLebesgueMeasure n) := by
  simpa [truncatedLebesgueMeasure] using
    (show IsFiniteMeasure (volume.restrict (Set.Icc (-(n : ℝ)) n)) from inferInstance)

/-- The weak-topology owner view of `truncatedLebesgueMeasure`. -/
def truncatedLebesgueFiniteMeasure (n : ℕ) : FiniteMeasure ℝ :=
  ⟨truncatedLebesgueMeasure n, isFiniteMeasure_truncatedLebesgueMeasure n⟩

-- Proof sketch: if `f` is compactly supported, then its support is contained in some compact
-- interval `[-R, R]`. For all sufficiently large `n`, the restriction of Lebesgue measure to
-- `[-n, n]` agrees with Lebesgue measure on the support of `f`, so the test-function integrals are
-- eventually constant and equal to the integral against `volume`.
/-- Exercise 13.2.4 (1): the restrictions of Lebesgue measure to the symmetric intervals `[-n, n]`
converge vaguely to Lebesgue measure on `ℝ`. -/
theorem truncatedLebesgueMeasures_vaguely_converge :
    radonMeasureVaguelyConvergesTo truncatedLebesgueMeasure volume := sorry

-- Proof sketch: weak convergence of finite measures would force convergence of the integrals of the
-- bounded continuous test function `1`, hence convergence of the total masses. But
-- the finite measure `truncatedLebesgueFiniteMeasure n` has mass `2n`,
-- so the masses diverge and no weak limit in `FiniteMeasure ℝ` can exist.
/-- Exercise 13.2.4 (2): the finite measures obtained by restricting Lebesgue measure to `[-n, n]`
do not converge weakly in the finite-measure topology. -/
theorem truncatedLebesgueMeasures_not_weakly_convergent :
    ¬ ∃ μ : FiniteMeasure ℝ,
      Tendsto truncatedLebesgueFiniteMeasure atTop (𝓝 μ) := sorry

/-! ### Exercise_13_2_5 (from Items/Chap13) -/
open Filter MeasureTheory
open scoped Topology

/- Exercise 13.2.5 splits naturally across the chapter's two convergence layers.
- `source-facing`: vague convergence is stated with `radonMeasureVaguelyConvergesTo`.
- `core/canonical`: weak convergence is stated as `Tendsto ... (𝓝 μ)` on `FiniteMeasure ℝ`.
- `bridge/view`: the weak statement uses the owner embedding
  `ProbabilityMeasure.toFiniteMeasure`, while the canonical Dirac owner theorem is
  `tendsto_diracProba_iff_tendsto`.
The only primitive data here is the Dirac sequence `n ↦ δₙ`, so no extra local wrapper API is
introduced. -/

/-- Exercise 13.2.5 (1): the Dirac masses `δ_n` on `ℝ` converge vaguely to the zero measure, in
the canonical sense of `radonMeasureVaguelyConvergesTo`. -/
-- Proof sketch: test against an arbitrary compactly supported continuous function `f`. Its support
-- is contained in some compact set, hence for all sufficiently large `n` one has `f n = 0`. Since
-- `∫ x, f x ∂Measure.dirac (n : ℝ) = f n`, the integrals are eventually zero and therefore tend to
-- the integral against the zero measure.
theorem dirac_nat_vaguely_converges_to_zero :
    radonMeasureVaguelyConvergesTo (fun n ↦ Measure.dirac (n : ℝ)) 0 := sorry

/-- Exercise 13.2.5 (2): the Dirac masses `δ_n` on `ℝ`, viewed in the owner space
`FiniteMeasure ℝ`, do not converge weakly in its canonical weak topology. -/
-- Proof sketch: any weak limit in `FiniteMeasure ℝ` would, by the owner theorem
-- `ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds`, lift to a weak limit of the
-- probability measures `δ_n`. The canonical Dirac owner theorem
-- `tendsto_diracProba_iff_tendsto` would then force `n ↦ (n : ℝ)` to converge in `ℝ`, which is
-- impossible along `atTop`. Hence no finite weak limit exists.
theorem dirac_nat_not_weakly_convergent :
    ¬ ∃ μ : FiniteMeasure ℝ,
      Tendsto (fun n ↦ (diracProba (n : ℝ)).toFiniteMeasure) atTop (𝓝 μ) := sorry

/-! ### Exercise_13_2_6 (from Items/Chap13) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/- Source-facing layer: the Lévy distance on real distribution functions.
Core owner layer: the Lévy-Prokhorov metric on `ProbabilityMeasure ℝ`.
Bridge layer: pull the owner metric back along the canonical cdf/distribution-function
equivalence `probabilityMeasureEquivDistributionFunction`. -/
private noncomputable def distributionFunctionProbabilityMeasure
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] : ProbabilityMeasure ℝ :=
  probabilityMeasureEquivDistributionFunction.symm ⟨F, inferInstance⟩

private noncomputable def distributionFunctionLevyProkhorov
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] :
    LevyProkhorov (ProbabilityMeasure ℝ) :=
  LevyProkhorov.ofMeasure (distributionFunctionProbabilityMeasure F)

/-- The Lévy distance on real distribution functions is the infimum of the nonnegative radii
`ε` for which `F x` stays between `G (x - ε) - ε` and `G (x + ε) + ε` for every `x`. -/
def levyDistance (F G : StieltjesFunction ℝ) [IsDistributionFunction F] [IsDistributionFunction G] :
    ℝ :=
  sInf {ε : ℝ | 0 ≤ ε ∧ ∀ x : ℝ, G (x - ε) - ε ≤ F x ∧ F x ≤ G (x + ε) + ε}

/-- Unfolding `levyDistance F G` gives the textbook infimum formula for the Lévy distance. -/
theorem levyDistance_def
    (F G : StieltjesFunction ℝ) [IsDistributionFunction F] [IsDistributionFunction G] :
    levyDistance F G =
      sInf {ε : ℝ | 0 ≤ ε ∧ ∀ x : ℝ, G (x - ε) - ε ≤ F x ∧ F x ≤ G (x + ε) + ε} := rfl

private theorem levyDistance_eq_dist_levyProkhorov
    (F G : StieltjesFunction ℝ) [IsDistributionFunction F] [IsDistributionFunction G] :
    levyDistance F G =
      dist (distributionFunctionLevyProkhorov F) (distributionFunctionLevyProkhorov G) := by
  sorry

-- Proof sketch: compare the textbook infimum formula with the canonical Lévy-Prokhorov metric on
-- the corresponding probability measures, then use nonnegativity of the ambient metric distance.
/-- Exercise 13.2.6 (1): Item (i). The Lévy distance is nonnegative on real distribution
functions. -/
theorem levyDistance_nonneg
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G] :
    0 ≤ levyDistance F G := by
  rw [levyDistance_eq_dist_levyProkhorov]
  exact dist_nonneg

-- Proof sketch: identify the textbook Lévy distance with the canonical Lévy-Prokhorov metric, then
-- use the metric-space equality criterion together with injectivity of
-- `probabilityMeasureEquivDistributionFunction.symm`.
/-- Exercise 13.2.6 (2): Item (i). On distribution functions, the Lévy distance vanishes exactly
when the two functions are equal. -/
theorem levyDistance_eq_zero_iff
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G] :
    levyDistance F G = 0 ↔ F = G := by
  constructor
  · intro h
    have h' :
        distributionFunctionLevyProkhorov F = distributionFunctionLevyProkhorov G := by
      apply eq_of_dist_eq_zero
      simpa [levyDistance_eq_dist_levyProkhorov] using h
    exact congrArg Subtype.val <|
      probabilityMeasureEquivDistributionFunction.symm.injective <|
        congrArg LevyProkhorov.toMeasure h'
  · intro h
    subst h
    simp [levyDistance_eq_dist_levyProkhorov]

-- Proof sketch: compare with the canonical Lévy-Prokhorov metric and use symmetry of `dist`.
/-- Exercise 13.2.6 (3): Item (i). The Lévy distance is symmetric on real distribution
functions. -/
theorem levyDistance_comm
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G] :
    levyDistance F G = levyDistance G F := by
  simpa [levyDistance_eq_dist_levyProkhorov] using
    dist_comm (distributionFunctionLevyProkhorov F) (distributionFunctionLevyProkhorov G)

-- Proof sketch: compare with the canonical Lévy-Prokhorov metric and use the ambient triangle
-- inequality.
/-- Exercise 13.2.6 (4): Item (i). The Lévy distance satisfies the triangle inequality on real
distribution functions. -/
theorem levyDistance_triangle
    {F G H : StieltjesFunction ℝ}
    [IsDistributionFunction F] [IsDistributionFunction G] [IsDistributionFunction H] :
    levyDistance F H ≤ levyDistance F G + levyDistance G H := by
  simpa [levyDistance_eq_dist_levyProkhorov] using
    dist_triangle
      (distributionFunctionLevyProkhorov F)
      (distributionFunctionLevyProkhorov G)
      (distributionFunctionLevyProkhorov H)

-- Proof sketch: identify distribution functions with probability measures on `ℝ`, use the bridge
-- theorem `levyDistance_eq_dist_levyProkhorov` to replace the source-facing textbook formula by
-- the canonical Lévy-Prokhorov metric, and then transport the convergence characterization back
-- through `probabilityMeasureEquivDistributionFunction`. In the project the source-facing weak
-- convergence predicate is `distribution_function_weakly_converges_to`.
/-- Exercise 13.2.6 (5): Item (ii). A sequence of real distribution functions converges weakly to
`F` exactly when its Lévy distances to `F` converge to `0`. -/
theorem distribution_function_convergence_iff_levyDistance_tendsto_zero
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ) :
    Π hF : IsDistributionFunction F,
      Π hFs : ∀ n, IsDistributionFunction (Fs n),
        distribution_function_weakly_converges_to Fs F ↔
      Tendsto (fun n ↦ levyDistance (Fs n) F) atTop (𝓝 0) := sorry

-- Proof sketch: approximate `P` by discrete probability measures obtained from quantizing the
-- real line into finer and finer partitions, then show their laws converge weakly to `P`.
/-- Exercise 13.2.6 (6): Item (iii). Every probability measure on `ℝ` is the weak limit of a
sequence of finitely supported probability measures. -/
theorem exists_tendsto_probabilityMeasure_with_finite_support
    (P : ProbabilityMeasure ℝ) :
    ∃ Ps : ℕ → ProbabilityMeasure ℝ,
      (∀ n, ((Ps n : Measure ℝ).support).Finite) ∧
      Tendsto Ps atTop (𝓝 P) := sorry

/-! ### Exercise_13_2_7 (from Items/Chap13) -/
noncomputable section

open Filter MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported Topology unitInterval

universe u

namespace MeasureTheory.SignedMeasure

section General

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Integration of a bounded continuous real-valued test function against a signed measure, via
its Jordan decomposition. This is the signed-measure extension of the weak test-function pairing
from Definition 13.12 (1). -/
def weakIntegral (f : E →ᵇ ℝ) : SignedMeasure E → ℝ :=
  fun φ ↦
    ∫ x, f x ∂φ.toJordanDecomposition.posPart - ∫ x, f x ∂φ.toJordanDecomposition.negPart

omit [BorelSpace E] in
@[simp] theorem weakIntegral_apply (f : E →ᵇ ℝ) (φ : SignedMeasure E) :
    weakIntegral f φ =
      ∫ x, f x ∂φ.toJordanDecomposition.posPart -
        ∫ x, f x ∂φ.toJordanDecomposition.negPart :=
  rfl

/-- Integration of a compactly supported continuous real-valued test function against a signed
measure. This is the signed-measure extension of the vague test-function pairing from
Definition 13.12 (2). -/
def vagueIntegral (f : C_c(E, ℝ)) : SignedMeasure E → ℝ :=
  weakIntegral f.toBoundedContinuousFunction

omit [BorelSpace E] in
@[simp] theorem vagueIntegral_apply (f : C_c(E, ℝ)) (φ : SignedMeasure E) :
    vagueIntegral f φ =
      ∫ x, f x ∂φ.toJordanDecomposition.posPart -
        ∫ x, f x ∂φ.toJordanDecomposition.negPart :=
  rfl

/-- The zero signed measure has zero weak integral against every bounded continuous real-valued
test function. -/
theorem weakIntegral_zero (f : E →ᵇ ℝ) : weakIntegral f 0 = 0 := sorry

/-- A signed measure is Radon when both parts of its Jordan decomposition are Radon measures. This
is the source-facing domain condition for vague convergence of signed measures. -/
def IsRadon (φ : SignedMeasure E) : Prop :=
  IsRadonMeasure φ.toJordanDecomposition.posPart ∧
    IsRadonMeasure φ.toJordanDecomposition.negPart

/-- The weak topology on signed measures is the coarsest topology making integration against every
bounded continuous real-valued test function continuous. -/
@[reducible] def weakTopology (E : Type u) [MetricSpace E] [MeasurableSpace E] [BorelSpace E] :
    TopologicalSpace (SignedMeasure E) :=
  ⨅ f : E →ᵇ ℝ, TopologicalSpace.induced (weakIntegral f) inferInstance

instance instTopologicalSpaceSignedMeasure :
    TopologicalSpace (SignedMeasure E) :=
  weakTopology E

/-- A sequence of signed measures converges weakly when it converges in the owner topology
`SignedMeasure.weakTopology`. -/
def weaklyConvergesTo (φs : ℕ → SignedMeasure E) (φ : SignedMeasure E) : Prop :=
  Tendsto φs atTop (𝓝 φ)

/-- A sequence of signed measures converges weakly exactly when every bounded continuous
real-valued test integral converges. -/
theorem weaklyConvergesTo_iff {φs : ℕ → SignedMeasure E} {φ : SignedMeasure E} :
    weaklyConvergesTo φs φ ↔
      ∀ f : E →ᵇ ℝ,
        Tendsto (fun n ↦ weakIntegral f (φs n)) atTop (𝓝 (weakIntegral f φ)) := by
  simp [weaklyConvergesTo, nhds_iInf, nhds_induced, Filter.tendsto_iInf,
    Filter.tendsto_comap_iff, Function.comp_def]

/-- Weak convergence to the zero signed measure amounts to convergence of every bounded continuous
test integral to `0`. -/
theorem weaklyConvergesTo_zero_iff (φs : ℕ → SignedMeasure E) :
    weaklyConvergesTo φs 0 ↔
      ∀ f : E →ᵇ ℝ, Tendsto (fun n ↦ weakIntegral f (φs n)) atTop (𝓝 0) := by
  constructor
  · intro h f
    simpa [weakIntegral, SignedMeasure.toJordanDecomposition_zero] using
      (weaklyConvergesTo_iff.mp h) f
  · intro h
    exact weaklyConvergesTo_iff.mpr fun f ↦ by
      simpa [weakIntegral, SignedMeasure.toJordanDecomposition_zero] using h f

/-- A sequence of signed measures converges vaguely when both the limit and the whole sequence are
Radon signed measures and all compactly supported continuous real-valued test integrals converge.
This is the signed-measure extension of Definition 13.12 (2). -/
def vaguelyConvergesTo (φs : ℕ → SignedMeasure E) (φ : SignedMeasure E) : Prop :=
  IsRadon φ ∧
    (∀ n, IsRadon (φs n)) ∧
    ∀ f : C_c(E, ℝ), Tendsto (fun n ↦ vagueIntegral f (φs n)) atTop (𝓝 (vagueIntegral f φ))

/- Vague convergence of signed measures means exactly convergence of integrals against all
compactly supported continuous real-valued test functions, together with the ambient Radon signed
measure assumptions on the sequence and its limit. -/
omit [BorelSpace E] in
theorem vaguelyConvergesTo_iff (φs : ℕ → SignedMeasure E) (φ : SignedMeasure E) :
    vaguelyConvergesTo φs φ ↔
      IsRadon φ ∧
        (∀ n, IsRadon (φs n)) ∧
        ∀ f : C_c(E, ℝ),
          Tendsto (fun n ↦ vagueIntegral f (φs n)) atTop (𝓝 (vagueIntegral f φ)) :=
  Iff.rfl

end General

end MeasureTheory.SignedMeasure

section UnitIntervalCounterexample

open MeasureTheory.SignedMeasure

/-- The reciprocal point `1 / (n + 2)` belongs to the closed unit interval. -/
lemma reciprocal_nat_add_two_mem_unit_interval (n : ℕ) :
    (((n : ℝ) + 2)⁻¹) ∈ Set.Icc (0 : ℝ) 1 := sorry

/-- The point `1 / (n + 2)` in the closed unit interval. -/
def reciprocal_unit_interval_point (n : ℕ) : I :=
  ⟨((n : ℝ) + 2)⁻¹, reciprocal_nat_add_two_mem_unit_interval n⟩

/-- The value of `reciprocal_unit_interval_point`. -/
theorem reciprocal_unit_interval_point_val (n : ℕ) :
    ((reciprocal_unit_interval_point n : I) : ℝ) = ((n : ℝ) + 2)⁻¹ :=
  rfl

/-- The point `2 / (n + 2)` belongs to the closed unit interval. -/
lemma double_reciprocal_nat_add_two_mem_unit_interval (n : ℕ) :
    ((2 : ℝ) / ((n : ℝ) + 2)) ∈ Set.Icc (0 : ℝ) 1 := sorry

/-- The point `2 / (n + 2)` in the closed unit interval. -/
def double_reciprocal_unit_interval_point (n : ℕ) : I :=
  ⟨(2 : ℝ) / ((n : ℝ) + 2), double_reciprocal_nat_add_two_mem_unit_interval n⟩

/-- The value of `double_reciprocal_unit_interval_point`. -/
theorem double_reciprocal_unit_interval_point_val (n : ℕ) :
    ((double_reciprocal_unit_interval_point n : I) : ℝ) =
      (2 : ℝ) / ((n : ℝ) + 2) :=
  rfl

/-- The dyadic point `2^{-n}` belongs to the closed unit interval. -/
lemma dyadic_inverse_mem_unit_interval (n : ℕ) :
    (((2 : ℝ) ^ n)⁻¹) ∈ Set.Icc (0 : ℝ) 1 := sorry

/-- The dyadic point `2^{-n}` in the closed unit interval. -/
def dyadic_unit_interval_point (n : ℕ) : I :=
  ⟨((2 : ℝ) ^ n)⁻¹, dyadic_inverse_mem_unit_interval n⟩

/-- The value of `dyadic_unit_interval_point`. -/
theorem dyadic_unit_interval_point_val (n : ℕ) :
    ((dyadic_unit_interval_point n : I) : ℝ) = ((2 : ℝ) ^ n)⁻¹ :=
  rfl

/-- The shifted Dirac-difference sequence used in the signed weak-convergence counterexample on
`[0,1]`. -/
def shifted_point_mass_difference (n : ℕ) : SignedMeasure I :=
  (Measure.dirac (reciprocal_unit_interval_point n)).toSignedMeasure -
    (Measure.dirac (double_reciprocal_unit_interval_point n)).toSignedMeasure

/-- The shifted Dirac-difference sequence is the difference of the two indicated Dirac masses. -/
theorem shifted_point_mass_difference_def (n : ℕ) :
    shifted_point_mass_difference n =
      (Measure.dirac (reciprocal_unit_interval_point n)).toSignedMeasure -
        (Measure.dirac (double_reciprocal_unit_interval_point n)).toSignedMeasure :=
  rfl

/-- Part (i): every fixed rescaling of the shifted Dirac-difference sequence converges weakly to
zero for the signed weak-convergence notion from this exercise. -/
theorem weakly_convergent_rescalings_of_shifted_point_mass_difference {C : ℝ} :
    weaklyConvergesTo (fun n ↦ C • shifted_point_mass_difference n) 0 := sorry

/-- Part (ii): if the weak topology on signed measures over `[0,1]` were metrizable, one could
choose rescaling factors tending to infinity while retaining weak convergence to zero. -/
theorem metrizable_weak_convergence_yields_unbounded_rescalings
    [TopologicalSpace.MetrizableSpace (SignedMeasure I)] :
    ∃ C : ℕ → ℝ,
      Monotone C ∧ Tendsto C atTop atTop ∧ (∀ n, 0 < C n) ∧
        weaklyConvergesTo (fun n ↦ C n • shifted_point_mass_difference n) 0 := sorry

/-- Part (iii): an unbounded positive rescaling sequence admits a bounded continuous real-valued
weak test function on `[0,1]` whose integrals against the rescaled signed measures fail to
converge to `0`. On the compact interval `[0,1]`, this is equivalent to using an ordinary
continuous test function. -/
theorem unbounded_rescalings_admit_obstructing_bounded_continuous_function
    {C : ℕ → ℝ} (hC_pos : ∀ n, 0 < C n) (hC_top : Tendsto C atTop atTop) :
    ∃ f : I →ᵇ ℝ,
      (∀ n, f (dyadic_unit_interval_point n) = (-1 : ℝ) ^ n / Real.sqrt (C n)) ∧
        ¬ Tendsto
          (fun n ↦ weakIntegral f (C n • shifted_point_mass_difference n))
          atTop (𝓝 0) := sorry

/-- Exercise 13.2.7: weak convergence on signed measures over `[0,1]` is not induced by any
metric. -/
theorem weak_convergence_on_signed_measures_over_unit_interval_not_metrizable :
    ¬ TopologicalSpace.MetrizableSpace (SignedMeasure I) := sorry

end UnitIntervalCounterexample

/-! ### Exercise_13_2_8 (from Items/Chap13) -/
open MeasureTheory

universe u

section

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
variable [TopologicalSpace.SeparableSpace E]

/- The first part of Exercise 13.2.8 is that the textbook distance `(13.3)` on `𝓜_1(E)`, which
Exercise 13.2.1 identifies with the Lévy-Prokhorov distance, is a genuine metric on
`ProbabilityMeasure E`. This is the canonical metric-space instance on the type synonym
`LevyProkhorov (ProbabilityMeasure E)`. -/
#check (inferInstance : MetricSpace (LevyProkhorov (ProbabilityMeasure E)))

/- Exercise 13.2.8: after identifying `(13.3)` with the Lévy-Prokhorov distance from Exercise
13.2.1, the induced metric topology on `𝓜_1(E)` is exactly the topology of weak convergence.
This is the canonical theorem `LevyProkhorov.eq_convergenceInDistribution`. -/
recall LevyProkhorov.eq_convergenceInDistribution

end

/-! ### Exercise_13_2_9 (from Items/Chap13) -/
open Filter MeasureTheory Set Topology

universe u

namespace MeasureTheory
namespace FiniteMeasure

section

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]

-- Proof sketch: apply the null-boundary convergence hypothesis to `univ` to get convergence of the
-- total masses. For a closed set `F`, approximate `F` from outside by the closed `r`-neighborhoods
-- and choose radii whose boundaries are `μ`-null; then pass to the limit and let `r ↓ 0`.
/-- Exercise 13.2.9: the null-boundary setwise convergence condition in Theorem 13.16 directly
implies the closed-set Portmanteau condition. -/
theorem closedSetPortmanteauCondition_of_nullBoundarySetwiseTendsto
    (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E)
    (h :
      ∀ A : Set E, MeasurableSet A → μ (frontier A) = 0 →
        Tendsto (fun n ↦ μs n A) atTop (𝓝 (μ A))) :
    μ.mass ≤ liminf (fun n ↦ (μs n).mass) atTop ∧
      ∀ F : Set E, IsClosed F → limsup (fun n ↦ μs n F) atTop ≤ μ F := by
  have hmass : Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) := by
    simpa [FiniteMeasure.mass] using h univ MeasurableSet.univ (by simp)
  refine ⟨(hmass.liminf_eq).symm.le, ?_⟩
  have h' : ∀ {A : Set E}, MeasurableSet A → (μ : Measure E) (frontier A) = 0 →
      Tendsto (fun n ↦ ((μs n : Measure E) A)) atTop (𝓝 ((μ : Measure E) A)) := by
    intro A hA hA0
    have hA0' : μ (frontier A) = 0 := by
      exact ENNReal.coe_eq_zero.mp (by simpa using hA0)
    have hA' : Tendsto (fun n ↦ ENNReal.ofNNReal ((μs n) A)) atTop
        (𝓝 (ENNReal.ofNNReal (μ A))) :=
      (ENNReal.continuous_coe.tendsto (μ A)).comp (h A hA hA0')
    simpa [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hA'
  intro F hF
  have hF' : limsup (fun n ↦ ((μs n : Measure E) F)) atTop ≤ (μ : Measure E) F := by
    exact limsup_measure_closed_le_of_forall_tendsto_measure h' F hF
  have hbounded : atTop.IsBoundedUnder (· ≤ ·) (μs · F) := by
    refine ⟨μ.mass + 1, ?_⟩
    show ∀ᶠ n in atTop, μs n F ≤ μ.mass + 1
    filter_upwards [hmass (Iio_mem_nhds (by simp : μ.mass < μ.mass + 1))] with n hn
    exact le_trans ((μs n).apply_le_mass F) hn.le
  have aux : ENNReal.ofNNReal (limsup (fun n ↦ μs n F) atTop) =
      limsup (ENNReal.ofNNReal ∘ fun n ↦ μs n F) atTop :=
    ENNReal.coe_mono.map_limsup_of_continuousAt (μs · F) ENNReal.continuous_coe.continuousAt
      hbounded ⟨0, by simp⟩
  have hfun : (fun n ↦ ((μs n : Measure E) F)) = ENNReal.ofNNReal ∘ fun n ↦ μs n F := by
    funext n
    simp [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, Function.comp_apply]
  have hF'' : limsup (ENNReal.ofNNReal ∘ fun n ↦ μs n F) atTop ≤ ENNReal.ofNNReal (μ F) := by
    simpa [hfun, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hF'
  have obs : ENNReal.ofNNReal (limsup (fun n ↦ μs n F) atTop) ≤ ENNReal.ofNNReal (μ F) := by
    rw [aux]
    exact hF''
  exact_mod_cast obs

end

end FiniteMeasure
end MeasureTheory

/-! ### Exercise_13_2_10 (from Items/Chap13) -/
open Filter MeasureTheory ProbabilityTheory

universe u

section

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Xn Y : ℕ → Ω → ℝ} {X : Ω → ℝ}
variable
    (hY_law : ∀ n, HasLaw (Y n) (gaussianReal 0 ⟨((n + 1 : ℝ)⁻¹), by positivity⟩) P)

-- Proof sketch: for every `ε > 0`, the event `{ω | ε ≤ |Yₙ ω|}` depends only on the law of `Yₙ`;
-- rewrite its probability using `hY_law n`, identify it with the corresponding Gaussian tail
-- probability for variance `(n + 1)⁻¹`, and show that this tail tends to `0` as the variance
-- shrinks to `0`.
/-- A Gaussian perturbation whose variances are `(n + 1)⁻¹` converges to `0` in probability. -/
theorem gaussian_noise_tendstoInMeasure_zero :
    TendstoInMeasure P Y atTop 0 := sorry

-- Proof sketch: first use `gaussian_noise_tendstoInMeasure_zero` to obtain `Yₙ → 0` in
-- probability. For the forward implication, apply the canonical owner theorem
-- `TendstoInDistribution.add_of_tendstoInMeasure_const` to `Xₙ` and `Yₙ`. For the reverse
-- implication, apply the same theorem to `Xₙ + Yₙ` and `-Yₙ`.
/-- Exercise 13.2.10: with Lean's `0`-based indexing, the textbook Gaussian laws
`\mathcal{N}_{0,1/n}` are represented as `gaussianReal 0 ((n + 1)⁻¹)`. Under this shrinking
Gaussian perturbation, `Xₙ` converges in distribution to `X` if and only if `Xₙ + Yₙ` converges
in distribution to `X`. -/
theorem tendstoInDistribution_iff_add_gaussian_noise :
    TendstoInDistribution Xn atTop X (fun _ ↦ P) P ↔
      TendstoInDistribution (Xn + Y) atTop X (fun _ ↦ P) P := sorry

end

/-! ### Exercise_13_2_11 (from Items/Chap13) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/- Exercise 13.2.11 is source-facing. Its owner abstraction is weak convergence in
`ProbabilityMeasure ℝ`, and the scaled geometric law is the derived pushforward of the geometric
probability measure along `k ↦ k / n`, so no separate public wrapper definition is needed. -/

private noncomputable def geometricProbabilityMeasure (p : ℝ) (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    ProbabilityMeasure ℕ :=
  ⟨geometricMeasure hp_pos (le_of_lt hp_lt_one),
    isProbabilityMeasure_geometricMeasure hp_pos (le_of_lt hp_lt_one)⟩

private noncomputable def expProbabilityMeasure (α : ℝ) (hα : 0 < α) : ProbabilityMeasure ℝ :=
  ⟨expMeasure α, isProbabilityMeasure_expMeasure hα⟩

/-- Exercise 13.2.11: the laws of the scaled geometric variables `Xₙ / n` converge weakly to the
exponential distribution with rate `α` exactly when the success probabilities satisfy
`n * pₙ → α`. -/
-- Proof sketch: view the law of `Xₙ / n` directly as the pushforward of the geometric
-- probability measure under `k ↦ k / n`, compute the associated distribution functions from the
-- explicit geometric and exponential formulas, and use the limit
-- `(1 - pₙ)^(n x) → exp (-α * x)` to show that weak convergence is equivalent to
-- `n * pₙ → α`.
theorem scaled_geometric_law_tendsto_expMeasure_iff
    (α : ℝ) (hα : 0 < α) (p : ℕ+ → ℝ) (hp_pos : ∀ n, 0 < p n)
    (hp_lt_one : ∀ n, p n < 1) :
    Tendsto
      (fun n ↦
        (geometricProbabilityMeasure (p n) (hp_pos n) (hp_lt_one n)).map
          ((measurable_of_countable fun k : ℕ ↦ (k : ℝ) / (n : ℝ)).aemeasurable))
      atTop
      (𝓝 (expProbabilityMeasure α hα)) ↔
    Tendsto (fun n : ℕ+ ↦ (n : ℝ) * p n) atTop (𝓝 α) := sorry

/-! ### Exercise_13_2_12 (from Items/Chap13) -/
open Filter MeasureTheory
open scoped ENNReal Topology

universe u v

section

/- Exercise 13.2.12 is `source-facing`: it keeps the textbook hypotheses and conclusions in terms
of random variables, but its `core/canonical` owner abstraction is weak convergence of their laws,
accessed here through `MeasureTheory.TendstoInDistribution`. The chapter-level bridge is
`tendstoInDistribution_iff_tendsto_limit_law`, and the lower-semicontinuity input for item `(i)`
is the Portmanteau lintegral theorem
`lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`. The moment
expressions are therefore derived from the law-level owner API, not additional primitive data. -/

variable {Ω : ℕ → Type u} {Ω' : Type v}
variable {m : ∀ n, MeasurableSpace (Ω n)} {m' : MeasurableSpace Ω'}
variable {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
variable {μ' : Measure Ω'} [IsProbabilityMeasure μ']
variable {X : (n : ℕ) → Ω n → ℝ} {Z : Ω' → ℝ}

-- Proof sketch: apply the portmanteau lower-semicontinuity inequality to the nonnegative lower
-- semicontinuous test function `x ↦ |x|`, written as an `ENNReal`-valued lower integral of the
-- laws of the random variables.
/-- Exercise 13.2.12 (1): Item (i). Under convergence in distribution, the first absolute moment
of the limit is bounded above by the liminf of the first absolute moments of the approximating
random variables, interpreted as nonnegative extended expectations. -/
theorem lintegral_abs_le_liminf_of_tendstoInDistribution
    (hXZ : TendstoInDistribution X atTop Z μ μ') :
    ∫⁻ ω, ENNReal.ofReal |Z ω| ∂μ' ≤
      liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal |X n ω| ∂μ n) atTop := sorry

-- Proof sketch: first apply the continuous mapping theorem to `x ↦ |x| ^ p` to obtain
-- convergence in distribution of the `p`-th absolute powers, then use the uniform `r`-moment
-- bound with `r > p` to get uniform integrability and conclude convergence of the corresponding
-- moments by Vitali/portmanteau.
/-- Exercise 13.2.12 (2): Item (ii). If `0 < p < r` and the `r`-th absolute moments are
uniformly bounded, then the `p`-th absolute moments converge along the distributional limit,
again in the extended nonnegative sense. -/
theorem tendsto_lintegral_abs_rpow_of_tendstoInDistribution_of_bounded_moment
    {p r : ℝ} (hp : 0 < p) (hpr : p < r)
    (hXZ : TendstoInDistribution X atTop Z μ μ')
    (hbound : sSup (Set.range fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ r) ∂μ n) < ⊤) :
    Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ p) ∂μ n) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (|Z ω| ^ p) ∂μ')) := sorry

end

/-! ### Exercise_13_2_13 (from Items/Chap13) -/
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace StieltjesFunction

/-- The left-continuous inverse, or quantile function, of a real distribution function. It is
defined by the infimum of the superlevel set `{x | u ≤ F x}`. -/
def leftInverse (F : StieltjesFunction ℝ) (u : ℝ) : ℝ :=
  sInf {x : ℝ | u ≤ F x}

-- Proof sketch: if `u ≤ v`, then the superlevel set `{x | v ≤ F x}` is contained in
-- `{x | u ≤ F x}`. Taking infima of these nested superlevel sets yields monotonicity on `(0,1)`.
/-- The left-continuous inverse of a distribution function is monotone on the open unit interval.
-/
theorem monotoneOn_leftInverse
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] :
    MonotoneOn F.leftInverse (Ioo (0 : ℝ) 1) := sorry

-- Proof sketch: apply the standard theorem that a monotone real function has at most countably
-- many discontinuities, restricted to the interval `(0,1)`, to the monotone quantile function.
/-- The left-continuous inverse of a distribution function is continuous for Lebesgue-almost every
parameter `u ∈ (0,1)`. -/
theorem ae_continuousWithinAt_leftInverse
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] :
    ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ContinuousWithinAt F.leftInverse (Ioo (0 : ℝ) 1) u := sorry

end StieltjesFunction

section

open StieltjesFunction

variable {Fs : ℕ → StieltjesFunction ℝ} {F : StieltjesFunction ℝ}

-- Proof sketch: combine the continuity-point convergence encoded in
-- `distribution_function_weakly_converges_to` with the defining infimum formula for the
-- left-continuous inverses. Continuity of the limit inverse at `u` lets the two-sided squeezing
-- argument for quantiles pass to the limit.
/-- Exercise 13.2.13 (1): if distribution functions `Fₙ` converge weakly to `F`, then their
left-continuous inverses converge at every continuity point of the limit inverse on `(0,1)`. -/
theorem tendsto_leftInverse_of_weak_convergence :
    Π hF : IsDistributionFunction F,
      Π hFs : ∀ n, IsDistributionFunction (Fs n),
        distribution_function_weakly_converges_to Fs F →
        {u : ℝ} →
          (hu : u ∈ Ioo (0 : ℝ) 1) →
          (hcont : ContinuousWithinAt F.leftInverse (Ioo (0 : ℝ) 1) u) →
          Tendsto (fun n ↦ (Fs n).leftInverse u) atTop (𝓝 (F.leftInverse u)) := sorry

-- Proof sketch: by the previous theorem, convergence of the inverses fails only at points where
-- the limit inverse is discontinuous. The exceptional set is Lebesgue-null because the quantile
-- function is monotone on `(0,1)`.
/-- Exercise 13.2.13 (2): consequently, the left-continuous inverses converge for
Lebesgue-almost every `u ∈ (0,1)`. -/
theorem ae_tendsto_leftInverse_of_weak_convergence :
    Π hF : IsDistributionFunction F,
      Π hFs : ∀ n, IsDistributionFunction (Fs n),
        distribution_function_weakly_converges_to Fs F →
    ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Tendsto (fun n ↦ (Fs n).leftInverse u) atTop (𝓝 (F.leftInverse u)) := sorry

end

/-! ### Exercise_13_2_14 (from Items/Chap13) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

universe u

-- Proof sketch: this is the one-dimensional specialization of the canonical Skorohod-coupling
-- theorem from Chapter 17.
/-- Exercise 13.2.14: if probability measures `μs n` on `ℝ` converge weakly to `μ`, then there
exists a probability space carrying real random variables with laws `μ` and `μs n` whose sample
paths converge almost surely to the limit random variable. -/
theorem exists_real_skorokhod_representation_of_tendsto
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hweak : Tendsto μs atTop (𝓝 μ)) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (X : Ω → ℝ) (Xs : ℕ → Ω → ℝ),
      HasLaw X (μ : Measure ℝ) (P : Measure Ω) ∧
        (∀ n : ℕ, HasLaw (Xs n) (μs n : Measure ℝ) (P : Measure Ω)) ∧
        (∀ᵐ ω ∂(P : Measure Ω), Tendsto (fun n ↦ Xs n ω) atTop (𝓝 (X ω))) := by
  simpa using exists_skorohod_coupling μ μs hweak

/-! ### Exercise_13_2_15 (from Items/Chap13) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

universe u v

section LawLevel

variable {E : Type u} [MeasurableSpace E]

/- Exercise 13.2.15 is `source-facing`: the textbook assumption is a tail-first-moment condition
for one fixed observable `f` tested against a sequence of laws `μₙ`. The `core/canonical` owner
used downstream is `MeasureTheory.UniformIntegrable` on a single measure space. The local
predicate below is therefore the law-level `bridge/view`, while the bridge theorem records the
canonical reformulation through any common-space realization with the same one-dimensional laws. -/
/-- A real-valued function is uniformly integrable with respect to a sequence of probability
measures when the supremum of its tail first moments tends to `0`, written in the textbook form as
an infimum over positive cutoffs. -/
def uniformlyIntegrableWithRespectToProbabilitySequence
    (f : E → ℝ) (μs : ℕ → ProbabilityMeasure E) : Prop :=
  (⨅ a : {a : ℝ // 0 < a},
      ⨆ n : ℕ,
        ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E)) = 0

-- Proof sketch: compare the tail integrals under `μₙ` with those of any common-space real
-- sequence having the same one-dimensional laws, using `IdentDistrib` to transport the relevant
-- truncated first moments. In the exercise proof, the needed realization comes from a Skorohod
-- coupling of the pushforward laws, but that auxiliary convergence package is not part of the
-- bridge API itself.
/-- The law-level tail criterion for `f` along `μₙ` is equivalent to the canonical owner
predicate `MeasureTheory.UniformIntegrable` for any real sequence with the same one-dimensional
laws. -/
theorem uniformlyIntegrableWithRespectToProbabilitySequence_iff_uniformIntegrable_of_identDistrib
    {Ω : Type v} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω}
    {f : E → ℝ} {μs : ℕ → ProbabilityMeasure E} {Ys : ℕ → Ω → ℝ}
    (hYs : ∀ n, IdentDistrib (Ys n) f (P : Measure Ω) (μs n : Measure E)) :
    uniformlyIntegrableWithRespectToProbabilitySequence f μs ↔
      UniformIntegrable Ys 1 (P : Measure Ω) := sorry

end LawLevel

section

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

-- Proof sketch: apply Exercise 13.2.14 to the pushforward probability measures `μₙ ∘ f⁻¹` on
-- `ℝ`, then use
-- `uniformlyIntegrableWithRespectToProbabilitySequence_iff_uniformIntegrable_of_identDistrib`
-- with the induced `IdentDistrib` family from the Skorohod realization to pass to the owner
-- predicate `UniformIntegrable` on the coupling space. The one-dimensional result yields
-- integrability of the limit law and convergence of first moments, which translate back to
-- integrability of `f` under `μ` and convergence of `∫ f dμₙ`.
/-- Exercise 13.2.15: if `f` is continuous, uniformly integrable with respect to the probability
measures `μₙ`, and `μₙ` converges weakly to `μ`, then `f` is integrable under `μ` and the
integrals `∫ f dμₙ` converge to `∫ f dμ`. -/
theorem integrable_and_tendsto_integral_of_continuous_of_uniformlyIntegrableProbabilitySequence
    {f : E → ℝ} {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hf_cont : Continuous f)
    (hf_ui : uniformlyIntegrableWithRespectToProbabilitySequence f μs)
    (hμs : Tendsto μs atTop (𝓝 μ)) :
    Integrable f (μ : Measure E) ∧
      Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
        (𝓝 (∫ x, f x ∂(μ : Measure E))) := sorry

end
