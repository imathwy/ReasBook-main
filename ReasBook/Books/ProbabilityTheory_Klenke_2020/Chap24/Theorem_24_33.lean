import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u v

namespace ProbabilityTheory

local instance : TopologicalSpace (ℕ → ℝ) := inferInstance
local instance : MeasurableSpace (ℕ → ℝ) := inferInstance
local instance : OpensMeasurableSpace (ℕ → ℝ) := inferInstance

/-- A finite stick-breaking input vector extended by the terminal value `1`. -/
def gemExtendWithTerminalOne {n : ℕ} (v : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases (1 : ℝ) v

-- Proof sketch: unfold `gemExtendWithTerminalOne`; it is defined by `Fin.lastCases`, so it agrees
-- with `v` on the nonterminal coordinates and takes the value `1` at the terminal coordinate.
/-- The extension used for finite GEM stick breaking is obtained by adjoining the terminal value
`1` to the input vector. -/
theorem gemExtendWithTerminalOne_def {n : ℕ} (v : Fin n → ℝ) :
    gemExtendWithTerminalOne v = Fin.lastCases (1 : ℝ) v := sorry

/-- The finite stick-breaking map sending break proportions, with a terminal factor already
included, to the associated mass vector. -/
def finiteGemStickBreakingMap {n : ℕ} (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i ↦ (∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) ↦ j < i), (1 - v j)) * v i

-- Proof sketch: unfold `finiteGemStickBreakingMap`; the `i`th mass is defined as the product of
-- the earlier residual factors `1 - v j` multiplied by the `i`th break proportion.
/-- The finite stick-breaking mass at coordinate `i` is the product of all previous residual
factors times the `i`th break proportion. -/
theorem finiteGemStickBreakingMap_apply {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    finiteGemStickBreakingMap v i =
      (∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) ↦ j < i), (1 - v j)) * v i := sorry

/-- The infinite stick-breaking map associated with a sequence of break proportions on `[0,1]`. -/
def gemStickBreaking (v : ℕ → ℝ) : ℕ → ℝ :=
  fun k ↦ (Finset.prod (Finset.range k) fun i ↦ (1 - v i)) * v k

-- Proof sketch: unfold `gemStickBreaking`; the `k`th coordinate is defined by multiplying the
-- residual factors from the previous breaks and then taking the `k`th break proportion.
/-- The `k`th GEM stick-breaking mass is the product of the previous residual factors times the
`k`th break proportion. -/
theorem gemStickBreaking_apply (v : ℕ → ℝ) (k : ℕ) :
    gemStickBreaking v k = (Finset.prod (Finset.range k) fun i ↦ (1 - v i)) * v k := sorry

/-- The canonical `GEM_θ` law, obtained by mapping an i.i.d. `Beta(1, θ)` sequence through the
infinite stick-breaking map. -/
def gemMeasure (θ : ℝ) : Measure (ℕ → ℝ) :=
  Measure.map gemStickBreaking (Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 θ)

-- Proof sketch: unfold `gemMeasure`; by definition it is the pushforward of the i.i.d.
-- `Beta(1, θ)` product law under `gemStickBreaking`.
/-- The `GEM_θ` law is the pushforward of the product `Beta(1, θ)` measure by the infinite
stick-breaking map. -/
theorem gemMeasure_def (θ : ℝ) :
    gemMeasure θ =
      Measure.map gemStickBreaking (Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 θ) := sorry

/-- The finite Beta product measure appearing in the size-biased stick-breaking representation of
the symmetric Dirichlet law with parameter `θ / (n + 1)` on `n + 1` coordinates. -/
def finiteSizeBiasedDirichletInputMeasure (θ : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun i : Fin n ↦
    betaMeasure (1 + θ / (n + 1 : ℝ)) (θ * ((n - i.1 : ℝ) / (n + 1 : ℝ)))

-- Proof sketch: unfold `finiteSizeBiasedDirichletInputMeasure`; it is exactly the product of the
-- Beta laws with parameters `1 + θ/(n+1)` and `θ (n-i)/(n+1)`.
/-- The finite size-biased Dirichlet input law is the product of the Beta measures from the
stick-breaking representation of `Dir_{θ/(n+1);\,n+1}`. -/
theorem finiteSizeBiasedDirichletInputMeasure_def (θ : ℝ) (n : ℕ) :
    finiteSizeBiasedDirichletInputMeasure θ n =
      Measure.pi fun i : Fin n ↦
        betaMeasure (1 + θ / (n + 1 : ℝ)) (θ * ((n - i.1 : ℝ) / (n + 1 : ℝ))) := sorry

/-- The finite stick-breaking sequence built from the Beta inputs for the size-biased order of the
symmetric Dirichlet law on `n + 1` coordinates, extended by zeros after coordinate `n`. -/
def finiteSizeBiasedDirichletStickBreaking (n : ℕ) (v : Fin n → ℝ) : ℕ → ℝ :=
  fun k ↦
    if hk : k < n + 1 then
      finiteGemStickBreakingMap (gemExtendWithTerminalOne v) ⟨k, hk⟩
    else
      0

-- Proof sketch: unfold `finiteSizeBiasedDirichletStickBreaking`; below the cutoff `n + 1` it is
-- the finite stick-breaking map with terminal value `1`, and afterwards it is zero.
/-- The finite size-biased Dirichlet stick-breaking sequence agrees with the finite
stick-breaking map on the first `n + 1` coordinates and vanishes afterwards. -/
theorem finiteSizeBiasedDirichletStickBreaking_apply
    (n : ℕ) (v : Fin n → ℝ) (k : ℕ) :
    finiteSizeBiasedDirichletStickBreaking n v k =
      if hk : k < n + 1 then
        finiteGemStickBreakingMap (gemExtendWithTerminalOne v) ⟨k, hk⟩
      else
        0 := sorry

/-- The law on `ℕ → ℝ` obtained by applying the finite size-biased Dirichlet stick-breaking map to
its Beta input measure. -/
def finiteSizeBiasedDirichletLaw (θ : ℝ) (n : ℕ) : Measure (ℕ → ℝ) :=
  Measure.map (finiteSizeBiasedDirichletStickBreaking n) (finiteSizeBiasedDirichletInputMeasure θ n)

-- Proof sketch: unfold `finiteSizeBiasedDirichletLaw`; by definition it is the pushforward of the
-- finite Beta input law under `finiteSizeBiasedDirichletStickBreaking`.
/-- The finite size-biased Dirichlet law is the pushforward of the corresponding finite Beta input
measure under the finite stick-breaking map. -/
theorem finiteSizeBiasedDirichletLaw_def (θ : ℝ) (n : ℕ) :
    finiteSizeBiasedDirichletLaw θ n =
      Measure.map (finiteSizeBiasedDirichletStickBreaking n)
        (finiteSizeBiasedDirichletInputMeasure θ n) := sorry

-- Proof sketch: each factor in the product measure is a Beta probability measure when `θ > 0`,
-- and products of probability measures are probability measures.
/-- The finite Beta input measure for the size-biased Dirichlet stick-breaking construction is a
probability measure when `θ > 0`. -/
instance instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure
    (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    IsProbabilityMeasure (finiteSizeBiasedDirichletInputMeasure θ n) := sorry

-- Proof sketch: `finiteSizeBiasedDirichletLaw θ n` is a pushforward of the finite Beta input
-- probability measure, and pushforwards preserve total mass.
/-- The finite size-biased Dirichlet stick-breaking law is a probability measure when `θ > 0`. -/
instance instIsProbabilityMeasureFiniteSizeBiasedDirichletLaw
    (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    IsProbabilityMeasure (finiteSizeBiasedDirichletLaw θ n) := sorry

-- Proof sketch: `gemMeasure θ` is the pushforward of a countable product of `Beta(1, θ)`
-- probability measures, hence it is again a probability measure when `θ > 0`.
/-- The `GEM_θ` law is a probability measure for `θ > 0`. -/
instance instIsProbabilityMeasureGemMeasure (θ : ℝ) (hθ : 0 < θ) :
    IsProbabilityMeasure (gemMeasure θ) := sorry

/-- The canonical `GEM_θ` law viewed as a probability measure. -/
def gemProbabilityMeasure (θ : ℝ) (hθ : 0 < θ) : ProbabilityMeasure (ℕ → ℝ) :=
  ⟨gemMeasure θ, instIsProbabilityMeasureGemMeasure θ hθ⟩

-- Proof sketch: unfold `gemProbabilityMeasure`; it is the probability-measure packaging of
-- `gemMeasure θ` using the canonical probability instance.
/-- The underlying measure of `gemProbabilityMeasure θ hθ` is `gemMeasure θ`. -/
theorem gemProbabilityMeasure_toMeasure (θ : ℝ) (hθ : 0 < θ) :
    (gemProbabilityMeasure θ hθ : Measure (ℕ → ℝ)) = gemMeasure θ := sorry

/-- The finite size-biased Dirichlet stick-breaking law viewed as a probability measure. -/
def finiteSizeBiasedDirichletProbabilityMeasure
    (θ : ℝ) (hθ : 0 < θ) (n : ℕ) : ProbabilityMeasure (ℕ → ℝ) :=
  ⟨finiteSizeBiasedDirichletLaw θ n, instIsProbabilityMeasureFiniteSizeBiasedDirichletLaw θ hθ n⟩

-- Proof sketch: unfold `finiteSizeBiasedDirichletProbabilityMeasure`; it is the
-- probability-measure packaging of `finiteSizeBiasedDirichletLaw θ n`.
/-- The underlying measure of `finiteSizeBiasedDirichletProbabilityMeasure θ hθ n` is the finite
size-biased Dirichlet stick-breaking law. -/
theorem finiteSizeBiasedDirichletProbabilityMeasure_toMeasure
    (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    (finiteSizeBiasedDirichletProbabilityMeasure θ hθ n : Measure (ℕ → ℝ)) =
      finiteSizeBiasedDirichletLaw θ n := sorry

variable {Ω : Type u} [MeasurableSpace Ω]
variable {Ω' : Type v} [MeasurableSpace Ω']

-- Proof sketch: use the convergence of the Beta parameters
-- `Beta(1 + θ/(n+1), θ (n-i)/(n+1)) ⇒ Beta(1, θ)` for each fixed coordinate, combine this with
-- independence of the product input laws, and then apply the continuous mapping theorem to the
-- finite and infinite stick-breaking maps.
/-- Theorem 24.33 (1): the laws of the explicit Beta stick-breaking sequences for the size-biased
order of `Dir_{θ/(n+1);\,n+1}` converge to the limiting `GEM_θ` law; equivalently, the
size-biased reorderings `\widehat X^{\,n}` converge in distribution to the size-biased order of
a `PD_θ` sample once that limit is identified. -/
theorem sizeBiasedSymmetricDirichletLaw_tendsto_gemMeasure
    (θ : ℝ) (hθ : 0 < θ) :
    Tendsto
      (fun n ↦ finiteSizeBiasedDirichletProbabilityMeasure θ hθ n)
      atTop
      (nhds (gemProbabilityMeasure θ hθ)) := sorry

-- Proof sketch: identify the law of the whole Beta input sequence `(V i)_i` with the infinite
-- product `Beta(1, θ)` measure using independence and the coordinate laws, then compose with the
-- measurable stick-breaking map.
/-- An i.i.d. family of `Beta(1, θ)` random variables has the `GEM_θ` law after applying the
infinite stick-breaking map. -/
theorem hasLaw_gemStickBreaking_of_iid_beta
    (θ : ℝ)
    {P : Measure Ω'} [IsProbabilityMeasure P]
    {V : ℕ → Ω' → ℝ}
    (hV_indep : iIndepFun V P)
    (hV_law : ∀ i : ℕ, HasLaw (V i) (betaMeasure 1 θ) P) :
    HasLaw (fun ω ↦ gemStickBreaking (fun i ↦ V i ω)) (gemMeasure θ) P := sorry

-- Proof sketch: first show that the stick-breaking sequence built from the i.i.d. Beta family has
-- law `gemMeasure θ` by identifying the law of the whole input sequence with the product
-- `Beta(1, θ)` measure; then use `HasLaw.identDistrib` to compare it with `Xhat`.
/-- Theorem 24.33 (2): if `X̂` has the limiting `GEM_θ` law and `Z` is the stick-breaking
sequence built from i.i.d. `Beta(1, θ)` variables, then `X̂` and `Z` are identically
distributed; this is the distributional identification `X̂ \overset{\mathcal D}= Z`. -/
theorem identDistrib_gemStickBreaking_of_hasLaw_gemMeasure
    (θ : ℝ)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {P : Measure Ω'} [IsProbabilityMeasure P]
    {Xhat : Ω → ℕ → ℝ} {V : ℕ → Ω' → ℝ}
    (hXhat : HasLaw Xhat (gemMeasure θ) μ)
    (hV_indep : iIndepFun V P)
    (hV_law : ∀ i : ℕ, HasLaw (V i) (betaMeasure 1 θ) P) :
    IdentDistrib Xhat (fun ω ↦ gemStickBreaking (fun i ↦ V i ω)) μ P := sorry

end ProbabilityTheory
