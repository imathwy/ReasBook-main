import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_17_3_1 (from Items/Chap17) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Domain-style sampling for Exercise 17.3.1:
- `weightedUrnPrefixEvent` and `blackPrefixCount` in `Exercise_17_3_2` are the Chapter 17
  primitive prefix-event and black-count declarations for Boolean-valued urn words.
- `IsGeneralizedPolyaUrnWithWeights` in `Exercise_17_3_2` is the nearby owner abstraction for the
  symmetric weighted urn with one common weight sequence. It is relevant domain style, but it is
  not the exact owner here because Exercise 17.3.1 has separate constant reinforcement parameters
  `r` and `s` for red and black draws and asks about the literal fraction of black balls in the
  urn.
- `IsConditionallyBernoulliIID` in `Example_12_3` is the canonical Chapter 12 bridge for a
  Bernoulli directing parameter.

Best owner abstraction:
- this file remains `source-facing`: the public owner is the constant-reinforcement generalized
  two-color urn with initial red/black counts `R`,`S` and reinforcement parameters `r`,`s`,
  encoded by the actual next-draw law coming from the current urn counts;
- `weightedUrnPrefixEvent` and `blackPrefixCount` are reused as the primitive prefix API instead
  of duplicated locally;
- `IsConditionallyBernoulliIID` is a downstream `bridge/view` consequence of this owner, not a
  replacement for it.

Primitive data:
- the measure `μ`, the initial red and black counts `R`,`S`, the constant reinforcement
  parameters `r`,`s`, and the `{0,1}`-valued draw process `X`.

Derived API:
- coordinate measurability and the one-step cylinder-probability formula are accessors of the
  owner abstraction;
- the fraction of black balls is the literal urn fraction
  `(S + s * L_n) / (R + S + r * (n - L_n) + s * L_n)`, where `L_n` is the black draw count in the
  first `n` draws;
- the Beta-law, conditional Bernoulli description, and almost-sure convergence statements are kept
  as source-facing exercise conclusions over that owner.
-/

/-- The source-facing fraction of black balls in the urn after the first `n` draws. If
`L_n(ω)` is the number of black draws among `X 0 ω, …, X (n - 1) ω`, then the urn contains
`S + s * L_n(ω)` black balls and `R + r * (n - L_n(ω))` red balls. -/
noncomputable def generalizedPolyaUrnBlackBallFraction
    (R S r s : ℕ) (X : ℕ → Ω → Bool) (n : ℕ) (ω : Ω) : ℝ :=
  let ℓ := blackPrefixCount (fun i : Fin n ↦ X i ω)
  (((S + s * ℓ : ℕ) : ℝ) / ((R + S + r * (n - ℓ) + s * ℓ : ℕ) : ℝ))

/-- A `{0,1}`-valued process is the constant-reinforcement generalized two-color Pólya urn with
initial red/black counts `R`,`S` and reinforcement parameters `r`,`s` if every coordinate is
measurable and, after a prefix `x` of length `n` with `ℓ` black draws, the next draw is black
with probability equal to the actual fraction of black balls currently present in the urn,
namely `(S + s * ℓ) / (R + S + r * (n - ℓ) + s * ℓ)`. -/
def IsGeneralizedPolyaUrn
    (μ : Measure Ω) (R S r s : ℕ) (X : ℕ → Ω → Bool) : Prop :=
  (∀ n : ℕ, Measurable (X n)) ∧
    ∀ ⦃n : ℕ⦄ (x : Fin n → Bool),
      let ℓ := blackPrefixCount x
      μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
        ((((S + s * ℓ : ℕ) : NNReal) /
            ((R + S + r * (n - ℓ) + s * ℓ : ℕ) : NNReal)) : ℝ≥0∞) *
          μ (weightedUrnPrefixEvent X x)

namespace IsGeneralizedPolyaUrn

variable {μ : Measure Ω} {R S r s : ℕ} {X : ℕ → Ω → Bool}

/-- Every coordinate of a constant-reinforcement generalized Pólya urn is measurable. -/
theorem measurable
    (hX : IsGeneralizedPolyaUrn μ R S r s X) (n : ℕ) :
    Measurable (X n) :=
  hX.1 n

/-- The defining one-step cylinder probability formula of the literal generalized Pólya urn. -/
theorem prefixEvent_inter_true_eq
    (hX : IsGeneralizedPolyaUrn μ R S r s X) {n : ℕ} (x : Fin n → Bool) :
    let ℓ := blackPrefixCount x
    μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
      ((((S + s * ℓ : ℕ) : NNReal) /
          ((R + S + r * (n - ℓ) + s * ℓ : ℕ) : NNReal)) : ℝ≥0∞) *
        μ (weightedUrnPrefixEvent X x) :=
  hX.2 x

/-- Exercise 17.3.1: the generalized urn admits a directing random parameter `Z ∈ [0,1]` such
that, conditionally on `Z`, the draws are i.i.d. Bernoulli with parameter `Z`. -/
theorem exists_conditionalBernoulliParameter
    [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    (hX : IsGeneralizedPolyaUrn μ R S r s X) :
    ∃ Z : Ω → unitInterval,
      IsConditionallyBernoulliIID Z X μ := sorry

end IsGeneralizedPolyaUrn

/-- Exercise 17.3.1: the directing parameter of the generalized Pólya urn has Beta law with the
parameters determined by the initial counts and constant reinforcements. -/
theorem generalizedPolyaUrn_limit_hasLaw_beta
    {μ : Measure Ω} [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    {X : ℕ → Ω → Bool}
    {R S r s : ℕ} (hX : IsGeneralizedPolyaUrn μ R S r s X)
    (hR : 0 < R) (hS : 0 < S) (hr : 0 < r) (hs : 0 < s) :
    ∃ Z : Ω → unitInterval,
      IsConditionallyBernoulliIID Z X μ ∧
        HasLaw (fun ω ↦ (Z ω : ℝ))
          (betaMeasure ((S : ℝ) / (s : ℝ)) ((R : ℝ) / (r : ℝ))) μ := sorry

/-- Exercise 17.3.1: the actual fraction of black balls in the urn converges almost surely to a
Beta-distributed directing random variable `Z`, and conditionally on `Z` the draw sequence is
i.i.d. Bernoulli with parameter `Z`. -/
theorem generalizedPolyaUrn_blackBallFraction_ae_tendsto_limit
    {μ : Measure Ω} [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    {X : ℕ → Ω → Bool}
    {R S r s : ℕ} (hX : IsGeneralizedPolyaUrn μ R S r s X)
    (hR : 0 < R) (hS : 0 < S) (hr : 0 < r) (hs : 0 < s) :
    ∃ Z : Ω → unitInterval,
      IsConditionallyBernoulliIID Z X μ ∧
        HasLaw (fun ω ↦ (Z ω : ℝ))
          (betaMeasure ((S : ℝ) / (s : ℝ)) ((R : ℝ) / (r : ℝ))) μ ∧
        ∀ᵐ ω ∂μ,
          Tendsto (fun n ↦ generalizedPolyaUrnBlackBallFraction R S r s X n ω) atTop
            (𝓝 (Z ω : ℝ)) := sorry

/-- At time `0`, the black-ball fraction is the initial proportion `S / (R + S)`. -/
@[simp] theorem generalizedPolyaUrnBlackBallFraction_zero
    {Ω' : Type u} [MeasurableSpace Ω']
    (R S r s : ℕ) (X : ℕ → Ω' → Bool) (ω : Ω') :
    generalizedPolyaUrnBlackBallFraction R S r s X 0 ω =
      (S : ℝ) / ((R + S : ℕ) : ℝ) := by
  simp [generalizedPolyaUrnBlackBallFraction]

/-! ### Exercise_17_3_2 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

universe u

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/- 
Domain-style sampling for Exercise 17.3.2:
- `IsExchangeable` in Chapter 12 is the source-facing owner for exchangeable sequences.
- `IsConditionallyBernoulliIID` in `Example_12_3` is the canonical Bernoulli-mixture bridge used
  for `{0,1}`-valued processes.
- `exists_conditionalBernoulliParameter_of_isExchangeable` in `Example_12_28` is the owner-level
  bridge from exchangeability to a Bernoulli directing parameter.
- `weightedUrnClockLaw` and `weightedUrnClockLaw_ae_eventually_single_color` in `Example_17_27`
  are the source-facing exponential-clock realization of the weighted Pólya urn.

Best owner abstraction:
- this file remains `source-facing`: `IsGeneralizedPolyaUrnWithWeights` is the owner for the
  textbook cylinder-probability specification of the generalized weighted urn process;
- the exponential-clock construction from Example 17.27 is a `bridge/view` under stronger
  realization hypotheses, not a replacement for this owner.

Primitive data:
- the ambient measure `μ`, the weight sequence `w`, and the `{0,1}`-valued process `X`.

Derived API:
- coordinate measurability and the one-step cylinder-probability formula are derived accessors of
  `IsGeneralizedPolyaUrnWithWeights`, not separate owner declarations.
-/

/-- The cylinder event that the first `n` draws of the urn process `X` match the prescribed
black/red pattern `x`, with `true` encoding a black draw and `false` a red draw. -/
def weightedUrnPrefixEvent (X : ℕ → Ω → Bool) {n : ℕ} (x : Fin n → Bool) : Set Ω :=
  {ω | ∀ i : Fin n, X i ω = x i}

/-- The number of black draws in a finite prefix `x`, where `true` encodes black. -/
def blackPrefixCount {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ x i = true).card

/-- A `{0,1}`-valued process is the generalized two-color Pólya urn from Example 17.27 with
weight sequence `w` if every coordinate is measurable and each one-step cylinder probability is
given by the ratio `w_ℓ / (w_ℓ + w_{n-ℓ})`, where `ℓ` is the number of black draws seen so far. -/
def IsGeneralizedPolyaUrnWithWeights
    (μ : Measure Ω) (w : ℕ → NNReal) (X : ℕ → Ω → Bool) : Prop :=
  (∀ n : ℕ, Measurable (X n)) ∧
    ∀ ⦃n : ℕ⦄ (x : Fin n → Bool),
      let ℓ := blackPrefixCount x
      μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
        (((w ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ (weightedUrnPrefixEvent X x)

namespace IsGeneralizedPolyaUrnWithWeights

-- Proof sketch: measurability is part of the defining data of
-- `IsGeneralizedPolyaUrnWithWeights`; unpack the first conjunct.
/-- Every coordinate of a generalized weighted Pólya-urn draw sequence is measurable. -/
theorem measurable
    {μ : Measure Ω} {w : ℕ → NNReal} {X : ℕ → Ω → Bool}
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) (n : ℕ) :
    Measurable (X n) :=
  hX.1 n

/-- The defining one-step cylinder probability formula of a generalized weighted Pólya urn. -/
theorem prefixEvent_inter_true_eq
    {μ : Measure Ω} {w : ℕ → NNReal} {X : ℕ → Ω → Bool}
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) {n : ℕ} (x : Fin n → Bool) :
    let ℓ := blackPrefixCount x
    μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
      (((w ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ (weightedUrnPrefixEvent X x) :=
  hX.2 x

end IsGeneralizedPolyaUrnWithWeights

-- Proof sketch: use the exponential-clock embedding from Example 17.27. When
-- `∑ (w n)⁻¹ = ∞`, the independent explosion times for the red and black clocks are both almost
-- surely infinite, so neither color can stop appearing after finitely many draws.
/-- Exercise 17.3.2: in the generalized two-color Pólya urn of Example 17.27 with one red and one
black initial ball and weight sequence `w`, if `∑ 1 / w_n = ∞`, then almost surely the draw
sequence contains infinitely many black draws and infinitely many red draws. -/
theorem ae_infinitely_many_draws_each_color_of_tsum_inv_weights_eq_top
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → Bool) (w : ℕ → NNReal)
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) (hw_pos : ∀ n : ℕ, 0 < w n)
    (hw_div : (∑' n : ℕ, ((w n : ℝ≥0∞)⁻¹)) = ∞) :
    ∀ᵐ ω ∂μ, {n : ℕ | X n ω = true}.Infinite ∧ {n : ℕ | X n ω = false}.Infinite := sorry

end ProbabilityTheory

/-! ### Definition_17_3 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {I : Type u} [AddMonoid I] [Preorder I]
variable {Ω : Type v} [mΩ : MeasurableSpace Ω]
variable {E : Type w} [mE : MeasurableSpace E]

/-- The time-`t` transition kernel induced by a path-space kernel `κ : Kernel E (I → E)`. -/
abbrev transitionKernel (κ : Kernel E (I → E)) (t : I) : Kernel E E :=
  κ.map fun y ↦ y t

-- Proof sketch: unfold `transitionKernel`; it is defined as `Kernel.map` of `κ` along the
-- coordinate-evaluation map `y ↦ y t`, so the resulting fiber at `x` is exactly `(κ x).map`.
/-- Evaluating `transitionKernel κ t` at a state `x` pushes the path law `κ x` forward by the
time-`t` coordinate projection. -/
theorem transitionKernel_apply (κ : Kernel E (I → E)) (t : I) (x : E) :
    transitionKernel κ t x = (κ x).map (fun y ↦ y t) := sorry

-- Proof sketch: `transitionKernel κ t` is `Kernel.map` of the Markov kernel `κ` along the
-- measurable evaluation map at time `t`; `IsMarkovKernel.map` preserves the Markov-kernel property.
/-- A Markov path kernel yields a Markov state-transition kernel at each time `t`. -/
instance (κ : Kernel E (I → E)) [IsMarkovKernel κ] (t : I) :
    IsMarkovKernel (transitionKernel κ t) := sorry

/-- Definition 17.3: a process `X` with laws `P x` is a time-homogeneous Markov process with
transition probabilities `κ` if each coordinate is measurable, `X 0 = x` almost surely under
`P x`, the path law of `X` under `P x` is the path-space kernel `κ x`, and the natural filtration
satisfies `P_x[X_{t+s} ∈ A | 𝓕_s] = κ_t(X_s, A)` almost surely for all measurable `A`. The
countable-state case is the discrete Markov-process case, and `I = ℕ` gives the Markov-chain case.
-/
class IsTimeHomogeneousMarkovProcess
    (X : I → Ω → E) (P : outParam (E → ProbabilityMeasure Ω))
    (κ : outParam (Kernel E (I → E))) : Prop where
  /-- Each time slice `X t` is measurable on the ambient measurable space `(Ω, 𝓐)`. -/
  measurable_process : ∀ t, Measurable (X t)
  /-- Under `P x`, the process starts from the state `x` almost surely. -/
  initial_state : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1
  /-- The canonical path law of `X` under `P x` is the stochastic kernel `κ x` on `E^I`. -/
  path_law : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun t : I ↦ X t ω)
  /-- The natural filtration generated by the past coordinates of `X` satisfies the
  time-homogeneous Markov property with transition kernel `κ_t`. -/
  markov_property :
    ∀ x ⦃A : Set E⦄, MeasurableSet A → ∀ s t : I,
      (P x)⟦X (t + s) ⁻¹' A | ⨆ r ≤ s, MeasurableSpace.comap (X r) mE⟧ =ᵐ[(P x : Measure Ω)]
        fun ω ↦ ((transitionKernel κ t) (X s ω)).real A

/-- Every time slice of a time-homogeneous Markov process is measurable. -/
instance (t : I) (X : I → Ω → E) {P : outParam (E → ProbabilityMeasure Ω)}
    {κ : outParam (Kernel E (I → E))} [h : IsTimeHomogeneousMarkovProcess X P κ] :
    Measurable (X t) :=
  h.measurable_process t

namespace IsTimeHomogeneousMarkovProcess

-- Proof sketch: `path_law` identifies each row of `κ` with the pushforward of the probability
-- measure `P x` along the full-path map `ω ↦ (t ↦ X t ω)`, so every row is again a probability
-- measure.
/-- Any time-homogeneous Markov process carries a Markov path kernel as derived data. -/
theorem isMarkovKernel
    (X : I → Ω → E) {P : outParam (E → ProbabilityMeasure Ω)}
    {κ : outParam (Kernel E (I → E))} [h : IsTimeHomogeneousMarkovProcess X P κ] :
    IsMarkovKernel κ := sorry

section

variable [AddCommMonoid I] [PartialOrder I] [ExistsAddOfLE I] [AddLeftMono I]
variable [Sub I] [OrderedSub I]

-- Proof sketch: the initial-state field gives `(P x).map (X 0) = Measure.dirac x`. For `s ≤ t`,
-- write `t = u + s`; then Definition 17.3 gives the conditional law of `X t` given the full
-- history up to `s` as the `σ(X s)`-measurable function `ω ↦ transitionKernel κ u (X s ω) A`. By
-- uniqueness of conditional expectation, this same function is also the conditional probability
-- given only `X s`, so the owner abstraction from Theorem 17.8 applies. The one-time marginal
-- identity is obtained by pushing forward the path-law field along the coordinate evaluation map.
/-- The source-facing path-kernel formulation of Definition 17.3 induces the canonical
state-kernel realization `t ↦ transitionKernel κ t` from Theorem 17.8. -/
theorem toIsMarkovProcessRealization
    (X : I → Ω → E) {P : outParam (E → ProbabilityMeasure Ω)}
    {κ : outParam (Kernel E (I → E))} [h : IsTimeHomogeneousMarkovProcess X P κ] :
    IsMarkovProcessRealization (transitionKernel κ) P X := sorry

-- Proof sketch: transport the owner-level consequences of
-- `toIsMarkovProcessRealization` through Theorem 17.8, which packages the initial-state law,
-- zero-time identity, and Chapman--Kolmogorov equation as `IsMarkovSemigroup`.
/-- The state kernels induced by a time-homogeneous Markov process form the canonical Markov
semigroup attached to the process. -/
theorem transitionKernel_isMarkovSemigroup
    (X : I → Ω → E) {P : outParam (E → ProbabilityMeasure Ω)}
    {κ : outParam (Kernel E (I → E))} [h : IsTimeHomogeneousMarkovProcess X P κ] :
    _root_.IsMarkovSemigroup (transitionKernel κ) := sorry

end

end IsTimeHomogeneousMarkovProcess

section

variable [AddCommMonoid I] [PartialOrder I] [ExistsAddOfLE I] [AddLeftMono I]
variable [Sub I] [OrderedSub I]

/-- The source-facing class of Definition 17.3 automatically supplies the canonical owner
abstraction `IsMarkovProcessRealization` for its induced state kernels. -/
instance (X : I → Ω → E) {P : outParam (E → ProbabilityMeasure Ω)}
    {κ : outParam (Kernel E (I → E))} [h : IsTimeHomogeneousMarkovProcess X P κ] :
    IsMarkovProcessRealization (transitionKernel κ) P X :=
  IsTimeHomogeneousMarkovProcess.toIsMarkovProcessRealization X

end

end ProbabilityTheory
