import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_17_8 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w w'

namespace ProbabilityTheory

variable {I : Type u} [Preorder I]
variable {E : Type v} [MeasurableSpace E]

-- Proof sketch: if every coordinate of `X` is measurable for the ambient σ-algebra, then each
-- coordinate pullback σ-algebra already lies below `mΩ`, so intersecting with `mΩ` does not
-- change the generated filtration space.
/-- A measurable process has the same history filtration whether one writes it with the ambient
measurable space built in or as the generated filtration space from Chapter 9. -/
theorem processFiltration_eq_generatedFiltrationSpace {Ω : Type w} [mΩ : MeasurableSpace Ω]
    (X : I → Ω → E) (hX : ∀ t, Measurable (X t)) (s : I) :
    processFiltration X s = generatedFiltrationSpace X s := sorry

/-- A process has the natural Markov property under `μ` when each coordinate is measurable and,
for every measurable state event at time `t`, conditioning on the whole history up to `s ≤ t`
agrees almost surely with conditioning only on the present state `X s`. -/
def HasNaturalMarkovProperty {Ω : Type w} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → E) : Prop :=
  (∀ t : I, Measurable (X t)) ∧
    ∀ ⦃s t : I⦄, s ≤ t → ∀ ⦃A : Set E⦄, MeasurableSet A →
      μ⟦X t ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[μ]
        μ⟦X t ⁻¹' A | MeasurableSpace.comap (X s) ‹MeasurableSpace E›⟧

-- Proof sketch: rewrite the defining conditional-probability identity using
-- `processFiltration_eq_generatedFiltrationSpace`; the coordinate measurability assumption is
-- exactly what is needed to identify generated-history measurability with adaptedness to
-- `processFiltration X`.
/-- The natural Markov property is equivalent to the canonical filtration-based Markov property for
the process filtration. -/
theorem hasNaturalMarkovProperty_iff {Ω : Type w} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → E) :
    HasNaturalMarkovProperty μ X ↔
      HasMarkovProperty (processFiltration X) μ X :=
  sorry

section

variable [Zero I]

/-- A realization of a kernel semigroup by a Markov process: for each initial state `x`, the law
`P x` makes `X` into a Markov process, starts the process from `x` at time `0`, and has one-time
marginals given by the kernel family `κ`. -/
class IsMarkovProcessRealization {Ω : Type w} [MeasurableSpace Ω] (κ : I → Kernel E E)
    (P : E → ProbabilityMeasure Ω) (X : I → Ω → E) : Prop where
  /-- Under each initial law `P x`, the process `X` has the Markov property with respect to its
  natural history. -/
  hasNaturalMarkovProperty : ∀ x : E, HasNaturalMarkovProperty (P x : Measure Ω) X
  /-- Under `P x`, the process starts from the deterministic state `x` at time `0`. -/
  initial_eq : ∀ x : E, (P x : Measure Ω).map (X 0) = Measure.dirac x
  /-- The one-time marginal at time `t` started from `x` is the kernel row `κ t x`. -/
  transition_eq : ∀ x : E, ∀ t : I, (P x : Measure Ω).map (X t) = κ t x

end

section

variable [Zero I]
variable [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
variable [SecondCountableTopology E]
variable [OpensMeasurableSpace E]
variable {Ω : Type w} [MeasurableSpace Ω]
variable {κ : I → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : I → Ω → E}

/-- Every time slice of a Markov-process realization is strongly measurable under each initial
law, because coordinate measurability is part of the realization's natural Markov property. -/
theorem IsMarkovProcessRealization.stronglyMeasurable
    (hX : IsMarkovProcessRealization κ P X) (x : E) (t : I) :
    StronglyMeasurable (X t) :=
  ((hX.hasNaturalMarkovProperty x).1 t).stronglyMeasurable

end

section

variable [AddMonoid I]

/-- Theorem 17.8: on a standard Borel state space, every Markov semigroup of stochastic kernels
admits a realization by a Markov process on some measurable space whose one-time marginals are
exactly the prescribed kernel rows `κ t x`. Here the semigroup structure is given by stochasticity
of each `κ t`, the identity law at time `0`, and the Chapman--Kolmogorov equation
`κ t ∘ₖ κ s = κ (s + t)`. -/
theorem exists_markovProcessRealization_of_markovSemigroup (κ : I → Kernel E E)
    [StandardBorelSpace E] [IsMarkovSemigroup κ] :
    ∃ (Ω : Type w), ∃ _ : MeasurableSpace Ω, ∃ X : I → Ω → E, ∃ P : E → ProbabilityMeasure Ω,
      IsMarkovProcessRealization κ P X := sorry

-- Proof sketch: each row `κ t x` is a probability measure by the transition formula. The initial
-- state identity and the time-`0` marginal identify `κ 0` with `Kernel.id`, and the natural
-- Markov property together with the marginal formula gives Chapman--Kolmogorov; these are exactly
-- the owner fields of `IsMarkovSemigroup`.
/-- Any realization of `κ` induces the ambient Markov-semigroup structure on the kernel family. -/
theorem isMarkovSemigroup_of_markovProcessRealization {Ω : Type w} [MeasurableSpace Ω]
    {κ : I → Kernel E E} {P : E → ProbabilityMeasure Ω} {X : I → Ω → E}
    [IsMarkovProcessRealization κ P X] :
    IsMarkovSemigroup κ := sorry

end

section

variable [AddCommMonoid I] [PartialOrder I] [ExistsAddOfLE I] [AddLeftMono I]
variable [Sub I] [OrderedSub I]

-- Proof sketch: the owner notion of finite-dimensional laws is the finite-set restriction law
-- `P.map (fun ω ↦ J.restrict (X · ω))`. Compute these laws recursively from the one-time
-- transition kernels using the Markov property; since both realizations use the same family `κ`,
-- the recursion agrees on every finite set of times.
/-- Two realizations of the same transition semigroup have the same finite-dimensional laws for
every initial state and every finite set of times, expressed through the canonical restriction-law
owner `P.map (fun ω ↦ J.restrict (X · ω))`. -/
theorem finiteDimensionalLaw_eq_of_sameSemigroup
    {Ω : Type w} [MeasurableSpace Ω] {Ω' : Type w'} [MeasurableSpace Ω']
    {κ : I → Kernel E E}
    {P : E → ProbabilityMeasure Ω} {Q : E → ProbabilityMeasure Ω'}
    {X : I → Ω → E} {Y : I → Ω' → E}
    [IsMarkovProcessRealization κ P X] [IsMarkovProcessRealization κ Q Y]
    (x : E) (J : Finset I) :
    (P x : Measure Ω).map (fun ω ↦ J.restrict (X · ω)) =
      (Q x : Measure Ω').map (fun ω ↦ J.restrict (Y · ω)) := sorry

-- Proof sketch: specialize the canonical finite-set law theorem to the ordered image of `times`;
-- strict monotonicity turns the finite-set restriction law into the ordered tuple law along
-- `times`.
/-- As a source-facing specialization of `finiteDimensionalLaw_eq_of_sameSemigroup`, two
realizations of the same transition semigroup have the same finite-dimensional distributions for
every initial state and every strictly increasing finite time tuple starting at `0`. -/
theorem finiteDimensionalDistribution_eq_of_sameSemigroup
    {Ω : Type w} [MeasurableSpace Ω] {Ω' : Type w'} [MeasurableSpace Ω']
    {κ : I → Kernel E E}
    {P : E → ProbabilityMeasure Ω} {Q : E → ProbabilityMeasure Ω'}
    {X : I → Ω → E} {Y : I → Ω' → E}
    [IsMarkovProcessRealization κ P X] [IsMarkovProcessRealization κ Q Y]
    (x : E) {n : ℕ} (times : Fin (n + 1) → I)
    (h_zero : times 0 = 0) (htimes : StrictMono times) :
    (P x : Measure Ω).map (fun ω i ↦ X (times i) ω) =
      (Q x : Measure Ω').map (fun ω i ↦ Y (times i) ω) := sorry

end

end ProbabilityTheory
