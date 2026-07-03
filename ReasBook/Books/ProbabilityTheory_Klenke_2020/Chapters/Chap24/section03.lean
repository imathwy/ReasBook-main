import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_24_3_1 (from Items/Chap24) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The two-parameter Dirichlet law on pairs, obtained by normalizing two independent
unit-rate Gamma coordinates with shapes `θ₁` and `θ₂`. -/
def dirichletPairMeasure (θ₁ θ₂ : ℝ) : Measure (Fin 2 → ℝ) :=
  (Measure.pi fun i : Fin 2 ↦ gammaMeasure (![θ₁, θ₂] i) 1).map
    (fun y i ↦ y i / ∑ j, y j)

-- Proof sketch: unfold `dirichletPairMeasure`; it is defined as the pushforward of the product
-- Gamma law under normalization by the total mass.
/-- Unfolding `dirichletPairMeasure θ₁ θ₂` gives the normalized-Gamma pushforward formula for the
two-parameter Dirichlet law. -/
theorem dirichletPairMeasure_def (θ₁ θ₂ : ℝ) :
    dirichletPairMeasure θ₁ θ₂ =
      (Measure.pi fun i : Fin 2 ↦ gammaMeasure (![θ₁, θ₂] i) 1).map
        (fun y i ↦ y i / ∑ j, y j) := sorry

-- Proof sketch: realize the Dirichlet pair by normalized independent Gamma coordinates and
-- identify the first coordinate as the classical Beta-Gamma ratio with parameters `θ₁` and `θ₂`.
/-- Exercise 24.3.1: if the pair `(X, 1 - X)` has the Dirichlet law with positive parameters
`θ₁, θ₂`, interpreted as `dirichletPairMeasure θ₁ θ₂`, then `X` has the Beta law with parameters
`θ₁, θ₂`. -/
theorem hasLaw_beta_of_hasLaw_dirichlet_pair
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {θ₁ θ₂ : ℝ}
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hX : HasLaw (fun ω ↦ ![X ω, 1 - X ω]) (dirichletPairMeasure θ₁ θ₂) μ) :
    HasLaw X (betaMeasure θ₁ θ₂) μ := sorry

end ProbabilityTheory

/-! ### Exercise_24_3_2 (from Items/Chap24) -/
open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The finite-dimensional Dirichlet law obtained by normalizing independent Gamma coordinates
with shape parameters `θ i`. -/
def dirichletMeasure {n : ℕ} (θ : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  (Measure.pi fun i ↦ gammaMeasure (θ i) 1).map (fun y i ↦ y i / ∑ j, y j)

-- Proof sketch: unfold `dirichletMeasure`; it is exactly the pushforward of the product Gamma law
-- along the coordinatewise normalization map `y ↦ (fun i ↦ y i / ∑ j, y j)`.
/-- Unfolding `dirichletMeasure` gives the normalized-Gamma construction of the Dirichlet law. -/
theorem dirichletMeasure_def {n : ℕ} (θ : Fin n → ℝ) :
    dirichletMeasure θ =
      (Measure.pi fun i ↦ gammaMeasure (θ i) 1).map (fun y i ↦ y i / ∑ j, y j) := sorry

-- Proof sketch: realize `X` by the normalized-Gamma construction of the Dirichlet law, then
-- permute the independent Gamma coordinates. The product Gamma law is invariant under coordinate
-- permutations, so pushing forward by the same normalization yields the Dirichlet law with the
-- permuted parameter vector.
/-- Exercise 24.3.2 (1): permuting the coordinates of a Dirichlet-distributed vector permutes the
parameter vector in the same way. -/
theorem hasLaw_dirichlet_permute
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin n → ℝ}
    {θ : Fin n → ℝ} (hθ : ∀ i, 0 < θ i) (σ : Equiv.Perm (Fin n))
    (hX : HasLaw X (dirichletMeasure θ) μ) :
    HasLaw (fun ω i ↦ X ω (σ i)) (dirichletMeasure fun i ↦ θ (σ i)) μ := sorry

-- Proof sketch: write `X` as normalized independent Gamma coordinates with shapes `θ i`. Group
-- the last two Gamma variables into their sum, use Gamma-additivity to identify the new last
-- shape as `θ_{n+1} + θ_{n+2}`, and normalize again to obtain the Dirichlet law of the merged
-- vector.
/-- Exercise 24.3.2 (2): combining the last two coordinates of a Dirichlet-distributed
`(n + 2)`-tuple produces a Dirichlet-distributed `(n + 1)`-tuple whose last parameter is the sum
of the last two parameters. -/
theorem hasLaw_dirichlet_merge_last
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin (n + 2) → ℝ}
    {θ : Fin (n + 2) → ℝ} (hθ : ∀ i, 0 < θ i)
    (hX : HasLaw X (dirichletMeasure θ) μ) :
    HasLaw
      (fun ω ↦
        Fin.snoc
          (Fin.init (Fin.init (X ω)))
          ((Fin.init (X ω)) (Fin.last n) + X ω (Fin.last (n + 1))))
      (dirichletMeasure <|
        Fin.snoc
          (Fin.init (Fin.init θ))
          ((Fin.init θ) (Fin.last n) + θ (Fin.last (n + 1)))) μ := sorry

end ProbabilityTheory

/-! ### Definition_24_3 (from Items/Chap24) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [TopologicalSpace E]

/-
Definition 24.3 is source-facing: it keeps the textbook random measure as a measure-valued random
variable, while the measurable owner abstraction for that ambient data is the canonical kernel
object `Kernel Ω E`.
-/
/-- Definition 24.3: a random measure on `E` under the probability law `P` is a measurable
`Measure E`-valued random variable whose values are locally finite almost surely. Mathlib's
canonical measurable-space structure on `Measure E` and the owner abstraction `Kernel Ω E`
model the measurable part of the textbook ambient space `\widetilde{\mathcal M}(E)`, while the
almost-sure local-finiteness clause formalizes `\mathbf{P}[X \in \mathcal{M}(E)] = 1`. -/
def IsRandomMeasure (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  Measurable X ∧ ∀ᵐ ω ∂(P : Measure Ω), IsLocallyFiniteMeasure (X ω)

namespace IsRandomMeasure

/-- A random measure is measurable as a `Measure E`-valued map. -/
theorem measurable {P : ProbabilityMeasure Ω} {X : Ω → Measure E} (hX : IsRandomMeasure P X) :
    Measurable X :=
  hX.1

/-- A random measure is almost everywhere measurable under the ambient probability law. -/
theorem aemeasurable {P : ProbabilityMeasure Ω} {X : Ω → Measure E} (hX : IsRandomMeasure P X) :
    AEMeasurable X (P : Measure Ω) :=
  hX.measurable.aemeasurable

/-- A random measure is locally finite almost surely. -/
theorem ae_isLocallyFiniteMeasure
    {P : ProbabilityMeasure Ω} {X : Ω → Measure E} (hX : IsRandomMeasure P X) :
    ∀ᵐ ω ∂(P : Measure Ω), IsLocallyFiniteMeasure (X ω) :=
  hX.2

end IsRandomMeasure

end ProbabilityTheory

/-! ### Exercise_24_3_3 (from Items/Chap24) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

noncomputable section

universe u v

namespace ProbabilityTheory

/-- The stick-breaking map associated with an infinite sequence of break proportions. -/
def gemStickBreaking (v : ℕ → ℝ) : ℕ → ℝ :=
  fun k ↦ (Finset.range k).prod (fun i ↦ (1 - v i)) * v k

-- Proof sketch: unfold `gemStickBreaking`; the `k`th coordinate is the product of the preceding
-- residual factors multiplied by the `k`th break proportion.
/-- The `k`th GEM stick-breaking mass is the product of the previous residual factors times the
`k`th break proportion. -/
theorem gemStickBreaking_apply (v : ℕ → ℝ) (k : ℕ) :
    gemStickBreaking v k = (Finset.range k).prod (fun i ↦ (1 - v i)) * v k := sorry

/-- The canonical `GEM_θ` law obtained by pushing forward an i.i.d. `Beta(1, θ)` sequence through
the stick-breaking map. -/
def gemMeasure (θ : ℝ) : Measure (ℕ → ℝ) :=
  Measure.map gemStickBreaking (Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 θ)

-- Proof sketch: unfold `gemMeasure`; by definition it is the pushforward of the product
-- `Beta(1, θ)` law under `gemStickBreaking`.
/-- The `GEM_θ` law is the pushforward of the i.i.d. `Beta(1, θ)` product measure by the
stick-breaking map. -/
theorem gemMeasure_def (θ : ℝ) :
    gemMeasure θ = Measure.map gemStickBreaking (Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 θ) :=
  sorry

/-- A source-facing realization of the zero-discount Chinese restaurant process with concentration
parameter `θ`, exposing the table-size coordinates `N_l^n` on a probability space. The Lean table
index `l = 0` corresponds to the textbook index `1`. -/
structure ChineseRestaurantProcessZeroDiscount (θ : ℝ) where
  /-- The underlying sample space of the process. -/
  Ω : Type u
  /-- The measurable-space structure on the sample space. -/
  mΩ : MeasurableSpace Ω
  /-- The probability law of the Chinese restaurant process. -/
  law : ProbabilityMeasure Ω
  /-- The table-size coordinate `N_l^n`, with zero-based Lean table index `l`. -/
  tableSize : ℕ → Ω → ℕ → ℕ
  /-- The concentration parameter is positive. -/
  theta_pos : 0 < θ
  /-- Every table-size coordinate is measurable. -/
  measurable_tableSize : ∀ n l, Measurable (fun ω ↦ tableSize n ω l)
  /-- At time `n`, the table sizes sum to `n`. -/
  total_customers : ∀ n ω, (Finset.range (n + 1)).sum (fun l ↦ tableSize n ω l) = n
  /-- At time `n`, all coordinates after index `n` vanish. -/
  tail_zero : ∀ n ω l, n < l → tableSize n ω l = 0

namespace ChineseRestaurantProcessZeroDiscount

variable {θ : ℝ}

/-- The measurable-space structure on the sample space of a Chinese restaurant process. -/
instance instMeasurableSpace (crp : ChineseRestaurantProcessZeroDiscount θ) :
    MeasurableSpace crp.Ω :=
  crp.mΩ

/-- The rescaled block-size sequence `l ↦ N_l^n / n` of the Chinese restaurant process. -/
def blockProportions (crp : ChineseRestaurantProcessZeroDiscount θ) (n : ℕ) :
    crp.Ω → ℕ → ℝ :=
  fun ω l ↦ (crp.tableSize n ω l : ℝ) / n

-- Proof sketch: unfold `blockProportions`; it is defined coordinatewise by dividing the
-- `l`th table size at time `n` by `n`.
/-- The rescaled block-size sequence is given coordinatewise by `N_l^n / n`. -/
theorem blockProportions_apply (crp : ChineseRestaurantProcessZeroDiscount θ) (n : ℕ)
    (ω : crp.Ω) (l : ℕ) :
    crp.blockProportions n ω l = (crp.tableSize n ω l : ℝ) / n := sorry

-- Proof sketch: measurability into the countable product `ℝ^ℕ` is coordinatewise; each coordinate
-- `ω ↦ (crp.tableSize n ω l : ℝ) / n` is measurable because `crp.measurable_tableSize n l` is and
-- scalar division preserves measurability.
/-- The rescaled block-size sequence is measurable as an `ℝ^ℕ`-valued random variable. -/
theorem measurable_blockProportions (crp : ChineseRestaurantProcessZeroDiscount θ) (n : ℕ) :
    Measurable (crp.blockProportions n) := sorry

end ChineseRestaurantProcessZeroDiscount

/-- The remaining mass after prescribing a finite initial block-size profile. -/
def chineseRestaurantRemainingMass {l : ℕ} (xs : Fin l → ℝ) : ℝ :=
  1 - Finset.univ.sum xs

-- Proof sketch: unfold `chineseRestaurantRemainingMass`; it is defined to be `1` minus the finite
-- sum of the prescribed coordinates.
/-- The remaining mass is `1` minus the sum of the prescribed initial coordinates. -/
theorem chineseRestaurantRemainingMass_def {l : ℕ} (xs : Fin l → ℝ) :
    chineseRestaurantRemainingMass xs = 1 - Finset.univ.sum xs := sorry

-- Proof sketch: for the zero-discount process with `θ = 1`, the first occupied table has the
-- same law as the length of the first cycle of a uniform random permutation of `{1, …, n}`; the
-- cycle-length law is uniform on `{1, …, n}`.
/-- Exercise 24.3.3 (1): in the case `θ = 1`, the first table size `N_1^n` (Lean index `0`) is
uniform on `{1, …, n}`. -/
theorem chineseRestaurant_first_table_uniform
    (crp : ChineseRestaurantProcessZeroDiscount 1) {n k : ℕ}
    (hk_pos : 0 < k) (hk_le : k ≤ n) :
    ((crp.law : Measure crp.Ω) ({ω | crp.tableSize n ω 0 = k} : Set crp.Ω)) =
      ENNReal.ofReal (1 / (n : ℝ)) := sorry

-- Proof sketch: condition on the first `l` table sizes and use the Ewens-permutation description
-- for `θ = 1`; after removing the already specified customers, the next table length is uniform on
-- the remaining set of admissible sizes.
/-- Exercise 24.3.3 (2): in the case `θ = 1`, after conditioning on the first `l` table sizes, the
next table size (Lean index `l`) is uniform on the remaining sizes. -/
theorem chineseRestaurant_next_table_conditional_uniform
    (crp : ChineseRestaurantProcessZeroDiscount 1) {n l k : ℕ} (ks : Fin l → ℕ)
    (hk_pos : 0 < k) (hks_pos : ∀ i, 0 < ks i)
    (hks_sum_le : Finset.univ.sum ks + k ≤ n) :
    (crp.law : Measure crp.Ω)[({ω | crp.tableSize n ω l = k} : Set crp.Ω) |
      ({ω | ∀ i : Fin l, crp.tableSize n ω i = ks i} : Set crp.Ω)] =
      ENNReal.ofReal (1 / ((n - Finset.univ.sum ks : ℕ) : ℝ)) := sorry

-- Proof sketch: combine the exact one-dimensional and conditional laws from clauses (1) and (2)
-- with the chain rule for finite-dimensional distributions. This identifies the joint limit law of
-- the rescaled block-size sequence with the canonical `GEM_1` stick-breaking law.
/-- Exercise 24.3.3 (3): for `θ = 1`, the rescaled Chinese-restaurant block-size sequence
converges in distribution to the canonical `GEM_1` law. -/
theorem chineseRestaurant_theta_one_blockProportions_tendsto_gem
    {Ω' : Type v} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    (crp : ChineseRestaurantProcessZeroDiscount 1) (V : Ω' → ℕ → ℝ)
    (hV : HasLaw V (gemMeasure 1) Q) :
    TendstoInDistribution
      (fun n ↦ crp.blockProportions n) atTop V
      (fun _ ↦ (crp.law : Measure crp.Ω)) Q := sorry

-- Proof sketch: write the exact Ewens sampling formula for `N_1^n`, evaluate it at
-- `k = ⌊n x⌋`, and use the asymptotics of Gamma-function ratios or rising factorials to identify
-- the limit density `θ (1 - x)^{θ - 1}`.
/-- Exercise 24.3.3 (4): for `θ > 0`, the first table size satisfies the local limit
`n P[N_1^n = ⌊n x⌋] → θ (1 - x)^{θ - 1}` for every `x ∈ (0, 1)`. -/
theorem chineseRestaurant_first_table_localLimit
    {θ x : ℝ} (crp : ChineseRestaurantProcessZeroDiscount θ)
    (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto
      (fun n : ℕ ↦
        (n : ℝ) *
          ((crp.law : Measure crp.Ω) {ω | crp.tableSize n ω 0 = ⌊(n : ℝ) * x⌋₊}).toReal)
      atTop
      (𝓝 (θ * (1 - x) ^ (θ - 1))) := sorry

-- Proof sketch: condition on the first `l` rescaled table sizes, apply the Ewens sampling formula
-- to the remaining restaurant with residual mass `y = 1 - ∑_{i < l} x_i`, and pass to the limit
-- exactly as in the one-dimensional case after rescaling by the residual mass.
/-- Exercise 24.3.3 (5): for `θ > 0`, after conditioning on the first `l` block sizes, the next
block size has local limit density `(θ / y) (1 - x / y)^{θ - 1}` with
`y = 1 - (x_1 + ··· + x_l)`. -/
theorem chineseRestaurant_next_table_conditional_localLimit
    {θ x : ℝ} (crp : ChineseRestaurantProcessZeroDiscount θ) {l : ℕ}
    (xs : Fin l → ℝ) (hxs_pos : ∀ i, 0 < xs i)
    (hx_pos : 0 < x) (hx_lt_remaining : x < chineseRestaurantRemainingMass xs) :
    Tendsto
      (fun n : ℕ ↦
        (n : ℝ) *
          ((crp.law : Measure crp.Ω)[{ω | crp.tableSize n ω l = ⌊(n : ℝ) * x⌋₊} |
            {ω | ∀ i : Fin l, crp.tableSize n ω i = ⌊(n : ℝ) * xs i⌋₊}]).toReal)
      atTop
      (𝓝
        ((θ / chineseRestaurantRemainingMass xs) *
          (1 - x / chineseRestaurantRemainingMass xs) ^ (θ - 1))) := sorry

-- Proof sketch: use the one-dimensional local limit and the conditional local-limit formula from
-- the previous two clauses to identify all finite-dimensional marginals of the rescaled process.
-- The chain rule then yields convergence in distribution to the canonical `GEM_θ` law.
/-- Exercise 24.3.3 (6): for `θ > 0`, the rescaled block-size sequence of the zero-discount
Chinese restaurant process converges in distribution to the canonical `GEM_θ` law. -/
theorem chineseRestaurant_blockProportions_tendsto_gem
    {θ : ℝ} {Ω' : Type v} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    (crp : ChineseRestaurantProcessZeroDiscount θ) (V : Ω' → ℕ → ℝ)
    (hV : HasLaw V (gemMeasure θ) Q) :
    TendstoInDistribution
      (fun n ↦ crp.blockProportions n) atTop V
      (fun _ ↦ (crp.law : Measure crp.Ω)) Q := sorry

end ProbabilityTheory
