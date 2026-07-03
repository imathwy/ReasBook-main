import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_2_2_1 (from Items/Chap02) -/
open MeasureTheory ProbabilityTheory

universe u

-- Proof sketch: identify the event `{ω | X ω < Y ω}` with the region below the diagonal for the
-- joint law of `(X, Y)`, use independence and the two exponential marginals to factor the joint
-- density, integrate over `{(x, y) | 0 ≤ x ∧ x < y}`, and simplify the resulting elementary
-- integral.
/-- Exercise 2.2.1: if `X` and `Y` are independent real random variables with exponential laws of
rates `θ` and `ρ`, then the probability that `X < Y` is `θ / (θ + ρ)`. -/
theorem indep_exponential_lt_probability
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ} {θ ρ : ℝ}
    (hX : HasLaw X (expMeasure θ) P)
    (hY : HasLaw Y (expMeasure ρ) P)
    (hXY : X ⟂ᵢ[P] Y)
    (hθ : 0 < θ) (hρ : 0 < ρ) :
    P.real {ω | X ω < Y ω} = θ / (θ + ρ) := sorry

/-! ### Example_2_2 (from Items/Chap02) -/
open Set MeasureTheory ProbabilityTheory

noncomputable section

/-- The sample space of three successive die rolls. -/
abbrev ThreeRolls := Fin 3 → Die

/-- The law of three independent fair die rolls. -/
abbrev threeRollsMeasure : Measure ThreeRolls :=
  Measure.pi fun _ : Fin 3 ↦ dieMeasure

/-- The three coordinate projections on the product space of die rolls are independent. -/
theorem threeRolls_iIndepFun :
    iIndepFun Function.eval threeRollsMeasure := by
  simpa [Function.eval, threeRollsMeasure] using
    (iIndepFun_pi (fun _ : Fin 3 ↦ measurable_id.aemeasurable) :
      iIndepFun (fun i (ω : ThreeRolls) ↦ ω i) (Measure.pi fun _ : Fin 3 ↦ dieMeasure))

/-- The three diagonal events `ω₀ = ω₁`, `ω₁ = ω₂`, and `ω₀ = ω₂`. -/
def diagonalEqualityEvents : Fin 3 → Set ThreeRolls
  | 0 => {ω : ThreeRolls | ω 0 = ω 1}
  | 1 => {ω : ThreeRolls | ω 1 = ω 2}
  | 2 => {ω : ThreeRolls | ω 0 = ω 2}

-- Proof sketch: `threeRollsMeasure` is a product measure, so the coordinate maps are independent;
-- apply this to the measurable sets `S i`.
/-- Events depending separately on the first, second, and third die roll are independent. -/
theorem coordinatePreimage_iIndepSet (S : Fin 3 → Set Die) :
    iIndepSet (fun i ↦ Function.eval i ⁻¹' S i) threeRollsMeasure := by
  rw [iIndepSet_iff_meas_biInter]
  · intro s
    simpa [Function.eval] using
      threeRolls_iIndepFun.measure_inter_preimage_eq_mul s
        (fun i _ ↦ (Set.toFinite (S i)).measurableSet)
  · intro i
    exact (measurable_pi_apply i) ((Set.toFinite (S i)).measurableSet)

-- Proof sketch: compute the probabilities of the pairwise intersections by counting outcomes in
-- the `216`-point sample space.
/-- The three diagonal equality events are pairwise independent. -/
theorem diagonalEqualityEvents_pairwise :
    Pairwise fun i j ↦ IndepSet (diagonalEqualityEvents i) (diagonalEqualityEvents j)
      threeRollsMeasure := sorry

-- Proof sketch: all three diagonal equalities hold exactly when all three rolls coincide, so the
-- probability of the triple intersection is `1 / 36`, whereas the product of the three marginal
-- probabilities is `1 / 216`.
/-- The three diagonal equality events are not independent as a family. -/
theorem diagonalEqualityEvents_not_iIndep :
    ¬ iIndepSet diagonalEqualityEvents threeRollsMeasure := sorry

-- Proof sketch: for the first clause, use that `threeRollsMeasure` is the uniform product measure
-- on `Fin 3 → Fin 6`, so events depending on disjoint coordinates are independent. For the second
-- clause, compute the probabilities of the three diagonal events and of their intersections by
-- counting outcomes.
/-- Example 2.2: For three fair die rolls, events depending separately on the first, second, and
third coordinate are independent, while the events `ω₁ = ω₂`, `ω₂ = ω₃`, and `ω₁ = ω₃` are
pairwise independent but not independent as a triple. -/
theorem roll_three_times_independence_examples :
    (∀ S : Fin 3 → Set Die,
      iIndepSet (fun i ↦ Function.eval i ⁻¹' S i) threeRollsMeasure) ∧
    Pairwise (fun i j ↦ IndepSet (diagonalEqualityEvents i) (diagonalEqualityEvents j)
      threeRollsMeasure) ∧
    ¬ iIndepSet diagonalEqualityEvents threeRollsMeasure := by
  exact ⟨coordinatePreimage_iIndepSet, diagonalEqualityEvents_pairwise,
    diagonalEqualityEvents_not_iIndep⟩

/-! ### Exercise_2_2_2 (from Items/Chap02) -/
open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {U V : Ω → ℝ}

-- Lebesgue measure restricted to the unit interval `[0,1]`.
local notation "unitIntervalVolume" => volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The Box-Muller map sends a pair of real parameters `(u, v)` to the corresponding pair of
Gaussian coordinates. -/
noncomputable
def boxMullerPair (u v : ℝ) : ℝ × ℝ :=
  (Real.sqrt (-2 * Real.log u) * Real.cos (2 * Real.pi * v),
    Real.sqrt (-2 * Real.log u) * Real.sin (2 * Real.pi * v))

variable (hU : HasLaw U unitIntervalVolume P)
variable (hV : HasLaw V unitIntervalVolume P)
variable (hUV : U ⟂ᵢ[P] V)

-- Proof sketch: compute the law of the radius `R = sqrt (-2 log U)` from the uniform law of `U`,
-- combine it with the uniform angular variable `2πV`, and apply the transformation formula in
-- polar coordinates to identify the pushforward measure with the product of two standard Gaussian
-- laws.
/-- Exercise 2.2.2: If `U` and `V` are independent and both uniformly distributed on `[0,1]`,
then the Box-Muller transform has joint law equal to the product of two standard Gaussian laws. -/
theorem boxMullerPair_hasLaw
    :
    HasLaw (fun ω ↦ boxMullerPair (U ω) (V ω))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) P := sorry

-- Proof sketch: rewrite independence in terms of the pushforward law of the pair
-- `(boxMullerPair (U ω) (V ω)).1, (boxMullerPair (U ω) (V ω)).2`, then use
-- `boxMullerPair_hasLaw` to identify this law with the product of the two marginal Gaussian laws.
/-- The two coordinates produced by the Box-Muller transform are independent. -/
theorem boxMuller_fst_indepFun_snd
    :
    (fun ω ↦ (boxMullerPair (U ω) (V ω)).1) ⟂ᵢ[P]
      (fun ω ↦ (boxMullerPair (U ω) (V ω)).2) := sorry

-- Proof sketch: compose the joint-law statement `boxMullerPair_hasLaw` with the first-coordinate
-- projection and use that the first marginal of the product measure
-- `(gaussianReal 0 1).prod (gaussianReal 0 1)` is `gaussianReal 0 1`.
/-- The first Box-Muller coordinate has the standard Gaussian law. -/
theorem boxMuller_fst_hasLaw
    :
    HasLaw (fun ω ↦ (boxMullerPair (U ω) (V ω)).1) (gaussianReal 0 1) P := sorry

-- Proof sketch: compose the joint-law statement `boxMullerPair_hasLaw` with the second-coordinate
-- projection and use that the second marginal of the product measure
-- `(gaussianReal 0 1).prod (gaussianReal 0 1)` is `gaussianReal 0 1`.
/-- The second Box-Muller coordinate has the standard Gaussian law. -/
theorem boxMuller_snd_hasLaw
    :
    HasLaw (fun ω ↦ (boxMullerPair (U ω) (V ω)).2) (gaussianReal 0 1) P := sorry

/-! ### Exercise_2_2_3 (from Items/Chap02) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

variable {Ω : Type u} {m n : ℕ}

/-- The count vector recording how often each value in `Fin m` appears among the samples
`X 0 ω, …, X (n - 1) ω`. -/
def multinomialCount (X : Fin n → Ω → Fin m) (ω : Ω) : Fin m → ℕ :=
  fun i ↦ Finset.card <| Finset.univ.filter fun j ↦ X j ω = i

/-- The entries of the count vector sum to the sample size. -/
theorem sum_multinomialCount (X : Fin n → Ω → Fin m) (ω : Ω) :
    ∑ i, multinomialCount X ω i = n := by
  let f : Fin n → Fin m := fun j ↦ X j ω
  have h_mapsTo :
      ((Finset.univ : Finset (Fin n)) : Set (Fin n)).MapsTo f (Finset.univ : Finset (Fin m)) :=
    fun _ _ ↦ Finset.mem_univ _
  simpa [multinomialCount] using
    (Finset.card_eq_sum_card_fiberwise h_mapsTo).symm

section

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Exercise 2.2.3: if `X : Fin n → Ω → Fin m` is an independent family with common law `p`,
then the count vector `ω ↦ (fun i ↦ #{j | X j ω = i})` has multinomial point mass
`Nat.multinomial Finset.univ k * ∏ i, p i ^ k i` at every
`k ∈ Finset.piAntidiag Finset.univ n`. -/
theorem multinomialCount_preimage_singleton_eq_multinomial
    (p : PMF (Fin m)) (X : Fin n → Ω → Fin m) (h_indep : iIndepFun X μ)
    (h_law : ∀ i, HasLaw (X i) p.toMeasure μ) (k : Fin m → ℕ)
    (hk : k ∈ Finset.piAntidiag Finset.univ n) :
    μ (multinomialCount X ⁻¹' {k}) =
      (Nat.multinomial Finset.univ k : ENNReal) * (∏ i, (p i) ^ k i) := sorry

/-- Source-style reformulation of Exercise 2.2.3 with the total-count hypothesis written as
`∑ i, k i = n`. -/
theorem multinomialCount_preimage_singleton_eq_multinomial_of_sum_eq
    (p : PMF (Fin m)) (X : Fin n → Ω → Fin m) (h_indep : iIndepFun X μ)
    (h_law : ∀ i, HasLaw (X i) p.toMeasure μ) (k : Fin m → ℕ) (hk : ∑ i, k i = n) :
    μ (multinomialCount X ⁻¹' {k}) =
      (Nat.multinomial Finset.univ k : ENNReal) * (∏ i, (p i) ^ k i) := by
  simpa [Finset.mem_piAntidiag, hk] using
    multinomialCount_preimage_singleton_eq_multinomial p X h_indep h_law k

end
