import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_11_2_1 (from Items/Chap11) -/
open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ProbabilityTheory Topology

universe u

namespace MeasureTheory

/- Exercise 11.2.1 is `source-facing`: it asserts the existence of a filtered probability space
supporting a martingale with four standard properties. The `core/canonical` owner layer is the
existing martingale API (`Martingale`, pointwise nonnegativity, expectation identities, and
almost-sure convergence), so no extra witness structure is kept here. -/

-- Proof sketch: use a standard non-uniformly-integrable nonnegative martingale, for example a
-- dyadic martingale or an exponential martingale from the earlier chapter, whose expectations stay
-- equal to `1` while the almost-sure limit is `0`.
/-- Exercise 11.2.1: there exists a filtered probability space carrying a nonnegative martingale
with expectation `1` at every time and which converges almost surely to `0`, so the `p = 1`
analogue of Theorem 11.10 can fail. -/
theorem exists_nonnegative_martingale_with_expectation_one_ae_tendsto_zero :
    ∃ (Ω : Type u) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ),
        Martingale X ℱ μ ∧
          0 ≤ X ∧
          (∀ n, μ[X n] = 1) ∧
          ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (0 : ℝ)) := sorry

end MeasureTheory

/-! ### Exercise_11_2_2 (from Items/Chap11) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

private lemma weighted_sum_eq
    (z : ℕ → ℝ) :
    ∀ n,
      ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * z i) =
        (n : ℝ) * ∑ i ∈ Finset.range n, z i -
          ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, z j
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, weighted_sum_eq z n,
        Nat.cast_add, Nat.cast_one]
      ring

private lemma weighted_sum_div_eq_sub_cesaro
    (z : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * z i) =
      ∑ i ∈ Finset.range n, z i -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, z j := by
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  rw [weighted_sum_eq]
  calc
    (n : ℝ)⁻¹ *
        ((n : ℝ) * ∑ i ∈ Finset.range n, z i -
          ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, z j) =
      (n : ℝ)⁻¹ * ((n : ℝ) * ∑ i ∈ Finset.range n, z i) -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, z j := by
          ring
    _ = ∑ i ∈ Finset.range n, z i -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, z j := by
          rw [← mul_assoc, inv_mul_cancel₀ hnR, one_mul]

omit [MeasurableSpace Ω] in
private lemma weighted_sum_div_eq_partialSum_sub_cesaro
    (Z : ℕ → Ω → ℝ) (ω : Ω) {n : ℕ} (hn : 0 < n) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * Z i ω) =
      partialSum Z n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, partialSum Z i ω := by
  let z : ℕ → ℝ := fun i ↦ Z i ω
  calc
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * Z i ω)
        = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * z i) := by
            simp [z]
    _ = ∑ i ∈ Finset.range n, z i -
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, z j := by
            exact weighted_sum_div_eq_sub_cesaro z hn
    _ = partialSum Z n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, partialSum Z i ω := by
            simp [partialSum, z]

-- Proof sketch: form the martingale with increments `(X (n + 1) - P[X (n + 1)]) / (n + 1)` and use
-- the summability of `Var[X (n + 1); P] / (n + 1)^2` to obtain an `L²`-bounded martingale, hence
-- almost sure convergence by the martingale convergence theorem; then apply Kronecker's lemma to
-- recover the almost sure convergence of the centered empirical averages.
/-- Exercise 11.2.2: the textbook sequence `X₁, X₂, …`, represented by `X 1, X 2, …`, satisfies
the strong law of large numbers whenever its terms are independent, square integrable, and the
series `∑ Var[Xₙ] / n²` is summable. -/
theorem satisfies_strong_law_of_large_numbers_of_iIndep_memLp_two_summable_variance
    (X : ℕ → Ω → ℝ) (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_memLp : ∀ n, MemLp (X (n + 1)) 2 P)
    (hX_var_summable : Summable (fun n : ℕ ↦ Var[X (n + 1); P] / (n + 1 : ℝ) ^ 2)) :
    satisfies_strong_law_of_large_numbers P (fun n ↦ X (n + 1)) := by
  let Z : ℕ → Ω → ℝ :=
    fun n ω ↦ ((n + 1 : ℝ)⁻¹) * (X (n + 1) ω - P[X (n + 1)])
  have hZ_indep : iIndepFun Z P := by
    let g : ℕ → ℝ → ℝ :=
      fun n x ↦ ((n + 1 : ℝ)⁻¹) * (x - P[X (n + 1)])
    simpa [Z, g, Function.comp] using hX_indep.comp g (fun _ ↦ by fun_prop)
  have hZ_memLp : ∀ n, MemLp (Z n) 2 P := by
    intro n
    simpa [Z] using ((hX_memLp n).sub (memLp_const _)).const_mul ((n + 1 : ℝ)⁻¹)
  have hZ_centered : ∀ n, P[Z n] = 0 := by
    intro n
    change P[fun ω ↦ ((n + 1 : ℝ)⁻¹) * (X (n + 1) ω - P[X (n + 1)])] = 0
    rw [integral_const_mul,
      integral_sub ((hX_memLp n).integrable (by norm_num)) (integrable_const _), integral_const]
    simp
  have hZ_var : ∀ n, Var[Z n; P] = Var[X (n + 1); P] / (n + 1 : ℝ) ^ 2 := by
    intro n
    change Var[fun ω ↦ ((n + 1 : ℝ)⁻¹) * (X (n + 1) ω - P[X (n + 1)]); P] = _
    rw [variance_const_mul]
    simp [variance_sub_const (hX_memLp n).aestronglyMeasurable, div_eq_mul_inv, pow_two,
      mul_assoc, mul_comm]
  have hZ_var_summable : Summable (fun n : ℕ ↦ Var[Z n; P]) := by
    simpa [hZ_var] using hX_var_summable
  obtain ⟨Y, _, hY_tendsto⟩ :=
    exists_memLp_two_ae_tendsto_partial_sums_of_iIndepFun_summable_variance
      P Z hZ_indep hZ_memLp hZ_centered hZ_var_summable
  refine ⟨fun n ↦ (hX_memLp n).integrable (by norm_num), ?_⟩
  filter_upwards [hY_tendsto] with ω hω
  have hCesaro :
      Tendsto
        (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, partialSum Z i ω)
        atTop (𝓝 (Y ω)) := by
    simpa [smul_eq_mul] using hω.cesaro
  have hBridge :
      Tendsto
        (fun n : ℕ ↦
          partialSum Z n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, partialSum Z i ω)
        atTop (𝓝 0) := by
    simpa using hω.sub hCesaro
  have hEq :
      (fun n ↦ centered_average P (fun k ↦ X (k + 1)) n ω) =ᶠ[atTop]
        (fun n : ℕ ↦
          partialSum Z n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, partialSum Z i ω) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : 0 < n := Nat.succ_le_iff.mp hn
    have hcentered :
        ∑ i ∈ Finset.range n, (X (i + 1) ω - P[X (i + 1)]) =
          ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * Z i ω) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hiR : (i + 1 : ℝ) ≠ 0 := by positivity
      simp [Z, hiR]
    calc
      centered_average P (fun k ↦ X (k + 1)) n ω
          = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((i + 1 : ℝ) * Z i ω) := by
            rw [centered_average, centered_partial_sum, div_eq_mul_inv, mul_comm, hcentered]
      _ = partialSum Z n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, partialSum Z i ω := by
            exact weighted_sum_div_eq_partialSum_sub_cesaro Z ω hn'
  exact Tendsto.congr' hEq.symm hBridge

/-! ### Theorem_11_2 (from Items/Chap11) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Finset

universe u

variable {Ω : Type u}

section DoobLp

variable {m0 : MeasurableSpace Ω}
variable {ℱ : Filtration ℕ m0} {μ : Measure Ω} [IsFiniteMeasure μ]
variable {X : ℕ → Ω → ℝ}

local macro:max "absMaxUpTo(" X:term ", " n:term ", " ω:term ")" : term =>
  `((range ($n + 1)).sup' nonempty_range_add_one fun k ↦ |($X k $ω)|)

local macro:max "terminalAbsRpow(" X:term ", " p:term ", " n:term ", " ω:term ")" : term =>
  `(Real.rpow |($X $n $ω)| $p)

local macro:max "absMaxUpToRpow(" X:term ", " p:term ", " n:term ", " ω:term ")" : term =>
  `(Real.rpow (absMaxUpTo($X, $n, $ω)) $p)

/- Theorem 11.2 is `source-facing`: it packages the textbook `L^p` corollaries of Doob's discrete
maximal inequality. Its `core/canonical` owner abstraction is `MeasureTheory.maximal_ineq`, and
its `bridge/view` layer for the transformed process `n ↦ |X n| ^ p` is the earlier project theorem
`submartingale_abs_rpow`; this file keeps only the source-level inequalities rather than a parallel
wrapper API for either ingredient. -/
recall MeasureTheory.maximal_ineq
recall submartingale_abs_rpow

/-- Theorem 11.2 (1): for a martingale or a nonnegative submartingale, Doob's `L^p` tail estimate
controls the event `{|X|*_n ≥ λ}` by the terminal `p`-th moment. -/
-- Proof sketch: if `X` is a martingale, apply the convex-function result from Theorem 9.35 to the
-- process `|X|^p`; if `X` is already a nonnegative submartingale, apply the same argument directly.
-- Then use Lemma 11.1, i.e. Doob's maximal inequality for nonnegative submartingales, with the
-- submartingale `k ↦ |X_k|^p`.
theorem doobLp_tail_bound
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X) {p threshold : ℝ}
    (hp : 1 ≤ p) (hthreshold : 0 < threshold)
    (n : ℕ) :
    ENNReal.ofReal (Real.rpow threshold p) *
        μ {ω | threshold ≤ absMaxUpTo(X, n, ω)} ≤
      ∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ := sorry

/-- Theorem 11.2 (2): for every nonnegative exponent `p`, the terminal `p`-th moment is bounded by
the `p`-th moment of the running maximal process. This is the left inequality in clause (ii),
isolated in the minimal exponent range actually used by its pointwise proof. -/
-- Proof sketch: for every `ω`, the terminal absolute value `|X n ω|` is one of the terms entering
-- the maximum `|X|*_n ω`, so pointwise monotonicity of `x ↦ x^p` on `ℝ≥0` for `p ≥ 0` and
-- monotonicity of the lower integral give the estimate.
theorem doobLp_terminalMoment_le_runningMaxMoment
    {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (absMaxUpToRpow(X, p, n, ω)) ∂μ := sorry

/-- Theorem 11.2 (3): for `p > 1`, the `p`-th moment of the running maximal process is bounded by
the classical Doob constant `(p / (p - 1))^p` times the terminal `p`-th moment. This is the right
inequality in clause (ii). -/
-- Proof sketch: integrate the tail estimate from clause (1) against `p λ^(p-1)`, truncate the
-- running maximum at level `K`, apply Hölder's inequality to the truncated moments, and then pass
-- to the limit `K → ∞`.
theorem doobLp_runningMaxMoment_le
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X) {p : ℝ} (hp : 1 < p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (absMaxUpToRpow(X, p, n, ω)) ∂μ ≤
      ENNReal.ofReal (Real.rpow (p / (p - 1)) p) *
        ∫⁻ ω, ENNReal.ofReal (terminalAbsRpow(X, p, n, ω)) ∂μ := sorry

end DoobLp

/-! ### Exercise_11_2_3 (from Items/Chap11) -/
open TopologicalSpace Filter MeasureTheory.Filtration
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

universe u

/- Exercise 11.2.3 is `source-facing`: it asserts the existence of a filtered probability space
carrying a square-integrable martingale that converges almost surely to its canonical limit process
without converging in `L²`. Its `core/canonical` owner layer is the chapter API around
`Martingale`, `Filtration.limitProcess`, and `TendstoInLp`; the `eLpNorm` formulation is only the
derived `bridge/view` from `tendstoInLp_iff_tendsto_eLpNorm`, so the main declaration stays owner-
shaped instead of exposing a parallel bridge-level interface. -/

-- Proof sketch: use a standard square-integrable martingale with almost-sure limit whose second
-- moments are not uniformly bounded, so Corollary 11.11 does not apply; then identify the almost-
-- sure limit with the canonical `limitProcess` and show that the `L²` distance to that limit does
-- not tend to `0`.
/-- Exercise 11.2.3: there exists a square-integrable martingale that converges almost surely to
its canonical limit process but does not converge to that limit in `L²`. -/
theorem exists_square_integrable_martingale_ae_tendsto_limitProcess_not_tendstoInLp_two :
    ∃ (Ω : Type u) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ),
        Martingale X ℱ μ ∧
          (∀ n, MemLp (X n) 2 μ) ∧
          (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
          ¬ TendstoInLp 2 μ X (ℱ.limitProcess X μ) := sorry

end MeasureTheory

/-! ### Exercise_11_2_4 (from Items/Chap11) -/
open TopologicalSpace Filter MeasureTheory.Filtration
open scoped ProbabilityTheory Topology

namespace MeasureTheory

universe u

/- Exercise 11.2.4 is `source-facing`: it gives a counterexample to the converse of
Theorem 11.14. Its `core/canonical` owner layer is the existing martingale API
`Martingale`, `MemLp`, `Filtration.limitProcess`, and the chapter's square-variation owner
`⟨X⟩[ℱ, μ]`. Since Theorem 11.14 is formulated with the owner hypothesis that
`⟨X⟩[ℱ, μ]` is almost surely bounded above along sample paths, the public statement below is kept
in that owner shape rather than via a parallel "finite limit" wrapper. -/

-- Proof sketch: choose a standard square-integrable martingale whose quadratic variation diverges
-- almost surely, for example a partial-sum martingale built from independent centered
-- square-integrable increments with infinite accumulated variance. The martingale convergence still
-- holds almost surely, but the canonical square variation is not almost surely bounded above,
-- equivalently it does not admit an almost surely finite real limit.
/-- Exercise 11.2.4: there exists a filtered probability space carrying a square-integrable
martingale that converges almost surely to its canonical limit process, but whose canonical square
variation `⟨X⟩[ℱ, μ]` is not almost surely bounded above along sample paths; equivalently, it does
not admit an almost surely finite real limit. -/
theorem exists_square_integrable_martingale_ae_tendsto_limitProcess_not_ae_bddAbove_squareVariation :
    ∃ (Ω : Type u) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ),
        Martingale X ℱ μ ∧
          (∀ n, MemLp (X n) 2 μ) ∧
          (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
          ¬ ∀ᵐ ω ∂μ, BddAbove (Set.range fun n ↦ ⟨X⟩[ℱ, μ] n ω) := sorry

end MeasureTheory

/-! ### Exercise_11_2_5 (from Items/Chap11) -/
open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

section

variable {X : ℕ → Ω → ℝ}

/-
Exercise 11.2.5 is `source-facing`: it compares the textbook pathwise properties usually denoted
`C`, `A⁺`, `A⁻`, and `F` for a real-valued martingale. Here the primitive data are only the
martingale `X` and the bounded-difference hypothesis. The `core/canonical` owner for the fourth
event is the chapter square-variation process `⟨X⟩[ℱ, μ]`, while formula-level identities such as
Theorem 10.4 are only `bridge/view` statements. The public theorem below therefore keeps the
owner event itself in the fourth clause instead of a parallel increment-sum presentation.
-/

-- Proof sketch: apply the canonical martingale Borel-Cantelli comparison between pathwise upper
-- and lower boundedness and convergence for bounded-difference martingales. The fourth clause is
-- stated directly in the owner shape from Chapter 10, so no parallel local square-variation API
-- survives in the public statement.
/-- Exercise 11.2.5: for a real-valued martingale with bounded differences, the textbook events
`C`, `A^+`, `A^-`, and `F` are almost surely equivalent. Equivalently, for almost every sample
point, the following are equivalent: the path converges in `ℝ`, its values are bounded above, its
values are bounded below, and the canonical square variation `n ↦ ⟨X⟩[ℱ, μ] n` is bounded above.
-/
theorem martingale_convergence_tfae_of_bdd_difference
    [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ)
    {R : ℝ≥0} (hbdd : ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ R) :
    ∀ᵐ ω ∂μ,
      List.TFAE [
        ∃ c : ℝ, Tendsto (fun n ↦ X n ω) atTop (𝓝 c),
        BddAbove (Set.range fun n ↦ X n ω),
        BddBelow (Set.range fun n ↦ X n ω),
        BddAbove (Set.range fun n ↦ ⟨X⟩[ℱ, μ] n ω)
      ] := sorry

end

/-! ### Exercise_11_2_6 (from Items/Chap11) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

section

variable {X : ℕ → Ω → ℝ}

local notation "incrementSupNorm" =>
  fun ω ↦ ⨆ n : ℕ, ENNReal.ofReal |X (n + 1) ω - X n ω|
local notation "Converges" =>
  fun ω ↦ ∃ c : ℝ, Tendsto (fun n ↦ X n ω) atTop (𝓝 c)
local notation "PathBddAbove" =>
  fun ω ↦ BddAbove (Set.range fun n ↦ X n ω)
local notation "PathBddBelow" =>
  fun ω ↦ BddBelow (Set.range fun n ↦ X n ω)

/- Exercise 11.2.6 is `source-facing`: it upgrades Exercise 11.2.5 from uniformly bounded
increments to the weaker hypothesis that the pathwise increment envelope has finite expectation.
Its `core/canonical` owner layer is still the martingale convergence API around `Martingale`,
`Submartingale.ae_tendsto_limitProcess`, and the pathwise boundedness/convergence predicates
isolated in Exercise 11.2.5. The increment envelope is only a local `bridge/view` quantity, so it
should not survive as a separate public owner-level definition here. -/

-- Proof sketch: for each level `K`, stop the martingale at a suitable time `ρ_K` before the
-- increment envelope exceeds `K`; the stopped martingale then has uniformly bounded increments, so
-- Exercise 11.2.5 and the martingale convergence theorem apply to it. Letting `K → ∞` and using
-- the integrability of `sup_n |X_{n+1} - X_n|` shows that the stopping events exhaust almost every
-- sample path, yielding the claimed three-way equivalence almost surely.
/-- Exercise 11.2.6: if a real-valued martingale has finite expectation of the supremum of its
absolute increments, then almost every sample path satisfies the same three-way equivalence between
convergence and one-sided boundedness as in Exercise 11.2.5. -/
theorem martingale_convergence_tfae_of_integrable_increment_sup
    (hX : Martingale X ℱ μ)
    (hinc : (∫⁻ ω, incrementSupNorm ω ∂μ) < (⊤ : ENNReal)) :
    ∀ᵐ ω ∂μ,
      List.TFAE [Converges ω, PathBddAbove ω, PathBddBelow ω] := sorry

end

/-! ### Exercise_11_2_7 (from Items/Chap11) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory symmDiff

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

section

variable {A : ℕ → Set Ω}

/- Exercise 11.2.7 is `bridge/view`: the `core/canonical` owner is the almost-everywhere event
equality from `MeasureTheory.ae_mem_limsup_atTop_iff`, while the textbook symmetric-difference
formulation is the derived measure-level view given by `measure_symmDiff_eq_zero_iff`. The recall
below records that owner theorem directly, and the subsequent declarations keep only the thin
source-facing companions needed in this file. -/
-- Proof sketch: pad the event sequence by the dummy initial term `∅`, apply
-- `MeasureTheory.ae_mem_limsup_atTop_iff` to that padded sequence, and use the fact that changing
-- finitely many initial terms does not change `limsup`. This identifies `limsup A atTop` almost
-- everywhere with the event that the partial sums of the conditional probabilities
-- `μ⟦A (k + 1) | ℱ k⟧` tend to `+∞`. Then rewrite that almost everywhere equivalence as vanishing
-- symmetric-difference measure using
-- `MeasureTheory.measure_symmDiff_eq_zero_iff`.
recall MeasureTheory.ae_mem_limsup_atTop_iff

/-- Exercise 11.2.7, source-facing AE form: the divergence event for
`∑ μ⟦A (n + 1) | ℱ n⟧` is almost surely equivalent to `limsup A atTop`. Only the tail
measurability assumptions `A (n + 1) ∈ ℱ (n + 1)` are needed; the finite initial term `A 0`
plays no role. -/
theorem conditionalBorelCantelliEvent_ae_iff_mem_limsup
    (hA : ∀ n, MeasurableSet[ℱ (n + 1)] (A (n + 1))) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n ↦ ∑ k ∈ Finset.range n, (μ⟦A (k + 1) | ℱ k⟧) ω)
      atTop atTop ↔ ω ∈ limsup A atTop := by
  let s : ℕ → Set Ω
    | 0 => ∅
    | n + 1 => A (n + 1)
  have hs : ∀ n, MeasurableSet[ℱ n] (s n) := by
    intro n
    cases n with
    | zero =>
        simp [s]
    | succ n =>
        simpa [s] using hA n
  have hs_shift : (fun n ↦ s (n + 1)) = fun n ↦ A (n + 1) := by
    funext n
    simp [s]
  have hlimsup : limsup s atTop = limsup A atTop := by
    rw [← limsup_nat_add s 1, ← limsup_nat_add A 1, hs_shift]
  filter_upwards [ae_mem_limsup_atTop_iff μ hs] with ω hω
  simpa [hlimsup, s] using hω.symm

/-- Exercise 11.2.7: for a filtration `(ℱ n)` and events `A n ∈ ℱ n`, the event that the series
of conditional probabilities `∑ μ⟦A (n + 1) | ℱ n⟧` diverges to `+∞` agrees almost surely with
the tail event `limsup A atTop`; equivalently, their symmetric difference has measure zero. -/
theorem measure_conditionalBorelCantelliEvent_symmDiff_limsup_eq_zero
    (hA : ∀ n, MeasurableSet[ℱ (n + 1)] (A (n + 1))) :
    μ
      ({ω | Tendsto
          (fun n ↦ ∑ k ∈ Finset.range n, (μ⟦A (k + 1) | ℱ k⟧) ω)
          atTop atTop} ∆
        limsup A atTop) = 0 := by
  exact measure_symmDiff_eq_zero_iff.mpr <|
    eventuallyEq_set.2 (conditionalBorelCantelliEvent_ae_iff_mem_limsup hA)

end

/-! ### Exercise_11_2_8 (from Items/Chap11) -/
open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/- Exercise 11.2.8 is `source-facing`: it describes a `{0,1}`-valued real process together with
its one-step conditional law. The public owner abstraction is therefore the transition-law
predicate `exercise1128Transition`, which packages both the binary state-space restriction and the
displayed conditional law along the natural filtration. The ambient-`ℝ` two-point row kernel below
is auxiliary support code for that statement, so it stays private. -/

private theorem exercise1128RowKernel_measurable (p : ℝ) :
    Measurable
      (fun x : ℝ ↦
        (ENNReal.ofReal x • Measure.dirac (1 - p + p * x) +
          ENNReal.ofReal (1 - x) • Measure.dirac (p * x) : Measure ℝ)) := by
  have h_left : Measurable (fun x : ℝ ↦ 1 - p + p * x) := by
    fun_prop
  have h_right : Measurable (fun x : ℝ ↦ p * x) := by
    fun_prop
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hs]
  refine Measurable.add ?_ ?_
  · refine measurable_id.ennreal_ofReal.mul ?_
    exact (measurable_const.indicator hs).comp h_left
  · refine (measurable_const.sub measurable_id).ennreal_ofReal.mul ?_
    exact (measurable_const.indicator hs).comp h_right

private def exercise1128RowKernel (p : ℝ) : Kernel ℝ ℝ where
  toFun x :=
    ENNReal.ofReal x • Measure.dirac (1 - p + p * x) +
      ENNReal.ofReal (1 - x) • Measure.dirac (p * x)
  measurable' := exercise1128RowKernel_measurable p

/-- The source-facing transition law from Exercise 11.2.8: with respect to the natural filtration
of `X`, the process is `{0,1}`-valued and the conditional law of `X_{n+1}` is the canonical
two-point law determined by `X_n` and `p`. -/
def exercise1128Transition (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (X : ℕ → Ω → ℝ) (hX_meas : ∀ n, Measurable (X n)) : Prop :=
  let ℱ := Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable
  (∀ n ω, X n ω ∈ ({0, 1} : Set ℝ)) ∧
    ∀ n ⦃s : Set ℝ⦄, MeasurableSet s →
      μ⟦X (n + 1) ⁻¹' s | ℱ n⟧ =ᵐ[μ] fun ω ↦ (exercise1128RowKernel p (X n ω)).real s

/-- A process satisfying `exercise1128Transition` is `{0,1}`-valued at every time. -/
theorem exercise1128Transition_binary {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    ∀ n ω, X n ω ∈ ({0, 1} : Set ℝ) :=
  hX_transition.1

private theorem exercise1128Transition_conditionalLaw {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    let ℱ := Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable
    ∀ n ⦃s : Set ℝ⦄, MeasurableSet s →
      μ⟦X (n + 1) ⁻¹' s | ℱ n⟧ =ᵐ[μ] fun ω ↦ (exercise1128RowKernel p (X n ω)).real s :=
  hX_transition.2

-- Proof sketch: if `x ∈ {0, 1}`, exactly one of the two weights in `exercise1128RowKernel p x`
-- is `1` and the other is `0`, so the two-point law reduces to the Dirac mass at `x`.
private theorem exercise1128RowKernel_eq_dirac_of_mem_zero_one {p x : ℝ}
    (hx : x ∈ ({0, 1} : Set ℝ)) :
    exercise1128RowKernel p x = Measure.dirac x := sorry

-- Proof sketch: under the conditional-law hypothesis, the one-step conditional law of
-- `X_{n + 1}` is `exercise1128RowKernel p (X n ω)` along the natural filtration. The binary part
-- of `exercise1128Transition` identifies this with `Measure.dirac (X n ω)` via
-- `exercise1128RowKernel_eq_dirac_of_mem_zero_one`,
-- `Measure.dirac (X n ω)`, so `X_{n + 1}` and `X_n` agree almost surely.
/-- For a process satisfying the source-facing Exercise 11.2.8 transition law,
consecutive time slices coincide almost everywhere. -/
theorem exercise1128_succ_ae_eq_self {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) (n : ℕ) :
    X (n + 1) =ᵐ[μ] X n := sorry

-- Proof sketch: iterate the one-step almost-everywhere identity from the previous lemma and use
-- transitivity of `=ᵐ[μ]` to show inductively that every time slice agrees almost everywhere with
-- the initial value.
/-- A process satisfying the Exercise 11.2.8 transition law is constant in time up to
almost-everywhere equality, with time slices equal almost everywhere to the initial state. -/
theorem exercise1128_ae_eq_initial {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) (n : ℕ) :
    X n =ᵐ[μ] X 0 := sorry

-- Proof sketch: `exercise1128_succ_ae_eq_self` gives the one-step almost-everywhere identity
-- needed by `MeasureTheory.martingale_nat` for the natural filtration; strong measurability comes
-- from `hX_meas`, and integrability follows from boundedness of the binary-valued process supplied
-- by `exercise1128Transition`.
/-- Exercise 11.2.8 (1): a real-valued process satisfying the displayed binary transition law from
the exercise is a martingale with respect to its natural filtration. -/
theorem binary_transition_process_martingale {p : ℝ}
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    Martingale X (Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable) μ := sorry

-- Proof sketch: `exercise1128_ae_eq_initial` yields a countable family of almost-everywhere
-- equalities. Intersecting the corresponding full-measure sets gives a full-measure set on which
-- every time slice equals `X 0`, so the sample paths converge there to `X 0`.
/-- Exercise 11.2.8 (2): under the same binary transition hypotheses, the process converges almost
surely, and its almost sure limit is the initial random variable `X 0`. -/
theorem binary_transition_process_ae_tendsto_initial {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (X 0 ω)) := sorry

-- Proof sketch: combine `binary_transition_process_martingale` with the previous almost-sure
-- convergence statement to identify the natural-filtration limit process with `X 0` almost
-- everywhere, then use `HasLaw.congr`.
/-- Exercise 11.2.8 (3): the canonical almost sure limit of the process has the same distribution
as the initial state `X 0`. -/
theorem binary_transition_process_limitProcess_hasLaw_initial {p : ℝ}
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    HasLaw
      ((Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable).limitProcess X μ)
      (μ.map (X 0)) μ := sorry

end ProbabilityTheory

/-! ### Exercise_11_2_9 (from Items/Chap11) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

noncomputable section

local notation "unitIntervalLebesgue" => volume.restrict (Set.Icc (0 : ℝ) 1)

local instance : IsProbabilityMeasure unitIntervalLebesgue := by
  refine ⟨by
    simp [Real.volume_Icc]
  ⟩

/-- The `k`-th dyadic half-open subinterval of `[0,1)` at level `n`. -/
def dyadicInterval (n : ℕ) (k : Fin (2 ^ n)) : Set ℝ :=
  Set.Ico ((k : ℝ) / (2 : ℝ) ^ n) (((k : ℕ) + 1 : ℕ) / (2 : ℝ) ^ n)

private def dyadicCompletionResidualSet (n : ℕ) : Set ℝ :=
  (⋃ k : Fin (2 ^ n), dyadicInterval n k)ᶜ

private def dyadicCompletionAtom (n : ℕ) : Option (Fin (2 ^ n)) → Set ℝ
  | some k => dyadicInterval n k
  | none => dyadicCompletionResidualSet n

private theorem measurableSet_dyadicInterval (n : ℕ) (k : Fin (2 ^ n)) :
    MeasurableSet (dyadicInterval n k) := by
  simp [dyadicInterval]

private theorem measurableSet_dyadicCompletionResidualSet (n : ℕ) :
    MeasurableSet (dyadicCompletionResidualSet n) := by
  rw [dyadicCompletionResidualSet]
  exact (MeasurableSet.iUnion fun k ↦ measurableSet_dyadicInterval n k).compl

private theorem measurableSet_dyadicCompletionAtom (n : ℕ) (i : Option (Fin (2 ^ n))) :
    MeasurableSet (dyadicCompletionAtom n i) := by
  cases i with
  | none =>
      simpa [dyadicCompletionAtom] using measurableSet_dyadicCompletionResidualSet n
  | some k =>
      simpa [dyadicCompletionAtom] using measurableSet_dyadicInterval n k

private theorem measurableSet_dyadicCompletionResidualSet_generateFrom (n : ℕ) :
    MeasurableSet[MeasurableSpace.generateFrom (Set.range (dyadicInterval n))]
      (dyadicCompletionResidualSet n) := by
  rw [dyadicCompletionResidualSet]
  refine (MeasurableSet.iUnion fun k ↦ ?_).compl
  exact MeasurableSpace.measurableSet_generateFrom
    (show dyadicInterval n k ∈ Set.range (dyadicInterval n) from ⟨k, rfl⟩)

private theorem generateFrom_dyadicCompletionAtom_eq (n : ℕ) :
    MeasurableSpace.generateFrom (Set.range (dyadicCompletionAtom n)) =
      MeasurableSpace.generateFrom (Set.range (dyadicInterval n)) := by
  refine le_antisymm ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨i, rfl⟩
    cases i with
    | none =>
        exact measurableSet_dyadicCompletionResidualSet_generateFrom n
    | some k =>
        exact MeasurableSpace.measurableSet_generateFrom
          (show dyadicInterval n k ∈ Set.range (dyadicInterval n) from ⟨k, rfl⟩)
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨k, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom
      (show dyadicCompletionAtom n (Option.some k) ∈ Set.range (dyadicCompletionAtom n) from
        ⟨Option.some k, rfl⟩)

private theorem dyadicFiltration_mono :
    Monotone fun n : ℕ ↦ MeasurableSpace.generateFrom (Set.range (dyadicInterval n)) := by
  intro i j hij
  sorry

/-- The canonical filtration whose `n`-th stage is generated by the level-`n` dyadic intervals on
`[0,1)`. -/
def dyadicFiltration : Filtration ℕ (borel ℝ) where
  seq n := MeasurableSpace.generateFrom (Set.range (dyadicInterval n))
  mono' := dyadicFiltration_mono
  le' n := MeasurableSpace.generateFrom_le fun s hs ↦ by
    rcases hs with ⟨k, rfl⟩
    exact measurableSet_dyadicInterval n k

/-- The `n`-th dyadic averaging approximation of a function on `[0,1]`, extended by `0` off the
level-`n` dyadic cells. -/
def dyadicAverageApproximation (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x ↦
    ∑ k : Fin (2 ^ n),
      Set.indicator
        (dyadicInterval n k)
        (fun _ ↦
          ((2 : ℝ) ^ n) *
            (∫ y in dyadicInterval n k, f y ∂unitIntervalLebesgue))
        x

/-- The textbook dyadic approximation agrees with the owner-style partition formula obtained by
taking the `unitIntervalLebesgue`-average of `f` on each dyadic atom. -/
theorem dyadicAverageApproximation_eq_partitionFormula (f : ℝ → ℝ) (n : ℕ) :
    dyadicAverageApproximation f n =
      fun x ↦
        ∑ k : Fin (2 ^ n),
          Set.indicator (dyadicInterval n k)
            (fun _ ↦ ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue) x := by
  sorry

/-- The dyadic averaging approximation is the source-facing realization of the canonical
conditional expectation onto the σ-algebra generated by the level-`n` dyadic intervals. -/
theorem dyadicAverageApproximation_ae_eq_condExp {f : ℝ → ℝ}
    (hf : Integrable f unitIntervalLebesgue) (n : ℕ) :
    dyadicAverageApproximation f n =ᵐ[unitIntervalLebesgue]
      unitIntervalLebesgue[f | dyadicFiltration n] := by
  rw [dyadicAverageApproximation_eq_partitionFormula]
  have h_formula' :
      unitIntervalLebesgue[f |
          MeasurableSpace.generateFrom (Set.range (dyadicCompletionAtom n))] =ᵐ[unitIntervalLebesgue]
        fun x ↦
          Set.indicator (dyadicCompletionResidualSet n)
              (fun _ ↦ ⨍ y in dyadicCompletionResidualSet n, f y ∂unitIntervalLebesgue) x +
            ∑ k : Fin (2 ^ n),
              Set.indicator (dyadicInterval n k)
                (fun _ ↦ ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue) x := by
    simpa [dyadicCompletionAtom, dyadicCompletionResidualSet, dyadicInterval] using
      (condExp_generateFrom_ae_eq_countable_partition_formula
        unitIntervalLebesgue (dyadicCompletionAtom n)
        (by
          intro i
          exact measurableSet_dyadicCompletionAtom n i)
        (by sorry) (by sorry) hf)
  have h_formula :
      unitIntervalLebesgue[f | dyadicFiltration n] =ᵐ[unitIntervalLebesgue]
        fun x ↦
          Set.indicator (dyadicCompletionResidualSet n)
              (fun _ ↦ ⨍ y in dyadicCompletionResidualSet n, f y ∂unitIntervalLebesgue) x +
            ∑ k : Fin (2 ^ n),
              Set.indicator (dyadicInterval n k)
                (fun _ ↦ ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue) x := by
    simpa [dyadicFiltration, generateFrom_dyadicCompletionAtom_eq n] using h_formula'
  have h_residual :
      (fun x ↦
          Set.indicator (dyadicCompletionResidualSet n)
              (fun _ ↦ ⨍ y in dyadicCompletionResidualSet n, f y ∂unitIntervalLebesgue) x +
            ∑ k : Fin (2 ^ n),
              Set.indicator (dyadicInterval n k)
                (fun _ ↦ ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue) x) =ᵐ[unitIntervalLebesgue]
        fun x ↦
          ∑ k : Fin (2 ^ n),
            Set.indicator (dyadicInterval n k)
              (fun _ ↦ ⨍ y in dyadicInterval n k, f y ∂unitIntervalLebesgue) x := by
    sorry
  exact (h_formula.trans h_residual).symm

-- Proof sketch: the source-facing dyadic filtration records the σ-algebras generated by the
-- dyadic interval families. The preceding bridge identifies `dyadicAverageApproximation f n` with
-- `𝔼[f | dyadicFiltration n]`, and the dyadic σ-algebras increase to the full Borel σ-algebra on
-- `[0,1]`. Lévy's upward theorem in the form `Integrable.tendsto_ae_condExp` then yields
-- almost-everywhere convergence to `f`.
/-- Exercise 11.2.9: for an integrable function on `[0,1]`, the dyadic interval averages converge
almost everywhere to the original function. -/
theorem ae_tendsto_dyadicAverageApproximation_of_integrable {f : ℝ → ℝ}
    (hf : Integrable f unitIntervalLebesgue) :
    ∀ᵐ x ∂unitIntervalLebesgue,
      Tendsto (fun n ↦ dyadicAverageApproximation f n x) atTop (𝓝 (f x)) := by
  have hf_meas : StronglyMeasurable[⨆ n, dyadicFiltration n] f := by
    sorry
  have h_eq :
      ∀ᵐ x ∂unitIntervalLebesgue, ∀ n,
        dyadicAverageApproximation f n x = unitIntervalLebesgue[f | dyadicFiltration n] x := by
    rw [ae_all_iff]
    intro n
    simpa using dyadicAverageApproximation_ae_eq_condExp hf n
  filter_upwards [h_eq, hf.tendsto_ae_condExp hf_meas] with x hx hcond
  simpa [hx] using hcond

end

end MeasureTheory

/-! ### Exercise_11_2_10 (from Items/Chap11) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section

variable (μ : Measure Ω) [IsFiniteMeasure μ]
variable (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)

local notation "TerminalValueSpace" => lpMeas ℝ ℝ (⨆ n, ℱ n) 1 μ
local notation "ProcessSpace" => ℕ → Lp ℝ 1 μ

/- Exercise 11.2.10 is `source-facing`: it identifies the actual vector space of uniformly
integrable `ℱ`-martingales with the terminal-value space `L¹(⨆ n, ℱ n)`. The
`core/canonical` owner abstractions are the existing martingale and uniform-integrability APIs on
processes, together with the `L¹` conditional-expectation operator `condExpL1CLM`. The quotient
level codomain is therefore organized as the submodule of `L¹`-classes admitting an actual
uniformly integrable martingale representative, while the conditional-expectation process map is
the `bridge/view` from a terminal class to that submodule. -/

/-- The `Lp`-valued conditional-expectation martingale attached to an `L¹(ℱ∞)` terminal class. -/
noncomputable def terminalValueMartingaleProcess :
    TerminalValueSpace →ₗ[ℝ] ProcessSpace where
  toFun X := fun n ↦ condExpL1CLM ℝ (ℱ.le n) μ (X : Lp ℝ 1 μ)
  map_add' := by
    intro X Y
    funext n
    exact map_add (condExpL1CLM ℝ (ℱ.le n) μ) (X : Lp ℝ 1 μ) (Y : Lp ℝ 1 μ)
  map_smul' := by
    intro c X
    funext n
    exact map_smul (condExpL1CLM ℝ (ℱ.le n) μ) c (X : Lp ℝ 1 μ)

/-- A quotient-level process is a uniformly integrable `ℱ`-martingale if it admits an actual
uniformly integrable martingale representative. -/
def IsUiMartingaleProcess (f : ProcessSpace) : Prop :=
  ∃ X : ℕ → Ω → ℝ, Martingale X ℱ μ ∧ UniformIntegrable X 1 μ ∧
    ∀ n, (f n : Ω → ℝ) =ᵐ[μ] X n

omit [IsFiniteMeasure μ] in
private theorem uniformIntegrable_zero_process :
    UniformIntegrable (0 : ℕ → Ω → ℝ) 1 μ := by
  refine ⟨fun _ ↦ aestronglyMeasurable_zero, ?_, ⟨0, fun _ ↦ by simp⟩⟩
  intro ε hε
  refine ⟨1, zero_lt_one, fun _ _ _ _ ↦ by simp⟩

omit [IsFiniteMeasure μ] in
private theorem uniformIntegrable_add {f g : ℕ → Ω → ℝ}
    (hf : UniformIntegrable f 1 μ) (hg : UniformIntegrable g 1 μ) :
    UniformIntegrable (f + g) 1 μ := by
  refine ⟨fun n ↦ (hf.aestronglyMeasurable n).add (hg.aestronglyMeasurable n), ?_, ?_⟩
  · exact hf.unifIntegrable.add hg.unifIntegrable le_rfl
      (fun n ↦ hf.aestronglyMeasurable n) (fun n ↦ hg.aestronglyMeasurable n)
  · rcases hf.2.2 with ⟨Cf, hCf⟩
    rcases hg.2.2 with ⟨Cg, hCg⟩
    refine ⟨Cf + Cg, fun n ↦ ?_⟩
    exact (eLpNorm_add_le (hf.aestronglyMeasurable n) (hg.aestronglyMeasurable n) le_rfl).trans
      (add_le_add (hCf n) (hCg n))

private theorem uniformIntegrable_smul (c : ℝ) {f : ℕ → Ω → ℝ}
    (hf : UniformIntegrable f 1 μ) :
    UniformIntegrable (c • f) 1 μ := by
  sorry

/-- The quotient-level vector space of uniformly integrable `ℱ`-martingales. -/
def uiMartingaleSubmodule : Submodule ℝ ProcessSpace where
  carrier := {f | IsUiMartingaleProcess μ ℱ f}
  zero_mem' := by
    refine ⟨0, martingale_zero ℝ ℱ μ, uniformIntegrable_zero_process μ,
      fun _ ↦ Lp.coeFn_zero ℝ 1 μ⟩
  add_mem' := by
    sorry
  smul_mem' := by
    sorry

local notation "UiMartingaleSpace" => uiMartingaleSubmodule μ ℱ

/-- Each terminal `L¹(ℱ∞)` class yields a uniformly integrable martingale after taking its
conditional expectations. -/
theorem terminalValueMartingaleProcess_is_ui_martingale (X : TerminalValueSpace) :
    Martingale (fun n ↦ terminalValueMartingaleProcess μ ℱ X n) ℱ μ ∧
      UniformIntegrable (fun n ↦ terminalValueMartingaleProcess μ ℱ X n) 1 μ := by
  sorry

private theorem terminalValueMartingaleProcess_mem_uiMartingaleSubmodule (X : TerminalValueSpace) :
    terminalValueMartingaleProcess μ ℱ X ∈ UiMartingaleSpace := by
  refine ⟨fun n ↦ terminalValueMartingaleProcess μ ℱ X n,
    (terminalValueMartingaleProcess_is_ui_martingale μ ℱ X).1,
    (terminalValueMartingaleProcess_is_ui_martingale μ ℱ X).2,
    fun _ ↦ .of_forall fun _ ↦ rfl⟩

/-- Source-facing form of Exercise 11.2.10: a quotient-level `L¹` process lies in the canonical
space of uniformly integrable martingales exactly when it is the conditional-expectation
martingale of some terminal `L¹(ℱ∞)` class. -/
theorem mem_uiMartingaleSpace_iff_exists_terminalValue (f : ProcessSpace) :
    f ∈ UiMartingaleSpace ↔
      ∃ X : TerminalValueSpace, ∀ n, f n = terminalValueMartingaleProcess μ ℱ X n := by
  sorry

private theorem terminalValueMartingaleProcess_injective :
    Function.Injective (terminalValueMartingaleProcess μ ℱ) := by
  intro X Y hXY
  sorry

/-- Exercise 11.2.10: the vector space of uniformly integrable `ℱ`-martingales is linearly
equivalent to the terminal-value space `L¹(⨆ n, ℱ n)`. -/
noncomputable def terminalValueToUiMartingale :
    TerminalValueSpace →ₗ[ℝ] UiMartingaleSpace where
  toFun X := ⟨terminalValueMartingaleProcess μ ℱ X,
    terminalValueMartingaleProcess_mem_uiMartingaleSubmodule μ ℱ X⟩
  map_add' := by
    sorry
  map_smul' := by
    sorry

/-- Exercise 11.2.10: the canonical bridge from terminal `L¹(ℱ∞)` classes to uniformly
integrable `ℱ`-martingales is a linear isomorphism. -/
noncomputable def terminalValueToUiMartingale_isomorphism :
    TerminalValueSpace ≃ₗ[ℝ] UiMartingaleSpace := by
  refine LinearEquiv.ofBijective (terminalValueToUiMartingale μ ℱ) ?_
  constructor
  · intro X Y hXY
    exact terminalValueMartingaleProcess_injective μ ℱ (by
      simpa [terminalValueToUiMartingale] using congrArg Subtype.val hXY)
  · intro f
    rcases (mem_uiMartingaleSpace_iff_exists_terminalValue μ ℱ f.1).mp f.2 with
      ⟨X, hX⟩
    refine ⟨X, ?_⟩
    apply Subtype.ext
    funext n
    exact (hX n).symm

/-- The linear equivalence is induced by the canonical conditional-expectation process map. -/
theorem terminalValueToUiMartingale_isomorphism_apply (X : TerminalValueSpace) :
    terminalValueToUiMartingale_isomorphism μ ℱ X =
      terminalValueToUiMartingale μ ℱ X :=
  rfl

end
