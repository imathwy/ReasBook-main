import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_42
import ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_2
import ProbabilityTheory_Klenke_2020.Items.Chap22.Remark_22_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/- Theorem 22.9 is `source-facing`: its binary-branching hypothesis is expressed through the
existing Chapter 9 owner `IsBinaryModel`, applied to each finite truncation of the martingale,
and its conclusion is the direct existence of Brownian stopping times with the stated law and
second-moment properties. The `core/canonical` ingredients on the conclusion side are the
natural-filtration stopping-time predicate, `IdentDistrib`, the Chapter 7 owner `TendstoInLp 2`,
and the canonical martingale terminal random variable `limitProcess`; there is no separate
Brownian-embedding owner to package here. -/

section BinaryModelMartingale

variable {X : ℕ → Ω → ℝ}
variable (hX_binary : ∀ T, IsBinaryModel (fun i : Fin (T + 1) ↦ X i.1))

local notation "ℱX" => Filtration.natural X
  (ProbabilityTheory.binaryModelTruncations_stronglyMeasurable hX_binary)
local notation "X∞" => Filtration.limitProcess X ℱX μ

-- Proof sketch: realize each binary split of the martingale as the next exit value of Brownian
-- motion from the two corresponding branch levels. The strong Markov property preserves the
-- conditional branch probabilities, and the two-sided Brownian exit-time formula yields
-- `E[τₙ] = E[Xₙ²]`.
/-- Theorem 22.9 (1): if `X` is a discrete martingale whose finite truncations are Chapter 9
binary models, with `X₀ = 0`, and `B` is Brownian motion with its canonical filtration, then
there exists an increasing sequence of canonical stopping times `τₙ` starting from `0` such that
`(Xₙ)ₙ` and `(B_{τₙ})ₙ` have the same law and `E[τₙ] = E[Xₙ²]` for every `n`. -/
theorem exists_brownian_stopping_embedding_of_binary_splitting_martingale
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {X : ℕ → Ω → ℝ}
    (hX_binary : ∀ T, IsBinaryModel (fun i : Fin (T + 1) ↦ X i.1))
    (hX_mart : Martingale X ℱX μ) (hX0 : X 0 = 0) :
    ∃ τ : ℕ → Ω → NNReal,
      τ 0 = 0 ∧
      (∀ n,
        IsStoppingTime (Filtration.natural B hB.stronglyMeasurable)
          (fun ω ↦ (τ n ω : ENNReal))) ∧
      Monotone τ ∧
      IdentDistrib (fun ω n ↦ X n ω) (fun ω n ↦ B (τ n ω) ω) μ μ ∧
      (∀ n, μ[fun ω ↦ (τ n ω : ℝ)] = μ[fun ω ↦ (X n ω) ^ 2]) := sorry

-- Proof sketch: start from the embedding of part (1). A finite uniform `L²` bound gives
-- almost-sure and `L²` convergence of the discrete martingale to a square-integrable limit.
-- Monotone convergence
-- for the increasing times identifies the expectation of `supₙ τₙ` with the variance of the
-- limit, and continuity of Brownian paths yields the terminal distributional identity.
/-- Theorem 22.9 (2): if, in addition, the binary-model martingale `X` is bounded in `L²`, then
one can choose the embedding stopping times `τₙ` so that `X` converges almost surely and in `L²`
to its canonical martingale limit `X∞`, the limit time `supₙ τₙ` is almost surely finite, its
expectation is `Var[X∞]`, and that
canonical limit has the law of the Brownian stopped value at the limit time. -/
theorem exists_brownian_limit_embedding_of_l2_bounded_binary_splitting_martingale
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {X : ℕ → Ω → ℝ}
    (hX_binary : ∀ T, IsBinaryModel (fun i : Fin (T + 1) ↦ X i.1))
    (hX_mart : Martingale X ℱX μ) (hX0 : X 0 = 0)
    (hX_l2_bdd : ∃ C : NNReal, ∀ n, eLpNorm (X n) 2 μ ≤ C) :
    ∃ τ : ℕ → Ω → NNReal,
      let tauLimit : Ω → ENNReal := fun ω ↦ ⨆ n : ℕ, ((τ n ω : NNReal) : ENNReal);
      τ 0 = 0 ∧
      (∀ n,
        IsStoppingTime (Filtration.natural B hB.stronglyMeasurable)
          (fun ω ↦ (τ n ω : ENNReal))) ∧
      Monotone τ ∧
      IdentDistrib (fun ω n ↦ X n ω) (fun ω n ↦ B (τ n ω) ω) μ μ ∧
      (∀ n, μ[fun ω ↦ (τ n ω : ℝ)] = μ[fun ω ↦ (X n ω) ^ 2]) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (X∞ ω))) ∧
        TendstoInLp 2 μ X X∞ ∧
        (∀ᵐ ω ∂μ, tauLimit ω < ⊤) ∧
        μ[fun ω ↦ (tauLimit ω).toReal] = Var[X∞; μ] ∧
        IdentDistrib X∞ (stoppedValue B tauLimit) μ μ :=
      sorry

end BinaryModelMartingale

end ProbabilityTheory
