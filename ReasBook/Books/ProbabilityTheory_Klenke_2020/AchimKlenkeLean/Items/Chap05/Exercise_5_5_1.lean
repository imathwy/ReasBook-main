import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap05.Definition_5_33
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap05.Theorem_5_35

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory unitInterval

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

private noncomputable def blockMarkToUnitInterval {n : ℕ} :
    Set.Ioc (n : ℝ) (n + 1) → I
  | x =>
      ⟨(x : ℝ) - n, by
        constructor
        · linarith [x.2.1]
        · linarith [x.2.2]⟩

private noncomputable def unitIntervalBlockMarks
    (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1)) (n : ℕ) :
    ℕ → Ω → I :=
  fun k ω ↦ blockMarkToUnitInterval (X n (k - 1) ω)

private noncomputable def lastBlockTime (t : NNReal) (n : ℕ)
    (hn : n = Nat.floor (t : ℝ)) : I :=
  ⟨(t : ℝ) - n, by
    constructor
    · have hn_le : (n : ℝ) ≤ t := by
        rw [hn]
        exact_mod_cast Nat.floor_le t.2
      linarith
    · have ht_lt : (t : ℝ) < Nat.floor (t : ℝ) + 1 := by
        simpa using Nat.lt_floor_add_one (t : ℝ)
      rw [← hn] at ht_lt
      linarith⟩

/-- The counting process from Exercise 5.5.1, written in the canonical `0`-based Lean indexing of
the textbook families `L₁, L₂, …` and `X₁¹, X₂¹, …`. Thus `L n` represents `L_(n+1)` and
`X n k` represents `X_(k+1)^(n+1)`. The implementation reuses the chapter's canonical
unit-interval counting process blockwise after translating the block `(n, n + 1]` to `(0,1]`,
and evaluates the last block at the local time `t - ⌊t⌋`. -/
noncomputable def poissonizedUniformBlockCountingProcess
    (L : ℕ → Ω → ℕ) (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1)) :
    NNReal → Ω → ℕ :=
  fun t ω ↦
    Finset.sum (Finset.range (Nat.floor (t : ℝ) + 1)) fun n ↦
      poissonizedUniformCountingProcess (L n) (unitIntervalBlockMarks X n)
        (if hn : n = Nat.floor (t : ℝ) then lastBlockTime t n hn else 1) ω

section

omit [MeasurableSpace Ω] in
/-- The blockwise Poissonized counting process is the cardinality of the set of `0`-based
block/mark pairs `(n, k)` with `n ≤ ⌊t⌋`, `k < L n`, and `X n k ≤ t`, written as a finite
blockwise sum. -/
theorem poissonizedUniformBlockCountingProcess_apply
    (L : ℕ → Ω → ℕ) (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (t : NNReal) (ω : Ω) :
    poissonizedUniformBlockCountingProcess L X t ω =
      Finset.sum (Finset.range (Nat.floor (t : ℝ) + 1)) fun n ↦
        Finset.sum (Finset.range (L n ω)) fun k ↦
          if (X n k ω : ℝ) ≤ (t : ℝ) then 1 else 0 := by
  sorry

end

-- Proof sketch: for each `n`, apply the unit-interval result to the counting process built from
-- the Poisson number `L n` of i.i.d. marks in `(n, n + 1]`, after translating that block to
-- `(0,1]`. The processes coming from different blocks are independent and their time-shifted
-- superposition has Poisson increments with parameter `α (t - s)`, hence defines a Poisson
-- process of intensity `α`.
/-- Exercise 5.5.1: if `L₁, L₂, …` are independent Poisson random variables with parameter `α`,
the families `X₁¹, X₂¹, …`, `X₁², X₂², …`, … are independent and each `X_k^(n+1)` is uniformly
distributed on `(n, n + 1]`, then the counting process is a Poisson process with intensity `α`.
In the faithful Lean version, exact block membership is encoded by taking
`X n k : Ω → Set.Ioc (n : ℝ) (n + 1)`, while the uniform law is stated for the coerced real-valued
random variables `ω ↦ (X n k ω : ℝ)`. This is the canonical 0-based reindexing of the textbook
statement, where `L n` encodes `L_(n+1)` and `X n k` encodes `X_(k+1)^(n+1)`. -/
theorem poissonizedUniformBlockCountingProcess_isPoissonProcess
    (P : Measure Ω) (α : NNReal) (L : ℕ → Ω → ℕ)
    (X : ∀ n : ℕ, ℕ → Ω → Set.Ioc (n : ℝ) (n + 1))
    (hL_indep : iIndepFun L P)
    (hLX_indep :
      IndepFun (fun ω ↦ fun n : ℕ ↦ L n ω)
        (fun ω ↦ fun p : ℕ × ℕ ↦ (X p.1 p.2 ω : ℝ)) P)
    (hX_indep : iIndepFun (fun p : ℕ × ℕ ↦ fun ω ↦ (X p.1 p.2 ω : ℝ)) P)
    (hL_law : ∀ n, HasLaw (L n) (poissonMeasure α) P)
    (hX_law : ∀ n k,
      HasLaw (fun ω ↦ (X n k ω : ℝ))
        (volume.restrict (Set.Ioc (n : ℝ) (n + 1))) P) :
    IsPoissonProcess α P (poissonizedUniformBlockCountingProcess L X) := by
  letI : IsProbabilityMeasure P := (hL_law 0).isProbabilityMeasure
  sorry
