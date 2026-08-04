import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Definition_3_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Theorem_3_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Example 17.20: the branching process started from `x` and driven by the offspring
array `Y`. -/
def branchingProcess (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) : ℕ → Ω → ℕ
  | 0 => fun _ ↦ x
  | n + 1 => fun ω ↦ Finset.sum (Finset.range (branchingProcess x Y n ω)) (fun i ↦ Y n i ω)

/-- Helper for Example 17.20: the branching process starts from the deterministic population `x`.
-/
theorem branchingProcess_zero (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) :
    branchingProcess x Y 0 = fun _ ↦ x := rfl

/-- Helper for Example 17.20: a finite history tuple is measurable once each process coordinate is
measurable. -/
private lemma measurable_historyTuple {E : Type*} [MeasurableSpace E] {n : ℕ}
    (X : ℕ → Ω → E) (times : Fin (n + 1) → ℕ) (hX : ∀ t, Measurable (X t)) :
    Measurable (fun ω k ↦ X (times k) ω) := by
  -- Proof comment: a function into a finite product is measurable exactly when each coordinate is.
  refine measurable_pi_lambda _ fun k ↦ ?_
  exact hX (times k)

/-- Helper for Example 17.20: the finite history tuple is measurable with respect to the
generated filtration at its terminal time. -/
private lemma historyTuple_comap_le_generatedFiltrationSpace {E : Type*}
    [MeasurableSpace E] {n : ℕ} (X : ℕ → Ω → E) (times : Fin (n + 1) → ℕ)
    (htimes : StrictMono times) :
    MeasurableSpace.comap (fun ω k ↦ X (times k) ω)
      (inferInstance : MeasurableSpace (Fin (n + 1) → E)) ≤
      generatedFiltrationSpace X (times (Fin.last n)) := by
  let _ : MeasurableSpace Ω := generatedFiltrationSpace X (times (Fin.last n))
  have hmeas :
      Measurable[generatedFiltrationSpace X (times (Fin.last n))]
        (fun ω k ↦ X (times k) ω) := by
    -- Proof comment: every observed time `times k` lies below the terminal time `times (last n)`.
    refine measurable_pi_iff.2 fun k ↦ ?_
    refine measurable_iff_comap_le.mpr ?_
    exact le_iSup_of_le (times k) <| le_iSup_of_le
      (htimes.monotone (Fin.le_last k)) le_rfl
  simpa using hmeas.comap_le

/- Example 17.20 is `source-facing`: for an arbitrary initial population `x`, the branching
process `branchingProcess x Y` driven by an i.i.d. offspring array has one-step law
`p(x,y) = q_y^{*x}`. The primitive data is the recursive offspring-convolution family `q^{*x}`.
Its `core/canonical` one-step owner is the stochastic matrix
`branchingTransitionMatrix q : ℕ → ℕ → ℝ≥0∞` together with the associated discrete kernel
`branchingTransitionKernel q = discreteMatrixKernel (branchingTransitionMatrix q)`. The
real-valued singleton formula is only a `bridge/view` companion. At the process level, the
ambient Chapter 17 owner is `HasNaturalMarkovProperty μ Z`, while the one-ancestor Chapter 3
owner `IsGaltonWatsonProcess Z μ q` is a `bridge/view` specialization obtained by taking `x = 1`
and recovering the offspring array with `IsGaltonWatsonProcess.exists_offspring`. -/

/-- The `x`-fold offspring law obtained by convolving the one-particle offspring distribution `q`
`x` times. This is the distribution denoted `q^{*x}` in the textbook. -/
def branchingOffspringPMF (q : PMF ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | n + 1 =>
      (branchingOffspringPMF q n).bind fun k ↦
        q.map (fun l : ℕ ↦ k + l)

scoped notation:arg q "^{*" x "}" => branchingOffspringPMF q x

-- Proof sketch: unfold the recursive definition of `branchingOffspringPMF` at `0`.
/-- The zeroth offspring convolution is the Dirac mass at `0`. -/
theorem branchingOffspringPMF_zero (q : PMF ℕ) :
    branchingOffspringPMF q 0 = PMF.pure 0 := by
  -- Unfold the recursive definition at the initial generation.
  rfl

-- Proof sketch: unfold the recursive definition at `n + 1`; the next convolution adds one more
-- offspring variable with law `q`.
/-- The successor step of the offspring-convolution recursion. -/
theorem branchingOffspringPMF_succ (q : PMF ℕ) (n : ℕ) :
    branchingOffspringPMF q (n + 1) =
      (branchingOffspringPMF q n).bind fun k ↦
        q.map (fun l : ℕ ↦ k + l) := by
  -- Unfold the recursive definition at the successor generation.
  rfl

/-- The branching-process transition matrix `p(x,y) = q^{*x}_y` attached to the offspring
distribution `q`. This is the textbook matrix view of the recursive offspring law. -/
def branchingTransitionMatrix (q : PMF ℕ) : ℕ → ℕ → ℝ≥0∞ :=
  fun x y ↦ branchingOffspringPMF q x y

-- Proof sketch: each row of `branchingTransitionMatrix q` is the PMF `q^{*x}`, so its total mass
-- is `1`.
/-- The branching-process transition matrix is stochastic. -/
theorem branchingTransitionMatrix_isStochasticMatrix (q : PMF ℕ) :
    IsStochasticMatrix (branchingTransitionMatrix q) := by
  intro x
  -- Each row is exactly the PMF `q^{*x}`, so its total mass is `1`.
  simp [branchingTransitionMatrix]

/-- The one-step transition kernel of the branching process associated with the offspring law `q`,
expressed through the canonical discrete-matrix kernel owner. -/
def branchingTransitionKernel (q : PMF ℕ) : Kernel ℕ ℕ :=
  discreteMatrixKernel (branchingTransitionMatrix q)

-- Proof sketch: `branchingTransitionMatrix q` was defined from the row PMFs `q^{*x}`.
/-- Evaluating the branching transition matrix at `(x,y)` gives the `y`-mass of the `x`-fold
offspring convolution. -/
theorem branchingTransitionMatrix_apply (q : PMF ℕ) (x y : ℕ) :
    branchingTransitionMatrix q x y = (q^{*x}) y := rfl

-- Proof sketch: unfold `branchingTransitionKernel`; `discreteMatrixKernel` stores exactly the row
-- measures determined by the point masses `q^{*x}_y`, which is the PMF measure
-- `(branchingOffspringPMF q x).toMeasure`.
/-- Evaluating the branching transition kernel at `x` gives the measure associated with the
`x`-fold offspring PMF. -/
theorem branchingTransitionKernel_apply (q : PMF ℕ) (x : ℕ) :
    branchingTransitionKernel q x = (q^{*x}).toMeasure := by
  -- Compare the two measures on an arbitrary measurable set in the discrete state space `ℕ`.
  ext s hs
  rw [branchingTransitionKernel, discreteMatrixKernel_apply, Measure.sum_apply _ hs,
    PMF.toMeasure_apply _ hs]
  -- The row of the discrete kernel is the indicator expansion of the PMF measure.
  refine tsum_congr fun y ↦ ?_
  by_cases hy : y ∈ s
  · simp [Measure.smul_apply, smul_eq_mul, branchingTransitionMatrix_apply, hy]
  · simp [Measure.smul_apply, smul_eq_mul, branchingTransitionMatrix_apply, hy]

/-- Helper for Example 17.20: the discrete kernel associated with the branching transition matrix
evaluates singleton masses by the corresponding matrix entries. -/
private theorem branchingTransitionKernel_apply_singletonMass (q : PMF ℕ) (x y : ℕ) :
    branchingTransitionKernel q x ({y} : Set ℕ) = branchingTransitionMatrix q x y := by
  rw [branchingTransitionKernel_apply, PMF.toMeasure_apply_singleton _ _
    (measurableSet_singleton y), branchingTransitionMatrix_apply]

-- Proof sketch: evaluate `branchingTransitionKernel q x` via `branchingTransitionKernel_apply`
-- and then compute the singleton mass of the PMF `q^{*x}`.
/-- The singleton mass of the branching transition kernel is the corresponding stochastic-matrix
entry. -/
theorem branchingTransitionKernel_apply_singleton (q : PMF ℕ) (x y : ℕ) :
    branchingTransitionKernel q x {y} = branchingTransitionMatrix q x y := by
  -- Reduce the singleton mass to the PMF value of `q^{*x}`.
  exact branchingTransitionKernel_apply_singletonMass q x y

/-- Helper for Example 17.20: a random finite sum of relatively measurable offspring counts is
again relatively measurable. -/
private lemma measurable_randomNatSum
    {mΩ : MeasurableSpace Ω} (T : Ω → ℕ) (hT : Measurable[mΩ] T) (X : ℕ → Ω → ℕ)
    (hX : ∀ n, Measurable[mΩ] (X n)) :
    Measurable[mΩ] (fun ω ↦ Finset.sum (Finset.range (T ω)) (fun i ↦ X i ω)) := by
  -- Proof comment: this is exactly the Chapter 3 measurability theorem for `natRandomSum`.
  simpa [natRandomSum] using measurable_natRandomSum T hT X hX

/-- Helper for Example 17.20: the current offspring row restricted to its first `m` entries. -/
private def offspringRowPrefix (Y : ℕ → ℕ → Ω → ℕ) (n m : ℕ) :
    Ω → Fin m → ℕ :=
  fun ω i ↦ Y n i ω

/-- Helper for Example 17.20: the sum of the first `m` offspring counts in row `n`. -/
private def offspringRowSum (Y : ℕ → ℕ → Ω → ℕ) (n m : ℕ) : Ω → ℕ :=
  fun ω ↦ ∑ i : Fin m, offspringRowPrefix Y n m ω i

/-- Helper for Example 17.20: the singleton mass of a convolution on `ℕ` is the finite
antidiagonal sum of the singleton masses of its two factors. -/
private lemma convolutionApplySingletonEqSumAntidiagonal
    {μ ν : Measure ℕ} [SFinite μ] [SFinite ν] (n : ℕ) :
    (μ ∗ ν) ({n} : Set ℕ) =
      ∑ p ∈ Finset.antidiagonal n, μ ({p.1} : Set ℕ) * ν ({p.2} : Set ℕ) := by
  -- Proof comment: rewrite convolution as the pushforward of the product law along addition.
  rw [Measure.conv, Measure.map_apply measurable_add (measurableSet_singleton n)]
  have hpreimage :
      (fun z : ℕ × ℕ ↦ z.1 + z.2) ⁻¹' ({n} : Set ℕ) = ↑(Finset.antidiagonal n) := by
    ext z
    simp [Finset.mem_antidiagonal]
  rw [hpreimage, ← MeasureTheory.sum_measure_singleton (μ := μ.prod ν)
    (s := Finset.antidiagonal n)]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hsingleton :
      ({p} : Set (ℕ × ℕ)) = ({p.1} : Set ℕ) ×ˢ ({p.2} : Set ℕ) := by
    ext z
    rcases z with ⟨a, b⟩
    cases p
    simp
  rw [hsingleton]
  exact Measure.prod_prod (μ := μ) (ν := ν) ({p.1} : Set ℕ) ({p.2} : Set ℕ)

/-- Helper for Example 17.20: convolving the `n`-fold offspring law with one more copy of `q`
matches the recursive PMF successor. -/
private lemma branchingOffspringPMF_toMeasure_succ (q : PMF ℕ) (n : ℕ) :
    ((q^{*n}).toMeasure ∗ q.toMeasure) = (q^{*(n + 1)}).toMeasure := by
  refine Measure.ext_of_singleton fun k ↦ ?_
  -- Proof comment: on the discrete state space `ℕ`, it is enough to compare singleton masses.
  rw [convolutionApplySingletonEqSumAntidiagonal]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b ↦ (q^{*n}).toMeasure ({a} : Set ℕ) * q.toMeasure ({b} : Set ℕ)) k]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rw [branchingOffspringPMF_succ, PMF.bind_apply]
  rw [tsum_eq_sum (s := Finset.range (k + 1))]
  · refine Finset.sum_congr rfl ?_
    intro a ha
    have hak : a ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    congr 1
    rw [← PMF.toMeasure_apply_singleton
      (q.map (fun l : ℕ ↦ a + l)) k (measurableSet_singleton k)]
    rw [PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete (measurableSet_singleton k)]
    have hpre : (fun l : ℕ ↦ a + l) ⁻¹' ({k} : Set ℕ) = {k - a} := by
      ext l
      simp
      omega
    rw [hpre, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (k - a))]
  · intro a ha
    have hka : k < a := by
      have hnot : ¬ a < k + 1 := by
        simpa using ha
      omega
    have hzero : (q.map (fun l : ℕ ↦ a + l)) k = 0 := by
      rw [← PMF.toMeasure_apply_singleton
        (q.map (fun l : ℕ ↦ a + l)) k (measurableSet_singleton k)]
      rw [PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete (measurableSet_singleton k)]
      have hpre : (fun l : ℕ ↦ a + l) ⁻¹' ({k} : Set ℕ) = ∅ := by
        ext l
        simp
        intro h
        exact (Nat.not_le_of_gt hka) <| h ▸ Nat.le_add_right a l
      simp [hpre]
    simp [hzero]

/-- Helper for Example 17.20: the finite offspring-row sum has the recursive convolution law

end ProbabilityTheory
