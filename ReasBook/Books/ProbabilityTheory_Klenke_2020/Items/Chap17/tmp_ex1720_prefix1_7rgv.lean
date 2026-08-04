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
`q^{*m}`. -/
private lemma offspringRowSum_hasLaw
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    (n m : ℕ) :
    HasLaw (fun ω ↦ Finset.sum (Finset.range m) (fun i ↦ Y n i ω))
      (branchingOffspringPMF q m).toMeasure (P : Measure Ω) := by
  induction m with
  | zero =>
      -- Proof comment: the empty offspring sum is the constant zero random variable.
      refine HasLaw.mk aemeasurable_const ?_
      ext s hs
      simp [branchingOffspringPMF_zero, PMF.toMeasure_pure]
  | succ m ih =>
      let rowSum : Ω → ℕ := fun ω ↦ Finset.sum (Finset.range m) (fun j ↦ Y n j ω)
      have hrowSum_eq : (∑ j ∈ Finset.range m, Y n j) = rowSum := by
        funext ω
        simp [rowSum]
      have hrow_indep : iIndepFun (fun i : ℕ ↦ Y n i) (P : Measure Ω) :=
        hY_indep.precomp (g := fun i : ℕ ↦ (n, i)) <| by
          intro i j hij
          simpa using congrArg Prod.snd hij
      have hsum_indep_base :
          IndepFun (∑ j ∈ Finset.range m, Y n j) (Y n m) (P : Measure Ω) := by
        exact
          (hrow_indep.indepFun_sum_range_succ₀
            (fun i ↦ (hY_law n i).aemeasurable) m)
      have hsum_indep :
          IndepFun rowSum (Y n m) (P : Measure Ω) :=
        hsum_indep_base.congr (Filter.EventuallyEq.of_eq hrowSum_eq) Filter.EventuallyEq.rfl
      have ihRow :
          HasLaw rowSum (branchingOffspringPMF q m).toMeasure (P : Measure Ω) := by
        simpa [rowSum] using ih
      have hstep :
          HasLaw (fun ω ↦ rowSum ω + Y n m ω)
            (((branchingOffspringPMF q m).toMeasure) ∗ q.toMeasure) (P : Measure Ω) :=
        hsum_indep.hasLaw_add ihRow (hY_law n m)
      -- Proof comment: append one more independent offspring variable and normalize the
      -- resulting convolution with the recursive PMF law.
      simpa [rowSum, Finset.sum_range_succ, branchingOffspringPMF_toMeasure_succ] using hstep

/-- Helper for Example 17.20: the finite history tuple of `branchingProcess x Y` up to time `n`.
-/
private def branchingHistoryTuple (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) (n : ℕ) :
    Ω → Fin (n + 1) → ℕ :=
  fun ω i ↦ branchingProcess x Y i ω

/-- Helper for Example 17.20: each finite branching history tuple is measurable. -/
private lemma measurable_branchingHistoryTuple
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) (n : ℕ) :
    Measurable (branchingHistoryTuple x Y n) := by
  let times : Fin (n + 1) → ℕ := fun i ↦ i
  have hX : ∀ t : ℕ, Measurable (branchingProcess x Y t) := by
    intro t
    exact (Measurable.of_discrete : Measurable (branchingProcess x Y t))
  -- Proof comment: the history tuple is a finite product of measurable `ℕ`-valued coordinates.
  simpa [branchingHistoryTuple, times] using
    (measurable_historyTuple (X := branchingProcess x Y) (times := times) hX)

/-- Helper for Example 17.20: the branching transition kernel is Markov because its rows are the
PMF measures `q^{*x}`. -/
private theorem branchingTransitionKernel_isMarkov (q : PMF ℕ) :
    IsMarkovKernel (branchingTransitionKernel q) :=
  discreteMatrixKernel_isMarkovKernel (branchingTransitionMatrix q)
    (branchingTransitionMatrix_isStochasticMatrix q)

/-- Helper for Example 17.20: the sigma-algebra generated by offspring rows strictly before
generation `n`. -/
private abbrev offspringPast
    (Y : ℕ → ℕ → Ω → ℕ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ ij ∈ {ij : ℕ × ℕ | ij.1 < n},
    MeasurableSpace.comap (fun ω ↦ Y ij.1 ij.2 ω) inferInstance

/-- Helper for Example 17.20: enlarging the cutoff generation enlarges the past-offspring
sigma-algebra. -/
private lemma offspringPast_mono {Y : ℕ → ℕ → Ω → ℕ} :
    Monotone (offspringPast (Ω := Ω) Y) := by
  intro n k hnk
  refine iSup_le ?_
  intro ij
  refine iSup_le ?_
  intro hij
  exact le_iSup_of_le ij <| le_iSup_of_le (lt_of_lt_of_le hij hnk) le_rfl

/-- Helper for Example 17.20: the first `m` offspring coordinates of row `n` generate their own
finite prefix sigma-algebra. -/
private abbrev currentOffspringPrefixSpace
    (Y : ℕ → ℕ → Ω → ℕ) (n m : ℕ) : MeasurableSpace Ω :=
  ⨆ ij ∈ {ij : ℕ × ℕ | ij.1 = n ∧ ij.2 < m},
    MeasurableSpace.comap (fun ω ↦ Y ij.1 ij.2 ω) inferInstance

/-- Helper for Example 17.20: every generation size is measurable with respect to the offspring
rows revealed up to that generation. -/
private lemma branchingProcess_measurable_offspringPast_self
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) :
    ∀ n, Measurable[offspringPast (Ω := Ω) Y n] (branchingProcess x Y n) := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the initial population is the deterministic constant `x`.
      simp [branchingProcess_zero]
  | succ n ih =>
      have hT :
          Measurable[offspringPast (Ω := Ω) Y (n + 1)] (branchingProcess x Y n) :=
        Measurable.mono ih
          (offspringPast_mono (Ω := Ω) (Y := Y) (show n ≤ n + 1 by omega)) le_rfl
      have hX :
          ∀ i, Measurable[offspringPast (Ω := Ω) Y (n + 1)] (Y n i) := by
        intro i
        refine measurable_iff_comap_le.mpr ?_
        exact le_iSup_of_le (n, i) <| le_iSup_of_le (by simp) le_rfl
      -- Proof comment: the next generation is a measurable random sum over the fresh row.
      simpa [branchingProcess] using
        (measurable_randomNatSum
          (mΩ := offspringPast (Ω := Ω) Y (n + 1))
          (T := branchingProcess x Y n) hT (X := fun i ↦ Y n i) hX)

/-- Helper for Example 17.20: any earlier generation is measurable with respect to any later
past-offspring sigma-algebra. -/
private lemma branchingProcess_measurable_offspringPast
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) :
    ∀ {k n}, k ≤ n → Measurable[offspringPast (Ω := Ω) Y n] (branchingProcess x Y k) := by
  intro k n hkn
  -- Proof comment: monotonicity of `offspringPast` lets us weaken the relative measurability
  -- statement from generation `k` to any later cutoff `n`.
  exact Measurable.mono
    (branchingProcess_measurable_offspringPast_self (x := x) (Y := Y) k)
    (offspringPast_mono (Ω := Ω) (Y := Y) hkn) le_rfl

/-- Helper for Example 17.20: the history tuple up to time `n` is measurable with respect to the
offspring rows revealed before generation `n`. -/
private lemma branchingHistoryTuple_comap_le_offspringPast
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) (n : ℕ) :
    MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance ≤
      offspringPast (Ω := Ω) Y n := by
  let _ : MeasurableSpace Ω := offspringPast (Ω := Ω) Y n
  have hmeas :
      Measurable[offspringPast (Ω := Ω) Y n] (branchingHistoryTuple x Y n) := by
    -- Proof comment: each coordinate of the history tuple is one earlier branching generation.
    refine measurable_pi_iff.2 fun i ↦ ?_
    refine measurable_iff_comap_le.mpr ?_
    simpa [branchingHistoryTuple] using
      (branchingProcess_measurable_offspringPast (x := x) (Y := Y)
        (k := (i : ℕ)) (n := n) (show (i : ℕ) ≤ n by exact Nat.le_of_lt_succ i.2)).comap_le
  simpa using hmeas.comap_le

/-- Helper for Example 17.20: the finite current-row tuple is measurable with respect to the
sigma-algebra generated by its coordinates. -/
private lemma offspringRowPrefix_comap_le_currentOffspringPrefixSpace
    (Y : ℕ → ℕ → Ω → ℕ) (n m : ℕ) :
    MeasurableSpace.comap (offspringRowPrefix Y n m) inferInstance ≤
      currentOffspringPrefixSpace (Ω := Ω) Y n m := by
  let _ : MeasurableSpace Ω := currentOffspringPrefixSpace (Ω := Ω) Y n m
  have hmeas :
      Measurable[currentOffspringPrefixSpace (Ω := Ω) Y n m] (offspringRowPrefix Y n m) := by
    -- Proof comment: each coordinate of the prefix tuple is one of the generators of the current
    -- row prefix sigma-algebra.
    refine measurable_pi_iff.2 fun i ↦ ?_
    refine measurable_iff_comap_le.mpr ?_
    exact le_iSup_of_le (n, i) <| le_iSup_of_le (by simp [i.2]) le_rfl
  simpa using hmeas.comap_le

/-- Helper for Example 17.20: the fresh row prefix is independent of all earlier offspring rows.
-/
private lemma currentOffspringPrefixSpace_indep_offspringPast
    (P : ProbabilityMeasure Ω) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (n m : ℕ) :
    Indep (currentOffspringPrefixSpace (Ω := Ω) Y n m)
      (offspringPast (Ω := Ω) Y n) (P : Measure Ω) := by
  let mY : ℕ × ℕ → MeasurableSpace Ω := fun ij ↦
    MeasurableSpace.comap (fun ω ↦ Y ij.1 ij.2 ω) inferInstance
  have hDisjoint :
      Disjoint {ij : ℕ × ℕ | ij.1 = n ∧ ij.2 < m} {ij : ℕ × ℕ | ij.1 < n} := by
    refine Set.disjoint_left.2 ?_
    intro ij hij hpast
    exact lt_irrefl n (hij.1 ▸ hpast)
  -- Proof comment: the fresh row coordinates and the older rows are indexed by disjoint blocks
  -- of the i.i.d. offspring array.
  simpa [mY, currentOffspringPrefixSpace, offspringPast] using
      (ProbabilityTheory.indep_iSup_of_disjoint
      (m := mY)
      (h_le := fun ij ↦ (Measurable.of_discrete : Measurable (fun ω ↦ Y ij.1 ij.2 ω)).comap_le)
      (h_indep := hY_indep.iIndep)
      hDisjoint)

/-- Helper for Example 17.20: the current row sum over `m` parents is independent of the whole
branching history up to time `n`. -/
private lemma branchingHistoryTuple_indep_offspringRowSum
    (P : ProbabilityMeasure Ω) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (n m : ℕ) :
    IndepFun (branchingHistoryTuple x Y n)
      (offspringRowSum Y n m)
      (P : Measure Ω) := by
  have hsum_meas :
      Measurable[MeasurableSpace.comap (offspringRowPrefix Y n m) inferInstance]
        (offspringRowSum Y n m) := by
    -- Proof comment: the row sum is a measurable function of the finite current-row tuple.
    exact
      (Measurable.of_discrete : Measurable (fun f : Fin m → ℕ ↦ ∑ i : Fin m, f i)).comp
      (comap_measurable (offspringRowPrefix Y n m))
  have hrow_indep :
      Indep (MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance)
        (MeasurableSpace.comap (offspringRowSum Y n m) inferInstance)
        (P : Measure Ω) := by
    have hbase :
        Indep (currentOffspringPrefixSpace (Ω := Ω) Y n m)
          (offspringPast (Ω := Ω) Y n) (P : Measure Ω) :=
      currentOffspringPrefixSpace_indep_offspringPast
        (Ω := Ω) P Y hY_indep n m
    have hhistory :
        MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance ≤
          offspringPast (Ω := Ω) Y n :=
      branchingHistoryTuple_comap_le_offspringPast (Ω := Ω) x Y n
    have hsum :
        MeasurableSpace.comap (offspringRowSum Y n m) inferInstance ≤
          currentOffspringPrefixSpace (Ω := Ω) Y n m := by
      exact hsum_meas.comap_le.trans
        (offspringRowPrefix_comap_le_currentOffspringPrefixSpace (Ω := Ω) Y n m)
    exact ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hbase.symm hhistory) hsum
  exact (IndepFun_iff_Indep _ _ _).2 hrow_indep

/-- Helper for Example 17.20: on a history fiber with terminal population `h (Fin.last n)`, the
next branching state is the sum of that many fresh offspring variables from row `n`. -/
private lemma branchingProcess_succ_eq_offspringRowSum_of_history
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) {n : ℕ} {h : Fin (n + 1) → ℕ} {ω : Ω}
    (hω : branchingHistoryTuple x Y n ω = h) :
    branchingProcess x Y (n + 1) ω = offspringRowSum Y n (h (Fin.last n)) ω := by
  have hlast : branchingProcess x Y n ω = h (Fin.last n) := by
    -- Proof comment: the last coordinate of the history tuple records the current population.
    simpa [branchingHistoryTuple] using
      congrArg (fun g : Fin (n + 1) → ℕ ↦ g (Fin.last n)) hω
  -- Proof comment: unfold the branching recursion and rewrite the terminal population with the
  -- value fixed by the history fiber.
  calc
    branchingProcess x Y (n + 1) ω
        = ∑ i ∈ Finset.range (branchingProcess x Y n ω), Y n i ω := by
            rfl
    _ = ∑ i ∈ Finset.range (h (Fin.last n)), Y n i ω := by rw [hlast]
    _ = offspringRowSum Y n (h (Fin.last n)) ω := by
      simpa [offspringRowSum, offspringRowPrefix] using
        (Fin.sum_univ_eq_sum_range (f := fun i ↦ Y n i ω)).symm

/-- Helper for Example 17.20: the finite history tuple generates exactly the time-`n`
sigma-algebra of the branching process. -/
private lemma generatedFiltrationSpace_branchingProcess_eq_historyTupleComap
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) (n : ℕ) :
    generatedFiltrationSpace (branchingProcess x Y) n =
      MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance := by
  let times : Fin (n + 1) → ℕ := fun i ↦ i
  have htimes : StrictMono times := fun i j hij ↦ hij
  have hleft :
      MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance ≤
        generatedFiltrationSpace (branchingProcess x Y) n := by
    -- Proof comment: the full history tuple is measurable for the natural filtration because
    -- each recorded time lies at most at `n`.
    simpa [branchingHistoryTuple, times] using
      (historyTuple_comap_le_generatedFiltrationSpace
        (X := branchingProcess x Y) (times := times) htimes)
  have hright :
      generatedFiltrationSpace (branchingProcess x Y) n ≤
        MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance := by
    -- Proof comment: each generator `branchingProcess x Y t` with `t ≤ n` is recovered by
    -- evaluating the history tuple at the coordinate `⟨t, t < n + 1⟩`.
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Fin (n + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
    have hCoord :
        Measurable[MeasurableSpace.comap (branchingHistoryTuple x Y n) inferInstance]
          (fun ω ↦ branchingHistoryTuple x Y n ω i) := by
      exact (measurable_pi_apply i).comp (comap_measurable (branchingHistoryTuple x Y n))
    simpa [branchingHistoryTuple, i] using hCoord.comap_le
  exact le_antisymm hright hleft

/-- Helper for Example 17.20: on a fixed history singleton, the next-state rectangle event agrees
with the corresponding fresh-row-sum rectangle event. -/
private lemma branchingHistoryTuple_nextPairPreimage_eq_rowSumPairPreimage
    (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ) {n : ℕ} (h : Fin (n + 1) → ℕ) (y : ℕ) :
    (fun ω ↦ (branchingHistoryTuple x Y n ω, branchingProcess x Y (n + 1) ω)) ⁻¹'
        ({h} ×ˢ ({y} : Set ℕ)) =
      (fun ω ↦
        (branchingHistoryTuple x Y n ω,
          offspringRowSum Y n (h (Fin.last n)) ω)) ⁻¹'
        ({h} ×ˢ ({y} : Set ℕ)) := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hHω, hnextω⟩
    have hrow :
        branchingProcess x Y (n + 1) ω = offspringRowSum Y n (h (Fin.last n)) ω := by
      -- Proof comment: on the history fiber `branchingHistoryTuple x Y n = h`, the recursive
      -- next state is exactly the row sum indexed by the terminal population `h (Fin.last n)`.
      simpa using
        (branchingProcess_succ_eq_offspringRowSum_of_history
          (x := x) (Y := Y) (n := n) (h := h) (ω := ω) hHω)
    exact ⟨hHω, hrow ▸ hnextω⟩
  · rintro ⟨hHω, hrowω⟩
    have hrow :
        branchingProcess x Y (n + 1) ω = offspringRowSum Y n (h (Fin.last n)) ω := by
      -- Proof comment: the same history-fiber identification converts the row-sum event back to
      -- the actual next-generation event.
      simpa using
        (branchingProcess_succ_eq_offspringRowSum_of_history
          (x := x) (Y := Y) (n := n) (h := h) (ω := ω) hHω)
    exact ⟨hHω, hrow.symm ▸ hrowω⟩

/-- Helper for Example 17.20: the joint law of the history tuple and the fresh row sum factors on
singleton rectangles into the history mass times the offspring transition row. -/
private lemma branchingHistoryTuple_rowSumPairMap_singleton
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    (n : ℕ) (h : Fin (n + 1) → ℕ) (y : ℕ) :
    (P : Measure Ω).map
        (fun ω ↦
          (branchingHistoryTuple x Y n ω,
            ∑ i : Fin (h (Fin.last n)), offspringRowPrefix Y n (h (Fin.last n)) ω i))
        ({h} ×ˢ ({y} : Set ℕ)) =
      (P : Measure Ω).map (branchingHistoryTuple x Y n) {h} *
        branchingTransitionKernel q (h (Fin.last n)) ({y} : Set ℕ) := by
  let μ : Measure Ω := (P : Measure Ω)
  let H : Ω → Fin (n + 1) → ℕ := branchingHistoryTuple x Y n
  let m : ℕ := h (Fin.last n)
  let U : Ω → ℕ := offspringRowSum Y n m
  have hH_meas : Measurable H := by simpa [H] using measurable_branchingHistoryTuple x Y n
  have hU_meas : Measurable U := by
    exact (Measurable.of_discrete : Measurable U)
  have hU_eq :
      U = fun ω ↦ Finset.sum (Finset.range m) (fun i ↦ Y n i ω) := by
    funext ω
    simpa [U, offspringRowSum, offspringRowPrefix] using
      (Fin.sum_univ_eq_sum_range (f := fun i ↦ Y n i ω)).symm
  have hU_law_range :
      HasLaw (fun ω ↦ Finset.sum (Finset.range m) (fun i ↦ Y n i ω))
        (branchingOffspringPMF q m).toMeasure μ :=
    offspringRowSum_hasLaw (Ω := Ω) P q Y hY_indep hY_law n m
  have hU_law : HasLaw U (branchingOffspringPMF q m).toMeasure μ :=
    hU_law_range.congr (Filter.EventuallyEq.of_eq hU_eq)
  have hHU_indep : IndepFun H U μ :=
    branchingHistoryTuple_indep_offspringRowSum (Ω := Ω) P x Y hY_indep n m
  have hmap_prod :
      μ.map (fun ω ↦ (H ω, U ω)) = (μ.map H).prod (μ.map U) :=
    (indepFun_iff_map_prod_eq_prod_map_map hH_meas.aemeasurable hU_meas.aemeasurable).mp hHU_indep
  -- Proof comment: independence factors the joint law into the product of the history law and the
  -- fresh-row-sum law, and that row-sum law is the `m`-fold offspring convolution.
  calc
    μ.map (fun ω ↦ (H ω, U ω)) ({h} ×ˢ ({y} : Set ℕ))
        = ((μ.map H).prod (μ.map U)) ({h} ×ˢ ({y} : Set ℕ)) := by
            rw [hmap_prod]
    _ = μ.map H {h} * μ.map U ({y} : Set ℕ) := by
          rw [Measure.prod_prod]
    _ = μ.map H {h} * branchingTransitionKernel q m ({y} : Set ℕ) := by
          rw [hU_law.map_eq, ← branchingTransitionKernel_apply q m]

/-- Helper for Example 17.20: conditioning the next branching state on a non-null history fiber
returns the transition kernel row determined by the last observed population. -/
private lemma branchingHistoryTuple_nextPairMap_eq_compProd
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    (n : ℕ) :
    let μ : Measure Ω := (P : Measure Ω)
    let H : Ω → Fin (n + 1) → ℕ := branchingHistoryTuple x Y n
    let next : Ω → ℕ := branchingProcess x Y (n + 1)
    let κ : Kernel (Fin (n + 1) → ℕ) ℕ :=
      Kernel.comap (branchingTransitionKernel q) (fun h : Fin (n + 1) → ℕ ↦ h (Fin.last n))
        (by fun_prop)
    μ.map (fun ω ↦ (H ω, next ω)) = μ.map H ⊗ₘ κ := by
  let μ : Measure Ω := (P : Measure Ω)
  let H : Ω → Fin (n + 1) → ℕ := branchingHistoryTuple x Y n
  let next : Ω → ℕ := branchingProcess x Y (n + 1)
  let κ : Kernel (Fin (n + 1) → ℕ) ℕ :=
    Kernel.comap (branchingTransitionKernel q) (fun h : Fin (n + 1) → ℕ ↦ h (Fin.last n))
      (by fun_prop)
  have hH_meas : Measurable H := by simpa [H] using measurable_branchingHistoryTuple x Y n
  have hnext_meas : Measurable next := by
    exact (Measurable.of_discrete : Measurable next)
  have hκ_apply :
      ∀ h : Fin (n + 1) → ℕ, κ h = branchingTransitionKernel q (h (Fin.last n)) := by
    intro h
    simp [κ]
  let _ : IsMarkovKernel (branchingTransitionKernel q) := branchingTransitionKernel_isMarkov q
  let _ : IsFiniteKernel κ := by infer_instance
  refine Measure.ext_of_singleton fun z ↦ ?_
  rcases z with ⟨h, y⟩
  let row : Ω → ℕ := offspringRowSum Y n (h (Fin.last n))
  have hsingleton :
      ({(h, y)} : Set ((Fin (n + 1) → ℕ) × ℕ)) = {h} ×ˢ ({y} : Set ℕ) := by
    ext z
    rcases z with ⟨h', y'⟩
    simp
  have hpairNext_meas : Measurable (fun ω ↦ (H ω, next ω)) := hH_meas.prodMk hnext_meas
  have hpairRow_meas :
      Measurable
        (fun ω ↦ (H ω, row ω)) := by
    exact hH_meas.prodMk (Measurable.of_discrete : Measurable row)
  -- Proof comment: compare the joint law on singleton rectangles and then recognize the
  -- resulting factorization as the defining `compProd` law for the conditional kernel.
  calc
    μ.map (fun ω ↦ (H ω, next ω)) ({(h, y)} : Set ((Fin (n + 1) → ℕ) × ℕ))
        =
          μ.map
            (fun ω ↦ (H ω, row ω))
            ({(h, y)} : Set ((Fin (n + 1) → ℕ) × ℕ)) := by
            rw [Measure.map_apply hpairNext_meas (measurableSet_singleton (h, y))]
            rw [Measure.map_apply hpairRow_meas (measurableSet_singleton (h, y))]
            simpa [hsingleton] using
              (branchingHistoryTuple_nextPairPreimage_eq_rowSumPairPreimage
                (x := x) (Y := Y) (h := h) (y := y))
    _ = μ.map H {h} * branchingTransitionKernel q (h (Fin.last n)) ({y} : Set ℕ) := by
          rw [hsingleton]
          exact branchingHistoryTuple_rowSumPairMap_singleton
            (Ω := Ω) (P := P) (q := q) (x := x) (Y := Y) hY_indep hY_law n h y
    _ = (μ.map H ⊗ₘ κ) ({(h, y)} : Set ((Fin (n + 1) → ℕ) × ℕ)) := by
          rw [hsingleton, Measure.compProd_apply_prod (measurableSet_singleton h)
            (measurableSet_singleton y)]
          simp [hκ_apply h]

/-- Helper for Example 17.20: conditioning the next branching state on a non-null history fiber
returns the transition kernel row determined by the last observed population. -/
private lemma branchingProcess_condDistrib_historyTuple_eq_transitionKernel
    (P : ProbabilityMeasure Ω) (q : PMF ℕ) (x : ℕ) (Y : ℕ → ℕ → Ω → ℕ)
    (hY_indep : iIndepFun (fun ni : ℕ × ℕ ↦ Y ni.1 ni.2) (P : Measure Ω))
    (hY_law : ∀ n i, HasLaw (Y n i) q.toMeasure (P : Measure Ω))
    (n : ℕ) :
    condDistrib (branchingProcess x Y (n + 1)) (branchingHistoryTuple x Y n)
        (P : Measure Ω) =ᵐ[(P : Measure Ω).map (branchingHistoryTuple x Y n)]
      fun h ↦ branchingTransitionKernel q (h (Fin.last n)) := by
  let μ : Measure Ω := (P : Measure Ω)
  let H : Ω → Fin (n + 1) → ℕ := branchingHistoryTuple x Y n
  let next : Ω → ℕ := branchingProcess x Y (n + 1)
  let κ : Kernel (Fin (n + 1) → ℕ) ℕ :=
    Kernel.comap (branchingTransitionKernel q) (fun h : Fin (n + 1) → ℕ ↦ h (Fin.last n))
      (by fun_prop)
  have hH_meas : Measurable H := by simpa [H] using measurable_branchingHistoryTuple x Y n
  have hnext_meas : Measurable next := by
    exact (Measurable.of_discrete : Measurable next)
  have hκ_apply :
      ∀ h : Fin (n + 1) → ℕ, κ h = branchingTransitionKernel q (h (Fin.last n)) := by
    intro h
    simp [κ]
  let _ : IsMarkovKernel (branchingTransitionKernel q) := branchingTransitionKernel_isMarkov q
  let _ : IsFiniteKernel κ := by infer_instance
  have hpair :
      μ.map (fun ω ↦ (H ω, next ω)) = μ.map H ⊗ₘ κ := by
    simpa [μ, H, next, κ] using
      (branchingHistoryTuple_nextPairMap_eq_compProd
        (Ω := Ω) (P := P) (q := q) (x := x) (Y := Y) hY_indep hY_law n)
  have hcond : condDistrib next H μ =ᵐ[μ.map H] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd H hnext_meas.aemeasurable hpair
  exact hcond.trans <| Filter.Eventually.of_forall hκ_apply

/-- Example 17.20: the branching process started from an arbitrary population `x` and driven by
an i.i.d. offspring array with common law `q` has one-step conditional law given by the branching
kernel whose matrix entries are `p(x,y) = q^{*x}_y`. -/

end ProbabilityTheory
