import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Corollary_3_22
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap02.Lemma_2_46
import BauschkeLean.Chap02.Lemma_2_51
import BauschkeLean.Chap04.Proposition_4_19
import BauschkeLean.Chap05.Corollary_5_17
import BauschkeLean.Chap06.Example_6_43
import BauschkeLean.Chap20.Example_20_26
import BauschkeLean.Chap22.Remark_22_3
import BauschkeLean.Chap23.Proposition_23_2
import BauschkeLean.Chap23.ResolventRealizer
import BauschkeLean.Chap26.Proposition_26_1
import BauschkeLean.Chap26.Proposition_26_5

open Function
open Filter
open ERealFunction
open EuclideanGeometry
open scoped InnerProductSpace Pointwise Set SetValuedOperator Topology

universe u

namespace SetValuedOperator

/- Source/core/bridge triage:
- `source-facing`: Theorem 26.11 is the relaxed Douglas--Rachford orbit `(26.29)` together with
  its weak/strong convergence consequences.
- `core/canonical`: the reusable owners are `relaxedOperatorIteration`,
  `douglasRachfordOperator`, `reflectedResolventComposition`, `primal_inclusion_solution_set`,
  `dual_inclusion_solution_set`, `N[C]`, and `P[C, hC]`.
- `bridge/view`: `douglasRachfordIteration` is the source-facing name for the Chapter 5 relaxed
  iteration driven by the constant Douglas--Rachford operator, and the primal/dual/auxiliary
  sequences are thin wrappers around that shared orbit.
Semantic recall: `lean_leansearch` only surfaced generic fixed-point iteration lemmas, so this
file follows the verified Chapter 5/20/23/26 owners directly. -/

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The relaxed Douglas--Rachford `y`-orbit from `(26.29)`, realized as the Krasnosel'skii--Mann
iteration of the canonical Douglas--Rachford operator built from `resolventMap A hA γ` and
`resolventMap B hB γ`, with relaxation parameters `lam`. -/
def douglasRachfordIteration
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  relaxedOperatorIteration
    (fun _ ↦ douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ))
    lam y0

/-- The shadow sequence `xₙ = J_{γ B} yₙ` attached to the relaxed Douglas--Rachford orbit. -/
def douglasRachfordPrimalSequence
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  fun n ↦ resolventMap B hB γ (douglasRachfordIteration A B hA hB γ lam y0 n)

/-- The dual sequence `uₙ = {}^[γ] B (yₙ) = γ⁻¹ (yₙ - xₙ)` attached to the relaxed
Douglas--Rachford orbit. -/
def douglasRachfordDualSequence
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  fun n ↦ yosidaApproximationMap B hB γ (douglasRachfordIteration A B hA hB γ lam y0 n)

/-- The auxiliary sequence `zₙ = J_{γ A} (2 xₙ - yₙ)` attached to the relaxed
Douglas--Rachford orbit. -/
def douglasRachfordAuxiliarySequence
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  fun n ↦
    resolventMap A hA γ
      ((2 : ℝ) • douglasRachfordPrimalSequence A B hA hB γ lam y0 n -
        douglasRachfordIteration A B hA hB γ lam y0 n)

/-- Helper for Theorem 26.11: the source divergence hypothesis `∑ λₙ (2 - λₙ) = +∞`
is the `α = 1 / 2` divergence condition required by Proposition 5.16. -/
theorem douglasRachfordAveragedHalfDivergence
    (lam : ℕ → ℝ)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop) :
    Tendsto
      (fun N ↦
        Finset.sum (Finset.range N)
          (fun n ↦ lam n * (1 - ((1 / 2 : ℝ) * lam n))))
      atTop atTop := by
  -- Multiply the source series by `1 / 2` to match the averaged-map normalization.
  convert Tendsto.const_mul_atTop (show 0 < (1 / 2 : ℝ) by norm_num) hdiv using 1
  ext N
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  ring

/-- Helper for Theorem 26.11: the Douglas--Rachford residual `T yₙ - yₙ` is exactly the
auxiliary-minus-primal gap `zₙ - xₙ`. -/
theorem douglasRachfordResidual_eq_auxiliary_sub_primal
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) (n : ℕ) :
    douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ)
        (douglasRachfordIteration A B hA hB γ lam y0 n) -
      douglasRachfordIteration A B hA hB γ lam y0 n =
        douglasRachfordAuxiliarySequence A B hA hB γ lam y0 n -
          douglasRachfordPrimalSequence A B hA hB γ lam y0 n := by
  -- Expand the Douglas--Rachford operator once and cancel the orbit term appearing with both signs.
  simp only [douglasRachfordPrimalSequence, douglasRachfordAuxiliarySequence]
  rw [douglasRachfordOperator_apply]
  abel_nf

/-- Helper for Theorem 26.11: a nonempty primal solution set yields a nonempty Douglas--Rachford
fixed-point set. -/
theorem douglasRachfordFixedPointsNonempty
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (hzero : (primal_inclusion_solution_set A B).Nonempty) :
    (fixedPoints
      (douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ))).Nonempty := by
  -- Read primal solvability through Proposition 26.1's fixed-point image formula.
  rw [primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_reflectedResolventComposition
    A B hA hB γ] at hzero
  rcases hzero with ⟨x, y, hy, rfl⟩
  refine ⟨y, ?_⟩
  -- Transport the reflected-resolvent fixed point back to the Douglas--Rachford operator.
  rw [fixedPoints_douglasRachfordOperator_resolvent_eq_fixedPoints_reflectedResolventComposition
    A B hA hB γ]
  exact hy

section ExistenceAndResidual

variable (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
variable (hzero : (primal_inclusion_solution_set A B).Nonempty)
variable (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
variable
  (hdiv :
    Tendsto
      (fun N ↦
        Finset.sum (Finset.range N)
          (fun n ↦ lam n * (2 - lam n)))
      atTop atTop)
variable (γ : PosReal) (y0 : H)

/-- Theorem 26.11. Under the Douglas--Rachford hypotheses, the relaxed Douglas--Rachford orbit
`yₙ` converges weakly to some `y ∈ fixedPoints (reflectedResolventComposition A B γ)`. -/
theorem douglasRachfordAlgorithm_exists_fixedPoint_tendsto_weakly
    (hzero : (primal_inclusion_solution_set A B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop) :
    ∃ y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ),
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y)) := by
  let T : H → H :=
    douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ)
  have hfix : (fixedPoints T).Nonempty :=
    douglasRachfordFixedPointsNonempty A B hA hB γ hzero
  rcases
      exists_tendsto_weakly_to_fixedPoint_of_relaxedOperatorIteration_of_firmlyNonexpansive
        (douglasRachfordSplittingOperator_firmlyNonexpansive A B hA hB γ)
        hfix lam hlam hdiv y0 with
    ⟨y, hy, hy_tendsto⟩
  refine ⟨y, ?_, ?_⟩
  · -- Rewrite the Chapter 5 fixed point back to the reflected-resolvent owner.
    rw
      [← fixedPoints_douglasRachfordOperator_resolvent_eq_fixedPoints_reflectedResolventComposition
        A B hA hB γ]
    exact hy
  · -- The named Douglas--Rachford orbit is exactly the constant relaxed iteration of `T`.
    simpa [douglasRachfordIteration, T] using hy_tendsto

/-- Clause (2) of Theorem 26.11: under the Douglas--Rachford hypotheses, the residual sequence
`xₙ - zₙ` converges strongly to `0`. -/
theorem douglasRachfordAlgorithm_primal_auxiliary_gap_tendsto_zero
    (hzero : (primal_inclusion_solution_set A B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop) :
    Tendsto
      (fun n ↦
        douglasRachfordPrimalSequence A B hA hB γ lam y0 n -
          douglasRachfordAuxiliarySequence A B hA hB γ lam y0 n)
      atTop (𝓝 (0 : H)) := by
  let T : H → H :=
    douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ)
  have hfix : (fixedPoints T).Nonempty :=
    douglasRachfordFixedPointsNonempty A B hA hB γ hzero
  have hresidual :
      Tendsto
        (fun n ↦
          douglasRachfordAuxiliarySequence A B hA hB γ lam y0 n -
            douglasRachfordPrimalSequence A B hA hB γ lam y0 n)
        atTop (𝓝 (0 : H)) := by
    have hbase :=
      residual_tendsto_zero_of_relaxedOperatorIteration_of_firmlyNonexpansive
        (douglasRachfordSplittingOperator_firmlyNonexpansive A B hA hB γ)
        hfix lam hlam hdiv y0
    have hresidual_eq :
        (fun n ↦
          T (relaxedOperatorIteration (fun _ ↦ T) lam y0 n) -
            relaxedOperatorIteration (fun _ ↦ T) lam y0 n) =
          (fun n ↦
            douglasRachfordAuxiliarySequence A B hA hB γ lam y0 n -
              douglasRachfordPrimalSequence A B hA hB γ lam y0 n) := by
      funext n
      simpa [T, douglasRachfordIteration] using
        douglasRachfordResidual_eq_auxiliary_sub_primal A B hA hB γ lam y0 n
    -- Proposition 5.16 gives asymptotic regularity of the Douglas--Rachford residual.
    rw [hresidual_eq] at hbase
    exact hbase
  -- Negate the residual limit to match the source orientation `xₙ - zₙ`.
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hresidual.neg

end ExistenceAndResidual

section FixedPointConsequences

variable (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
variable (γ : PosReal) {y : H}
variable (hy_fix : y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ))

/-- Clause (1) of Theorem 26.11: if `y ∈ Fix R_{γ A} R_{γ B}`, then
`x = J_{γ B} y ∈ primal_inclusion_solution_set A B` and
`u = {}^[γ] B y ∈ dual_inclusion_solution_set A B`. -/
theorem douglasRachfordAlgorithm_limit_primal_dual_solution
    (hy_fix : y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ)) :
    resolventMap B hB γ y ∈ primal_inclusion_solution_set A B ∧
      yosidaApproximationMap B hB γ y ∈ dual_inclusion_solution_set A B := by
  constructor
  · -- Proposition 26.1 identifies primal solutions as the resolvent image of the fixed-point set.
    rw [primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_reflectedResolventComposition
      A B hA hB γ]
    exact ⟨y, hy_fix, rfl⟩
  · -- The dual conclusion is the companion Yosida image statement from the same proposition.
    rw [dual_inclusion_solution_set_eq_image_yosida_fixedPoints_reflectedResolventComposition
      A B hA hB γ]
    exact ⟨y, hy_fix, rfl⟩

/-- Helper for Theorem 26.11: a fixed point `y` determines the canonical graph witnesses
`(x, -u) ∈ gra A` and `(x, u) ∈ gra B`, where `x = J_{γ B} y` and `u = {}^[γ] B y`. -/
theorem douglasRachfordLimitGraphData
    (hy_fix : y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ)) :
    (-yosidaApproximationMap B hB γ y) ∈ A (resolventMap B hB γ y) ∧
      yosidaApproximationMap B hB γ y ∈ B (resolventMap B hB γ y) := by
  let x : H := resolventMap B hB γ y
  let u : H := yosidaApproximationMap B hB γ y
  have hu_mem : u ∈ ({}^[γ] B) y := by
    -- The Yosida realizer is the unique point of the singleton Yosida value.
    rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal B hB γ y]
    simp [u]
  have hy_decomp : y = x + (γ : ℝ) • u := by
    -- Rewrite `y` into its standard resolvent-plus-Yosida decomposition.
    simpa [x, u] using eq_resolventMap_add_smul_yosidaApproximationMap B hB γ y
  have huB : u ∈ B x := by
    -- Transport the Yosida graph witness from `y - γ • u` to `x`.
    have huB' : u ∈ B (y - (γ : ℝ) • u) :=
      (mem_yosidaApproximation_iff_mem B γ y u).1 hu_mem
    have hbase : y - (γ : ℝ) • u = x := by
      rw [hy_decomp]
      abel_nf
    simpa [hbase] using huB'
  have hargA : (2 : ℝ) • x - y = x - (γ : ℝ) • u := by
    -- Normalize the reflected resolvent argument to the usual resolvent graph form.
    simpa [x, u] using
      two_smul_resolventMap_sub_eq_sub_smul_yosidaApproximationMap B hB γ y
  have huA : -u ∈ A x := by
    -- The fixed-point equation for `y` is exactly the resolvent equation for `A` at `x`.
    have hresA : resolventMap A hA γ ((2 : ℝ) • x - y) = x := by
      have hyfix' :=
        (mem_fixedPoints_reflectedResolventComposition_iff_resolventMap_eq
          A B hA hB γ y).1 hy_fix
      simpa [x] using hyfix'
    rw [hargA] at hresA
    exact (resolventMap_sub_smul_eq_iff_neg_mem A hA γ x u).1 hresA
  exact ⟨by simpa [u] using huA, by simpa [x, u] using huB⟩

end FixedPointConsequences

section WeakConsequences

variable (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
variable (hzero : (primal_inclusion_solution_set A B).Nonempty)
variable (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
variable
  (hdiv :
    Tendsto
      (fun N ↦
        Finset.sum (Finset.range N)
          (fun n ↦ lam n * (2 - lam n)))
      atTop atTop)
variable (γ : PosReal) (y0 : H) {y : H}
variable (hy_fix : y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ))
variable
  (hy_tendsto :
    Tendsto
      (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n))
      atTop (𝓝 (toWeakSpace ℝ H y)))

omit [CompleteSpace H] in
/-- Helper for Theorem 26.11: subtracting a strongly null residual preserves the weak limit of a
sequence. -/
theorem tendstoWeaklyOfSubTendstoZeroSeq
    {aSeq bSeq : ℕ → H} {a : H}
    (ha :
      Tendsto (fun n ↦ toWeakSpace ℝ H (aSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H a)))
    (hsub : Tendsto (fun n ↦ aSeq n - bSeq n) atTop (𝓝 (0 : H))) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (bSeq n)) atTop
      (𝓝 (toWeakSpace ℝ H a)) := by
  -- Send the strong residual to `WeakSpace`, then subtract it from the known weak limit.
  have hsubWeak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (aSeq n - bSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H (0 : H))) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto (0 : H)).comp hsub
  simpa [sub_sub_cancel] using ha.sub hsubWeak

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 26.11: a localized modulus forced below `0` identifies the two points. -/
theorem eq_of_modulus_le_zero
    {p q : H} {φ : NNReal → EReal}
    (hφ_mono : Monotone φ)
    (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0)
    (hineq : φ ‖p - q‖₊ ≤ 0) :
    p = q := by
  -- Nonnegativity of the modulus collapses the lower bound to equality at `0`.
  have hφ_nonneg : (0 : EReal) ≤ φ ‖p - q‖₊ := by
    rw [← (hφ_zero 0).2 rfl]
    exact hφ_mono bot_le
  have hφ_eq_zero : φ ‖p - q‖₊ = 0 := le_antisymm hineq hφ_nonneg
  have hdist_zero : ‖p - q‖₊ = 0 := (hφ_zero _).1 hφ_eq_zero
  have hnorm_zero : ‖p - q‖ = 0 := by
    simpa using congrArg (fun r : NNReal ↦ (r : ℝ)) hdist_zero
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)

/-- Helper for Theorem 26.11: the Douglas--Rachford iterates produce the graph data
`(xₙ, uₙ) ∈ gra B`, `(zₙ, wₙ) ∈ gra A`, and the residual identity
`xₙ - zₙ = γ • (uₙ + wₙ)`. -/
theorem douglasRachfordGraphData
    (n : ℕ) :
    let y_n := douglasRachfordIteration A B hA hB γ lam y0
    let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
    let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
    let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
    let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
    (x_n n, u_n n) ∈ gra B ∧
      (z_n n, w_n n) ∈ gra A ∧
      x_n n - z_n n = (γ : ℝ) • (u_n n + w_n n) := by
  let y_n := douglasRachfordIteration A B hA hB γ lam y0
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
  have hu_eq : u_n n = (γ : ℝ)⁻¹ • (y_n n - x_n n) := by
    -- Unfold the dual iterate once to expose the scaled residual formula.
    simp [u_n, x_n, y_n, douglasRachfordDualSequence, douglasRachfordPrimalSequence,
      yosidaApproximationMap_apply]
  have hw_eq : w_n n = (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n n - y_n n - z_n n) := by
    -- The companion term is just its defining scaled reflected residual.
    simp [w_n]
  have hxu_mem : u_n n ∈ ({}^[γ] B) (y_n n) := by
    -- The canonical Yosida realizer is the unique point in the singleton Yosida value.
    rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal B hB γ]
    simp [u_n, y_n, douglasRachfordDualSequence, yosidaApproximationMap_apply]
  have hxu_graph :
      (x_n n, u_n n) ∈ gra B := by
    -- Rewrite the Yosida graph point on `yₙ` to the primal point `xₙ = J_{γ B} yₙ`.
    have hgraph :
        (y_n n - (γ : ℝ) • u_n n, u_n n) ∈ gra B :=
      (mem_yosidaApproximation_iff_mem_graph B γ (y_n n) (u_n n)).1 hxu_mem
    have hbase : y_n n - (γ : ℝ) • u_n n = x_n n := by
      -- Cancel the scaled Yosida residual back to the primal point.
      rw [hu_eq]
      simp [x_n, douglasRachfordPrimalSequence, γ.2.ne']
    simpa [hbase] using hgraph
  have hxz_mem : z_n n ∈ J[((γ : ℝ) • A)] ((2 : ℝ) • x_n n - y_n n) := by
    -- The auxiliary iterate is the canonical resolvent realizer of `A`.
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ ((2 : ℝ) • x_n n - y_n n)]
    simp [z_n, x_n, y_n, douglasRachfordAuxiliarySequence]
  have hzw_graph :
      (z_n n, w_n n) ∈ gra A := by
    -- The resolvent graph criterion identifies the companion term `wₙ`.
    have hgraph :
        (z_n n, (γ : ℝ)⁻¹ • (((2 : ℝ) • x_n n - y_n n) - z_n n)) ∈ gra A :=
      (mem_resolvent_smul_iff_mem_graph A γ ((2 : ℝ) • x_n n - y_n n) (z_n n)).1 hxz_mem
    simpa [w_n, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hgraph
  have hresidual :
      x_n n - z_n n = (γ : ℝ) • (u_n n + w_n n) := by
    -- Expanding the Yosida and companion terms collapses to the primal-auxiliary gap.
    have hsplit :
        (y_n n - x_n n) + ((2 : ℝ) • x_n n - y_n n - z_n n) = x_n n - z_n n := by
      simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    calc
      x_n n - z_n n = (y_n n - x_n n) + ((2 : ℝ) • x_n n - y_n n - z_n n) := by
        simpa using hsplit.symm
      _ = (γ : ℝ) • (u_n n + w_n n) := by
        rw [hu_eq, hw_eq]
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add, γ.2.ne']
  exact ⟨hxu_graph, hzw_graph, hresidual⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 26.11: a firmly nonexpansive self-map on the whole space is `1`-Lipschitz.
-/
theorem lipschitzWith_one_of_firmlyNonexpansiveOn_univ
    {T : H → H}
    (hT : FirmlyNonexpansiveOn (Set.univ : Set H) T) :
    LipschitzWith 1 T := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hfirm := (firmlyNonexpansiveOn_iff.mp hT) x (by simp) y (by simp)
  have hsq : ‖T x - T y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(x - T x) - (y - T y)‖]
  have hnorm : ‖T x - T y‖ ≤ ‖x - y‖ := by
    nlinarith [norm_nonneg (T x - T y), norm_nonneg (x - y), hsq]
  simpa [dist_eq_norm] using hnorm

/-- Helper for Theorem 26.11: the weakly convergent Douglas--Rachford orbit has a bounded primal
shadow sequence `xₙ = J_{γ B} yₙ`. -/
theorem douglasRachfordPrimalSequence_boundedRange
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y))) :
    Bornology.IsBounded
      (Set.range (douglasRachfordPrimalSequence A B hA hB γ lam y0)) := by
  let y_n := douglasRachfordIteration A B hA hB γ lam y0
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  have hy_bounded : Bornology.IsBounded (Set.range y_n) :=
    bounded_range_of_tendsto_weakly hy_tendsto
  have hfirm : FirmlyNonexpansive (resolventMap B hB γ) := by
    -- The resolvent is firmly nonexpansive on the whole space.
    simpa [FirmlyNonexpansive] using resolventMap_firmlyNonexpansiveOn_univ B hB γ
  have hLip : LipschitzWith 1 (resolventMap B hB γ) := by
    -- Repackage whole-space firm nonexpansiveness as a `1`-Lipschitz estimate.
    exact
      lipschitzWith_one_of_firmlyNonexpansiveOn_univ (T := resolventMap B hB γ) <| by
        simpa [FirmlyNonexpansive] using hfirm
  have hrange :
      Set.range x_n = (resolventMap B hB γ) '' Set.range y_n := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨y_n n, ⟨n, rfl⟩, rfl⟩
    · rintro ⟨y', ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
  -- Transport boundedness through the `1`-Lipschitz resolvent.
  rw [hrange]
  exact hLip.isBounded_image hy_bounded

/-- Helper for Theorem 26.11: along a weakly convergent primal subsequence, the auxiliary
subsequence has the same weak limit because the primal-auxiliary gap is strongly null. -/
theorem douglasRachfordAuxiliarySubsequence_tendsto_weakly
    (hzero : (primal_inclusion_solution_set A B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    {z : H} {φ : ℕ → ℕ}
    (hφmono : StrictMono φ)
    (hφx :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordPrimalSequence A B hA hB γ lam y0 (φ n)))
        atTop (𝓝 (toWeakSpace ℝ H z))) :
    Tendsto
      (fun n ↦ toWeakSpace ℝ H (douglasRachfordAuxiliarySequence A B hA hB γ lam y0 (φ n)))
      atTop (𝓝 (toWeakSpace ℝ H z)) := by
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  have hgap :
      Tendsto (fun n ↦ x_n n - z_n n) atTop (𝓝 (0 : H)) := by
    -- Start from the full-sequence primal-auxiliary gap theorem.
    simpa [x_n, z_n] using
      douglasRachfordAlgorithm_primal_auxiliary_gap_tendsto_zero
        (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
        (hdiv := hdiv) (γ := γ) (y0 := y0)
  have hgap_sub :
      Tendsto (fun n ↦ x_n (φ n) - z_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- Restrict the strong gap to the extracted subsequence.
    simpa [Function.comp, x_n, z_n] using hgap.comp hφmono.tendsto_atTop
  -- Transport the weak limit through the small residual bridge first.
  exact tendstoWeaklyOfSubTendstoZeroSeq hφx hgap_sub

/-- Helper for Theorem 26.11: along a primal cluster subsequence, the dual sequence converges
weakly to the normalized limit `γ⁻¹ • (y - z)`. -/
theorem douglasRachfordDualSubsequence_tendsto_weakly
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y)))
    {z : H} {φ : ℕ → ℕ}
    (hφmono : StrictMono φ)
    (hφx :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordPrimalSequence A B hA hB γ lam y0 (φ n)))
        atTop (𝓝 (toWeakSpace ℝ H z))) :
    Tendsto
      (fun n ↦ toWeakSpace ℝ H (douglasRachfordDualSequence A B hA hB γ lam y0 (φ n)))
      atTop (𝓝 (toWeakSpace ℝ H ((γ : ℝ)⁻¹ • (y - z)))) := by
  let y_n := douglasRachfordIteration A B hA hB γ lam y0
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
  have hy_subseq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (y_n (φ n))) atTop (𝓝 (toWeakSpace ℝ H y)) := by
    -- Restrict the weak limit of the Douglas--Rachford orbit to the chosen subsequence.
    simpa [y_n, Function.comp] using hy_tendsto.comp hφmono.tendsto_atTop
  have hdiff :=
    (hy_subseq.sub hφx).const_smul ((γ : ℝ)⁻¹)
  -- Normalize the dual subsequence through `u_n = γ⁻¹ • (y_n - x_n)`.
  simpa [u_n, y_n, x_n, douglasRachfordDualSequence, yosidaApproximationMap_apply,
    Function.comp, smul_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdiff

/-- Helper for Theorem 26.11: scaling the primal-auxiliary gap by `γ⁻¹` gives the summed dual
residual `uₙ + wₙ`. -/
theorem douglasRachfordScaledGap_eq_dualResidual
    (n : ℕ) :
    let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
    let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
    let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
    let w_n := fun k : ℕ ↦
      (γ : ℝ)⁻¹ •
        ((2 : ℝ) • x_n k - douglasRachfordIteration A B hA hB γ lam y0 k - z_n k)
    (γ : ℝ)⁻¹ • (x_n n - z_n n) = u_n n + w_n n := by
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  let w_n := fun k : ℕ ↦
    (γ : ℝ)⁻¹ •
      ((2 : ℝ) • x_n k - douglasRachfordIteration A B hA hB γ lam y0 k - z_n k)
  have hgraph := (douglasRachfordGraphData A B hA hB lam γ y0 n).2.2
  have hgap_eq : x_n n - z_n n = (γ : ℝ) • (u_n n + w_n n) := by
    -- Read the primal-auxiliary residual directly from the packaged graph data.
    simpa [x_n, u_n, z_n, w_n] using hgraph
  -- Scale the primal-auxiliary residual once and cancel `γ` against its inverse.
  calc
    (γ : ℝ)⁻¹ • (x_n n - z_n n) = (γ : ℝ)⁻¹ • ((γ : ℝ) • (u_n n + w_n n)) := by
      rw [hgap_eq]
    _ = u_n n + w_n n := by
      simp [smul_smul, γ.2.ne']

/-- Helper for Theorem 26.11: along a primal cluster subsequence, the dual residual
`w_(φ n) + u_(φ n)` is the scaled primal-auxiliary gap along the extracted subsequence. -/
theorem douglasRachfordDualResidualSubsequence_eq
    {φ : ℕ → ℕ} (n : ℕ) :
    let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
    let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
    let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
    let y_n := douglasRachfordIteration A B hA hB γ lam y0
    let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
    (γ : ℝ)⁻¹ • (x_n (φ n) - z_n (φ n)) = w_n (φ n) + u_n (φ n) := by
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  let y_n := douglasRachfordIteration A B hA hB γ lam y0
  let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
  -- Specialize the pointwise residual normalization to the extracted subsequence.
  simpa [x_n, u_n, z_n, y_n, w_n, add_comm] using
    (douglasRachfordScaledGap_eq_dualResidual
      (A := A) (B := B) hA hB (lam := lam) (γ := γ) (y0 := y0) (n := φ n))

/-- Helper for Theorem 26.11: along a primal cluster subsequence, the dual residual
`w_(φ n) + u_(φ n)` converges strongly to `0`. -/
theorem douglasRachfordDualResidualSubsequence_tendsto_zero
    (hzero : (primal_inclusion_solution_set A B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    {φ : ℕ → ℕ} (hφmono : StrictMono φ) :
    Tendsto
      (fun n ↦
        let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
        let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
        let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
        let y_n := douglasRachfordIteration A B hA hB γ lam y0
        let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
        w_n (φ n) + u_n (φ n))
      atTop (𝓝 (0 : H)) := by
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  let y_n := douglasRachfordIteration A B hA hB γ lam y0
  let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
  have hgap :
      Tendsto (fun n ↦ x_n n - z_n n) atTop (𝓝 (0 : H)) := by
    -- Start from the strong primal-auxiliary gap on the full sequence.
    simpa [x_n, z_n] using
      douglasRachfordAlgorithm_primal_auxiliary_gap_tendsto_zero
        (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
        (hdiv := hdiv) (γ := γ) (y0 := y0)
  have hgap_sub :
      Tendsto (fun n ↦ x_n (φ n) - z_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- Restrict the strong gap to the extracted subsequence.
    simpa [Function.comp, x_n, z_n] using hgap.comp hφmono.tendsto_atTop
  have hscaled :
      Tendsto (fun n ↦ (γ : ℝ)⁻¹ • (x_n (φ n) - z_n (φ n))) atTop (𝓝 (0 : H)) := by
    -- Scale the strong gap by `γ⁻¹` before rewriting it as the dual residual.
    simpa using hgap_sub.const_smul ((γ : ℝ)⁻¹)
  have hscaled_eq :
      (fun n ↦ (γ : ℝ)⁻¹ • (x_n (φ n) - z_n (φ n))) =
        (fun n ↦ w_n (φ n) + u_n (φ n)) := by
    funext n
    -- Consume the pointwise normalization once, then reuse it by rewriting.
    simpa [x_n, u_n, z_n, y_n, w_n] using
      douglasRachfordDualResidualSubsequence_eq
        (A := A) (B := B) hA hB (lam := lam) (γ := γ) (y0 := y0) (φ := φ) n
  rw [← hscaled_eq]
  exact hscaled

/-- Helper for Theorem 26.11: the `A`-graph witnesses persist along any extracted subsequence. -/
theorem douglasRachfordAuxiliaryGraphSubsequence_mem
    {φ : ℕ → ℕ} :
    ∀ n,
      let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
      let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
      let y_n := douglasRachfordIteration A B hA hB γ lam y0
      let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
      (z_n (φ n), w_n (φ n)) ∈ gra A := by
  intro n
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  let y_n := douglasRachfordIteration A B hA hB γ lam y0
  let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
  -- Read the `A`-graph point directly from the packaged Douglas--Rachford graph data.
  simpa [z_n, w_n] using (douglasRachfordGraphData A B hA hB lam γ y0 (φ n)).2.1

/-- Helper for Theorem 26.11: the `B`-graph witnesses persist along any extracted subsequence. -/
theorem douglasRachfordPrimalGraphSubsequence_mem
    {φ : ℕ → ℕ} :
    ∀ n,
      let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
      let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
      (x_n (φ n), u_n (φ n)) ∈ gra B := by
  intro n
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
  -- Read the `B`-graph point directly from the packaged Douglas--Rachford graph data.
  simpa [x_n, u_n] using (douglasRachfordGraphData A B hA hB lam γ y0 (φ n)).1

/-- Helper for Theorem 26.11: along any extracted subsequence, the residual in the
`z_(φ n) - x_(φ n)` orientation converges strongly to `0`. -/
theorem douglasRachfordAuxiliaryMinusPrimalSubsequence_tendsto_zero
    (hzero : (primal_inclusion_solution_set A B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    {φ : ℕ → ℕ} (hφmono : StrictMono φ) :
    Tendsto
      (fun n ↦
        let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
        let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
        z_n (φ n) - x_n (φ n))
      atTop (𝓝 (0 : H)) := by
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  have hgap :
      Tendsto (fun n ↦ x_n n - z_n n) atTop (𝓝 (0 : H)) := by
    -- Start from the strong primal-auxiliary gap on the full sequence.
    simpa [x_n, z_n] using
      douglasRachfordAlgorithm_primal_auxiliary_gap_tendsto_zero
        (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
        (hdiv := hdiv) (γ := γ) (y0 := y0)
  have hgap_sub :
      Tendsto (fun n ↦ x_n (φ n) - z_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- Restrict the strong gap to the extracted subsequence.
    simpa [Function.comp, x_n, z_n] using hgap.comp hφmono.tendsto_atTop
  -- Proposition 26.5 uses the residual in the `z_n - x_n` orientation.
  simpa [x_n, z_n, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hgap_sub.neg

/-- Helper for Theorem 26.11: the `L = id` specialization of Proposition 26.5 closes the
same-space `B`-graph limit without reintroducing any Douglas--Rachford transport. -/
theorem mem_graph_B_of_weak_primal_dual_residual_zero_id
    (hA : Maximal IsMonotone A)
    (hB : Maximal IsMonotone B)
    {xSeq uSeq ySeq vSeq : ℕ → H} {x v : H}
    (hxu : ∀ n, (xSeq n, uSeq n) ∈ gra A)
    (hyv : ∀ n, (ySeq n, vSeq n) ∈ gra B)
    (hx :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hv :
      Tendsto (fun n ↦ toWeakSpace ℝ H (vSeq n)) atTop (𝓝 (toWeakSpace ℝ H v)))
    (hxy : Tendsto (fun n ↦ xSeq n - ySeq n) atTop (𝓝 (0 : H)))
    (huv : Tendsto (fun n ↦ uSeq n + vSeq n) atTop (𝓝 (0 : H))) :
    (x, v) ∈ gra B := by
  have huv_id :
      Tendsto
        (fun n ↦ uSeq n + (ContinuousLinearMap.id ℝ H).adjoint (vSeq n))
        atTop (𝓝 (0 : H)) := by
    -- Normalize the dual residual to the exact Proposition 26.5 interface.
    simpa [ContinuousLinearMap.adjoint_id] using huv
  -- Freeze the identity-map specialization once so the graph-limit theorem only passes explicit
  -- subsequence data to Proposition 26.5.
  simpa [ContinuousLinearMap.id_apply, ContinuousLinearMap.adjoint_id] using
    (mem_graph_B_of_weak_primal_dual_residual_zero
      (L := ContinuousLinearMap.id ℝ H)
      (A := A)
      (B := B)
      (xSeq := xSeq)
      (uSeq := uSeq)
      (ySeq := ySeq)
      (vSeq := vSeq)
      (x := x)
      (v := v)
      hA hB hxu hyv hx hv hxy huv_id)

/-- Helper for Theorem 26.11: once the subsequence weak limits, graph memberships, and residual
limits are prepared, Proposition 26.5 closes the limiting `B`-graph point. -/
theorem weakClusterPoint_mem_graphBLimit_of_subsequence
    {y z : H} {φ : ℕ → ℕ}
    (hz_subseq :
      let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (z_n (φ n)))
        atTop (𝓝 (toWeakSpace ℝ H z)))
    (hu_subseq :
      let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (u_n (φ n)))
        atTop (𝓝 (toWeakSpace ℝ H ((γ : ℝ)⁻¹ • (y - z)))))
    (hgraphA :
      let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
      let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
      let y_n := douglasRachfordIteration A B hA hB γ lam y0
      let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
      ∀ n, (z_n (φ n), w_n (φ n)) ∈ gra A)
    (hgraphB :
      let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
      let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
      ∀ n, (x_n (φ n), u_n (φ n)) ∈ gra B)
    (hresidual :
      let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
      let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
      Tendsto (fun n ↦ z_n (φ n) - x_n (φ n)) atTop (𝓝 (0 : H)))
    (hdualResidual :
      let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
      let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
      let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
      let y_n := douglasRachfordIteration A B hA hB γ lam y0
      let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
      Tendsto (fun n ↦ w_n (φ n) + u_n (φ n)) atTop (𝓝 (0 : H))) :
    (z, (γ : ℝ)⁻¹ • (y - z)) ∈ gra B := by
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  let y_n := douglasRachfordIteration A B hA hB γ lam y0
  let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
  -- Route correction: freeze the `L = id` specialization once, then feed it only the prepared
  -- subsequence weak limits, graph memberships, and residual limits.
  simpa [x_n, u_n, z_n, y_n, w_n] using
    (mem_graph_B_of_weak_primal_dual_residual_zero_id
      (A := A)
      (B := B)
      (hA := hA)
      (hB := hB)
      (xSeq := fun n ↦ z_n (φ n))
      (uSeq := fun n ↦ w_n (φ n))
      (ySeq := fun n ↦ x_n (φ n))
      (vSeq := fun n ↦ u_n (φ n))
      (x := z)
      (v := (γ : ℝ)⁻¹ • (y - z))
      hgraphA hgraphB hz_subseq hu_subseq hresidual hdualResidual)

/-- Helper for Theorem 26.11: every weak cluster point of the primal shadow sequence produces the
limiting graph point of `B` needed in the `L = id` specialization of Proposition 26.5. -/
private theorem weakClusterPoint_mem_graphBLimit
    (hzero : (primal_inclusion_solution_set A B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y)))
    {z : H}
    (hz :
      IsSequentialClusterPt
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordPrimalSequence A B hA hB γ lam y0 n))
        (toWeakSpace ℝ H z)) :
    (z, (γ : ℝ)⁻¹ • (y - z)) ∈ gra B := by
  rcases hz.exists_subseq_tendsto with ⟨φ, hφmono, hφx⟩
  let y_n := douglasRachfordIteration A B hA hB γ lam y0
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
  have hz_subseq :
      Tendsto (fun n ↦ toWeakSpace ℝ H (z_n (φ n))) atTop (𝓝 (toWeakSpace ℝ H z)) := by
    -- Route correction: first transport the weak cluster limit from `x_(φ n)` to `z_(φ n)`.
    simpa [z_n] using
      douglasRachfordAuxiliarySubsequence_tendsto_weakly
        (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
        (hdiv := hdiv) (γ := γ) (y0 := y0) hφmono hφx
  have hu_subseq :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (u_n (φ n)))
        atTop (𝓝 (toWeakSpace ℝ H ((γ : ℝ)⁻¹ • (y - z)))) := by
    -- Normalize the dual subsequence via `u_n = γ⁻¹ • (y_n - x_n)`.
    simpa [u_n] using
      douglasRachfordDualSubsequence_tendsto_weakly
        (A := A) (B := B) hA hB (lam := lam) (γ := γ) (y0 := y0)
        hy_tendsto hφmono hφx
  have hgraphA :
      ∀ n, (z_n (φ n), w_n (φ n)) ∈ gra A := by
    -- Reuse the standalone `A`-graph helper to refresh the elaboration budget.
    simpa [z_n, w_n] using
      (douglasRachfordAuxiliaryGraphSubsequence_mem
        (A := A) (B := B) hA hB (lam := lam) (γ := γ) (y0 := y0) (φ := φ))
  have hgraphB :
      ∀ n, (x_n (φ n), u_n (φ n)) ∈ gra B := by
    -- Reuse the standalone `B`-graph helper to refresh the elaboration budget.
    simpa [x_n, u_n] using
      (douglasRachfordPrimalGraphSubsequence_mem
        (A := A) (B := B) hA hB (lam := lam) (γ := γ) (y0 := y0) (φ := φ))
  have hresidual :
      Tendsto (fun n ↦ z_n (φ n) - x_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- Reuse the standalone residual helper to keep the final specialization transport-light.
    simpa [x_n, z_n] using
      douglasRachfordAuxiliaryMinusPrimalSubsequence_tendsto_zero
        (A := A) (B := B) hA hB (lam := lam) (hzero := hzero) (hlam := hlam)
        (hdiv := hdiv) (γ := γ) (y0 := y0) (φ := φ) hφmono
  have hdualResidual :
      Tendsto (fun n ↦ w_n (φ n) + u_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- Close the last transport bridge with the normalized residual identity.
    simpa [w_n, u_n, x_n, y_n, z_n] using
      douglasRachfordDualResidualSubsequence_tendsto_zero
        (A := A) (B := B) hA hB (lam := lam) (hzero := hzero) (hlam := hlam)
        (hdiv := hdiv) (γ := γ) (y0 := y0) (φ := φ) hφmono
  -- Route correction: reduce the main theorem to the fixed-subsequence graph-limit helper.
  exact
    weakClusterPoint_mem_graphBLimit_of_subsequence
      (A := A) (B := B) hA hB (lam := lam) (γ := γ) (y0 := y0) (y := y) (z := z) (φ := φ)
      hz_subseq hu_subseq hgraphA hgraphB hresidual hdualResidual

/-- Helper for Theorem 26.11: every weak cluster point of the primal sequence is the resolvent
limit `J_{γ B} y`. -/
theorem weakClusterPoint_eq_resolventLimit
    (hzero : (primal_inclusion_solution_set A B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y)))
    {z : H}
    (hz :
      IsSequentialClusterPt
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordPrimalSequence A B hA hB γ lam y0 n))
        (toWeakSpace ℝ H z)) :
    z = resolventMap B hB γ y := by
  have hz_graph :
      (z, (γ : ℝ)⁻¹ • (y - z)) ∈ gra B :=
    weakClusterPoint_mem_graphBLimit
      (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
      (hdiv := hdiv) (γ := γ) (y0 := y0) (hy_tendsto := hy_tendsto) hz
  have hz_mem : z ∈ J[((γ : ℝ) • B)] y :=
    (mem_resolvent_smul_iff_mem_graph B γ y z).2 hz_graph
  -- Singleton-valuedness of the maximal-monotone resolvent identifies the cluster point.
  rw [resolvent_smul_eq_singleton_resolventMap_of_maximal B hB γ y] at hz_mem
  simpa using hz_mem

/-- Clause (3) of Theorem 26.11: with `y` as in the existence clause, the shadow sequence `xₙ`
and the auxiliary sequence `zₙ` both converge weakly to `J_{γ B} y`. -/
theorem douglasRachfordAlgorithm_primal_auxiliary_tendsto_weakly
    (hzero : (primal_inclusion_solution_set A B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hy_fix : y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ))
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y))) :
    Tendsto
      (fun n ↦ toWeakSpace ℝ H (douglasRachfordPrimalSequence A B hA hB γ lam y0 n))
      atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))) ∧
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordAuxiliarySequence A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))) := by
  -- Keep the fixed-point hypothesis explicit in the clause interface.
  let _ := hy_fix
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  have hx_bounded : Bornology.IsBounded (Set.range x_n) :=
    douglasRachfordPrimalSequence_boundedRange A B hA hB lam γ y0 hy_tendsto
  have hunique :
      ∀ z₁ z₂ : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x_n n)) (toWeakSpace ℝ H z₁) →
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x_n n)) (toWeakSpace ℝ H z₂) →
          z₁ = z₂ := by
    intro z₁ z₂ hz₁ hz₂
    calc
      z₁ = resolventMap B hB γ y :=
        weakClusterPoint_eq_resolventLimit
          (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
          (hdiv := hdiv) (γ := γ) (y0 := y0) (hy_tendsto := hy_tendsto) hz₁
      _ = z₂ := by
            symm
            exact
              weakClusterPoint_eq_resolventLimit
                (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
                (hdiv := hdiv) (γ := γ) (y0 := y0) (hy_tendsto := hy_tendsto) hz₂
  rcases
      (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint x_n).2
        ⟨hx_bounded, hunique⟩ with
    ⟨x, hx_tendsto_raw⟩
  have hx_cluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x_n n)) (toWeakSpace ℝ H x) := by
    -- The convergent full primal sequence witnesses its own weak cluster point.
    exact ⟨id, strictMono_id, by simpa using hx_tendsto_raw⟩
  have hx_eq : x = resolventMap B hB γ y :=
    weakClusterPoint_eq_resolventLimit
      (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
      (hdiv := hdiv) (γ := γ) (y0 := y0) (hy_tendsto := hy_tendsto) hx_cluster
  have hx_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (x_n n))
        atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))) := by
    -- Identify the unique weak limit with the resolvent point from the graph bridge.
    simpa [x_n, hx_eq] using hx_tendsto_raw
  have hgap :
      Tendsto (fun n ↦ x_n n - z_n n) atTop (𝓝 (0 : H)) := by
    -- Clause (2) transports the primal weak limit to the auxiliary sequence.
    simpa [x_n, z_n] using
      douglasRachfordAlgorithm_primal_auxiliary_gap_tendsto_zero
        (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
        (hdiv := hdiv) (γ := γ) (y0 := y0)
  have hz_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (z_n n))
        atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))) :=
    tendstoWeaklyOfSubTendstoZeroSeq hx_tendsto hgap
  exact ⟨by simpa [x_n] using hx_tendsto, by simpa [z_n] using hz_tendsto⟩

/-- Clause (4) of Theorem 26.11: with `y` as in the existence clause, the dual sequence `uₙ`
converges weakly to `{}^[γ] B y`. -/
theorem douglasRachfordAlgorithm_dual_tendsto_weakly
    (hzero : (primal_inclusion_solution_set A B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hy_fix : y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ))
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y))) :
    Tendsto
      (fun n ↦ toWeakSpace ℝ H (douglasRachfordDualSequence A B hA hB γ lam y0 n))
      atTop (𝓝 (toWeakSpace ℝ H (yosidaApproximationMap B hB γ y))) := by
  have hx_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordPrimalSequence A B hA hB γ lam y0 n))
      atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))) :=
    (douglasRachfordAlgorithm_primal_auxiliary_tendsto_weakly
      (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
      (hdiv := hdiv) (γ := γ) (y0 := y0) (hy_fix := hy_fix) (hy_tendsto := hy_tendsto)).1
  have hdiff :
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n) -
            toWeakSpace ℝ H (douglasRachfordPrimalSequence A B hA hB γ lam y0 n))
        atTop
        (𝓝
          (toWeakSpace ℝ H y -
            toWeakSpace ℝ H (resolventMap B hB γ y))) :=
    hy_tendsto.sub hx_tendsto
  -- Scale the weak difference `yₙ - xₙ` by `γ⁻¹` to recover the dual sequence.
  simpa [douglasRachfordDualSequence, yosidaApproximationMap_apply, sub_eq_add_neg, smul_sub,
    add_assoc, add_left_comm, add_comm] using hdiff.const_smul ((γ : ℝ)⁻¹)

end WeakConsequences

section AffineNormalConeCase

variable (C : AffineSubspace ℝ H) (hC_nonempty : (C : Set H).Nonempty)
variable (hC_closed : IsClosed (C : Set H))
variable (B : SetValuedOperator H H) (hB : Maximal IsMonotone B)
local notation "hC" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex
local notation "hNC" =>
  Set.normalCone_isMaximallyMonotone hC_nonempty hC_closed C.convex

variable (hzero : (primal_inclusion_solution_set N[(C : Set H)] B).Nonempty)
variable (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
variable
  (hdiv :
    Tendsto
      (fun N ↦
        Finset.sum (Finset.range N)
          (fun n ↦ lam n * (2 - lam n)))
      atTop atTop)
variable (γ : PosReal) (y0 : H) {y : H}
variable
  (hy_fix : y ∈ fixedPoints (reflectedResolventComposition N[(C : Set H)] B hNC hB γ))
variable
  (hy_tendsto :
    Tendsto
      (fun n ↦
        toWeakSpace ℝ H
          (douglasRachfordIteration N[(C : Set H)] B hNC hB γ lam y0 n))
      atTop (𝓝 (toWeakSpace ℝ H y)))

/-- Helper for Theorem 26.11: for a closed affine subspace `C`, the normal-cone resolvent is the
metric projector `P[(C : Set H), hC]`. -/
theorem resolventMap_normalConeAffine_eq_projectionPoint
    (x : H) :
    resolventMap N[(C : Set H)] hNC γ x = P[(C : Set H), hC] x := by
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set H) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set H) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  have hpC : P[(C : Set H), hC] x ∈ (C : Set H) := by
    exact projectionPoint_mem (C : Set H) hC x
  have horth : x - P[(C : Set H), hC] x ∈ C.directionᗮ := by
    -- Replace the projector with the affine orthogonal projection and read off the residual
    -- orthogonality.
    have hEq : x - P[(C : Set H), hC] x = x -ᵥ (orthogonalProjection C x : C) := by
      simpa [vsub_eq_sub] using congrArg (fun z : H ↦ x - z)
        (projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
          hC_nonempty hC_closed x)
    rw [hEq]
    exact vsub_orthogonalProjection_mem_direction_orthogonal C x
  have hscaled :
      (γ : ℝ)⁻¹ • (x - P[(C : Set H), hC] x) ∈ (C.directionᗮ : Set H) := by
    exact Submodule.smul_mem (C.directionᗮ) _ horth
  have hp_mem :
      P[(C : Set H), hC] x ∈ J[((γ : ℝ) • N[(C : Set H)])] x := by
    -- The projector point satisfies the normal-cone resolvent graph criterion.
    refine (mem_resolvent_smul_iff_mem_graph N[(C : Set H)] γ x _).2 ?_
    simpa [mem_graph, normalCone_affineSubspace_eq_direction_orthogonal_of_mem C hpC] using
      hscaled
  -- Singleton-valuedness of the maximal-monotone resolvent identifies the chosen realizer.
  rw [resolvent_smul_eq_singleton_resolventMap_of_maximal N[(C : Set H)] hNC γ x] at hp_mem
  simpa using hp_mem.symm

/-- Helper for Theorem 26.11: a fixed point of the reflected normal-cone Douglas--Rachford map
forces agreement between the affine projector `P_C` and the resolvent `J_{γ B}` at the limit
point. -/
theorem affineProjector_eq_resolventLimit_of_fixedPoint
    (hy_fix :
      y ∈ fixedPoints (reflectedResolventComposition N[(C : Set H)] B hNC hB γ)) :
    P[(C : Set H), hC] y = resolventMap B hB γ y := by
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set H) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set H) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  let x : H := resolventMap B hB γ y
  have hy_fix_dr :
      y ∈ fixedPoints
        (douglasRachfordOperator (resolventMap N[(C : Set H)] hNC γ) (resolventMap B hB γ)) := by
    -- Rewrite the reflected-resolvent fixed point into the Chapter 4 Douglas--Rachford owner.
    rw [fixedPoints_douglasRachfordOperator_resolvent_eq_fixedPoints_reflectedResolventComposition
      N[(C : Set H)] B hNC hB γ]
    exact hy_fix
  have hx_proj : P[(C : Set H), hC] ((2 : ℝ) • x - y) = x := by
    -- The fixed-point equation identifies the normal-cone resolvent point with `x = J_{γ B} y`.
    have hy_eq :
        douglasRachfordOperator (resolventMap N[(C : Set H)] hNC γ) (resolventMap B hB γ) y = y :=
      hy_fix_dr
    have hres_eq : resolventMap N[(C : Set H)] hNC γ ((2 : ℝ) • x - y) = x := by
      have hcore :
          resolventMap N[(C : Set H)] hNC γ ((2 : ℝ) • x - y) + y - x = y := by
        simpa [x, douglasRachfordOperator_apply] using hy_eq
      have hsum :
          resolventMap N[(C : Set H)] hNC γ ((2 : ℝ) • x - y) + y = y + x :=
        sub_eq_iff_eq_add.mp hcore
      have hsum' :
          resolventMap N[(C : Set H)] hNC γ ((2 : ℝ) • x - y) + y = x + y := by
        simpa [add_comm] using hsum
      exact add_right_cancel hsum'
    rw [resolventMap_normalConeAffine_eq_projectionPoint (C := C) (hC_nonempty := hC_nonempty)
      (hC_closed := hC_closed) (γ := γ) ((2 : ℝ) • x - y)] at hres_eq
    exact hres_eq
  have hx_mem : x ∈ (C : Set H) := by
    simpa [hx_proj] using projectionPoint_mem (C : Set H) hC ((2 : ℝ) • x - y)
  have hy_orth : y - x ∈ C.directionᗮ := by
    -- Route correction: recover the residual orthogonality from the projector equation at
    -- `2x - y`, then negate it to target the point `y`.
    have hx_proj_orth : (orthogonalProjection C ((2 : ℝ) • x - y) : H) = x := by
      rw [← projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
        hC_nonempty hC_closed ((2 : ℝ) • x - y)]
      simpa using hx_proj
    have hchar := (coe_orthogonalProjection_eq_iff_mem).mp hx_proj_orth
    rcases hchar with ⟨_, horth⟩
    have horth' : x - y ∈ C.directionᗮ := by
      simpa [vsub_eq_sub, sub_eq_add_neg, two_smul, add_assoc, add_left_comm, add_comm] using horth
    have hneg : -(x - y) ∈ C.directionᗮ := Submodule.neg_mem _ horth'
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg
  have hy_proj : P[(C : Set H), hC] y = x := by
    have hy_proj_orth : (orthogonalProjection C y : H) = x := by
      refine (coe_orthogonalProjection_eq_iff_mem).2 ?_
      exact ⟨hx_mem, hy_orth⟩
    simpa [x] using
      (projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
        hC_nonempty hC_closed y).trans hy_proj_orth
  -- Replace the affine projector by the orthogonal projection and conclude with the agreement
  -- identity.
  simpa [x] using hy_proj

/-- Clause (5) of Theorem 26.11: if `A = N[(C : Set H)]` for a nonempty closed affine subspace
`C`, then the projected orbit `P[(C : Set H), hC] yₙ` converges weakly to `J_{γ B} y`. -/
theorem douglasRachfordAlgorithm_affineProjector_tendsto_weakly
    (hzero : (primal_inclusion_solution_set N[(C : Set H)] B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hy_fix :
      y ∈ fixedPoints (reflectedResolventComposition N[(C : Set H)] B hNC hB γ))
    (hy_tendsto :
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (douglasRachfordIteration N[(C : Set H)] B hNC hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y))) :
    Tendsto
      (fun n ↦
        toWeakSpace ℝ H
          (P[(C : Set H), hC]
            (douglasRachfordIteration N[(C : Set H)] B hNC hB γ lam y0 n)))
      atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))) :=
by
  -- Keep the full theorem hypotheses explicit even though this clause only uses the limit data.
  let _ := hzero
  let _ := hlam
  let _ := hdiv
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set H) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set H) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  have hproj_weak :
      WeaklyContinuous (fun x : (Set.univ : Set H) ↦ P[(C : Set H), hC] x) :=
    projectionPoint_weaklyContinuous_of_nonempty_isClosed_affineSubspace
      hC_nonempty hC_closed
  have hproj_tendsto :
      Tendsto
        (fun n ↦
          toWeakSpace ℝ H
            (P[(C : Set H), hC]
              (douglasRachfordIteration N[(C : Set H)] B hNC hB γ lam y0 n)))
        atTop (𝓝 (toWeakSpace ℝ H (P[(C : Set H), hC] y))) := by
    -- Push the weak limit of `yₙ` through the weakly continuous affine projector.
    exact
      (weaklyContinuous_iff_forall_net_tendsto.mp hproj_weak)
        (fun n ↦
          ⟨douglasRachfordIteration N[(C : Set H)] B hNC hB γ lam y0 n, by simp⟩)
        ⟨y, by simp⟩
        (by simpa using hy_tendsto)
  have hy_proj :
      P[(C : Set H), hC] y = resolventMap B hB γ y :=
    affineProjector_eq_resolventLimit_of_fixedPoint
      (C := C) (hC_nonempty := hC_nonempty) (hC_closed := hC_closed)
      (B := B) (hB := hB) (γ := γ) hy_fix
  -- Rewrite the projector limit point to the resolvent limit using the fixed-point agreement
  -- helper.
  simpa [hy_proj] using hproj_tendsto

end AffineNormalConeCase

section UniformMonotoneConsequences

variable (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
variable (hzero : (primal_inclusion_solution_set A B).Nonempty)
variable (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
variable
  (hdiv :
    Tendsto
      (fun N ↦
        Finset.sum (Finset.range N)
          (fun n ↦ lam n * (2 - lam n)))
      atTop atTop)
variable (γ : PosReal) (y0 : H) {y : H}
variable (hy_fix : y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ))
variable
  (hy_tendsto :
    Tendsto
      (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n))
      atTop (𝓝 (toWeakSpace ℝ H y)))

/-- Helper for Theorem 26.11: under the localized uniform-monotonicity branch, every primal
solution coincides with the resolvent point selected by the fixed point `y`. -/
theorem primalSolution_eq_resolventLimit_of_uniformBranch
    {q : H}
    (hy_fix : y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ))
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ A.dom → A.IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S)
    (hq : q ∈ primal_inclusion_solution_set A B) :
    q = resolventMap B hB γ y := by
  let x : H := resolventMap B hB γ y
  let u : H := yosidaApproximationMap B hB γ y
  rcases
      (mem_primal_inclusion_solution_set_iff_exists_mem_dual_inclusion_solution_set A B).1 hq with
    ⟨uq, _huqD, hqA, hqB⟩
  have hx_graph := douglasRachfordLimitGraphData A B hA hB γ hy_fix
  have hxA : -u ∈ A x := by
    simpa [x, u] using hx_graph.1
  have hxB : u ∈ B x := by
    simpa [x, u] using hx_graph.2
  have hA_mono : A.IsMonotone := SetValuedOperator.Maximal.isMonotone hA
  have hB_mono : B.IsMonotone := SetValuedOperator.Maximal.isMonotone hB
  rw [isMonotone_iff] at hA_mono hB_mono
  rcases hUniform with hUniformA | hUniformB
  · let S : Set H := Set.insert x ({q} : Set H)
    have hxS : x ∈ S := by
      exact Set.mem_insert x ({q} : Set H)
    have hqS : q ∈ S := by
      exact Set.mem_insert_of_mem x (by simp)
    have hS_nonempty : S.Nonempty := ⟨x, hxS⟩
    have hS_bounded : Bornology.IsBounded S := by
      exact ((Set.finite_singleton q).insert x).isBounded
    have hS_subA : S ⊆ A.dom := by
      intro r hr
      rcases Set.mem_insert_iff.mp hr with hr | hr
      · subst r
        exact (SetValuedOperator.mem_dom_iff A x).2 ⟨-u, hxA⟩
      · rcases Set.mem_singleton_iff.mp hr with rfl
        exact (SetValuedOperator.mem_dom_iff A _).2 ⟨-uq, hqA⟩
    rcases hUniformA S hS_nonempty hS_bounded hS_subA with ⟨φ, hφ⟩
    have hineq :
        φ ‖q - x‖₊ ≤ (0 : EReal) := by
      have hAineq :
          φ ‖q - x‖₊ ≤ (⟪q - x, (-uq) - (-u)⟫_ℝ : EReal) := by
        simpa [x, u] using hφ.ineq hqS hxS hqA hxA
      have hupper_real : ⟪q - x, (-uq) - (-u)⟫_ℝ ≤ 0 := by
        have hpair_nonneg : 0 ≤ ⟪q - x, uq - u⟫_ℝ := hB_mono hqB hxB
        have hneg_eq : ⟪q - x, (-uq) - (-u)⟫_ℝ = -⟪q - x, uq - u⟫_ℝ := by
          have hterm : (-uq) - (-u) = -(uq - u) := by
            abel_nf
          rw [hterm, inner_neg_right]
        rw [hneg_eq]
        linarith
      have hupper : (⟪q - x, (-uq) - (-u)⟫_ℝ : EReal) ≤ 0 := by
        exact_mod_cast hupper_real
      exact le_trans hAineq hupper
    exact eq_of_modulus_le_zero hφ.monotone hφ.modulus_eq_zero_iff hineq
  · let S : Set H := Set.insert x ({q} : Set H)
    have hxS : x ∈ S := by
      exact Set.mem_insert x ({q} : Set H)
    have hqS : q ∈ S := by
      exact Set.mem_insert_of_mem x (by simp)
    have hS_nonempty : S.Nonempty := ⟨x, hxS⟩
    have hS_bounded : Bornology.IsBounded S := by
      exact ((Set.finite_singleton q).insert x).isBounded
    have hS_subB : S ⊆ B.dom := by
      intro r hr
      rcases Set.mem_insert_iff.mp hr with hr | hr
      · subst r
        exact (SetValuedOperator.mem_dom_iff B x).2 ⟨u, hxB⟩
      · rcases Set.mem_singleton_iff.mp hr with rfl
        exact (SetValuedOperator.mem_dom_iff B _).2 ⟨uq, hqB⟩
    rcases hUniformB S hS_nonempty hS_bounded hS_subB with ⟨φ, hφ⟩
    have hineq :
        φ ‖q - x‖₊ ≤ (0 : EReal) := by
      have hBineq :
          φ ‖q - x‖₊ ≤ (⟪q - x, uq - u⟫_ℝ : EReal) := by
        simpa [x, u] using hφ.ineq hqS hxS hqB hxB
      have hupper_real : ⟪q - x, uq - u⟫_ℝ ≤ 0 := by
        have hpairA : 0 ≤ ⟪q - x, u - uq⟫_ℝ := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hA_mono hqA hxA
        have hneg :
            ⟪q - x, u - uq⟫_ℝ = -⟪q - x, uq - u⟫_ℝ := by
          have hterm : u - uq = -(uq - u) := by
            abel_nf
          rw [hterm, inner_neg_right]
        linarith
      have hupper : (⟪q - x, uq - u⟫_ℝ : EReal) ≤ 0 := by
        exact_mod_cast hupper_real
      exact le_trans hBineq hupper
    exact eq_of_modulus_le_zero hφ.monotone hφ.modulus_eq_zero_iff hineq

/-- Clause (6) of Theorem 26.11: if `y ∈ Fix R_{γ A} R_{γ B}` and, in addition, `A` or `B` is
uniformly monotone on every nonempty bounded subset of its domain, then the primal solution set
is the singleton `{J_{γ B} y}`. -/
theorem douglasRachfordAlgorithm_unique_primal_solution_of_uniformlyMonotoneOnEveryBoundedSubset
    (hy_fix : y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ))
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ A.dom → A.IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S) :
    primal_inclusion_solution_set A B = {resolventMap B hB γ y} :=
by
  ext q
  constructor
  · intro hq
    -- Localize the uniform monotonicity branch to the two-point set `{q, J_{γ B} y}`.
    exact Set.mem_singleton_iff.mpr <|
      primalSolution_eq_resolventLimit_of_uniformBranch
        A B hA hB γ hy_fix hUniform hq
  · intro hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    -- Clause (1) already places the limit resolvent point in the primal solution set.
    exact (douglasRachfordAlgorithm_limit_primal_dual_solution A B hA hB γ hy_fix).1

/-- Helper for Theorem 26.11: if a localized modulus is controlled by pairings of a strongly null
residual and a weakly null companion, then the base sequence converges strongly. -/
theorem tendsto_of_modulusPairing_of_tendsto_zero_of_tendsto_weakly
    {s a b : ℕ → H} {p : H} {φ : NNReal → EReal}
    (ha_tendsto : Tendsto a atTop (𝓝 (0 : H)))
    (hb_tendsto :
      Tendsto (fun n ↦ toWeakSpace ℝ H (b n)) atTop (𝓝 (toWeakSpace ℝ H (0 : H))))
    (hφ_mono : Monotone φ)
    (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0)
    (hineq : ∀ n, φ ‖s n - p‖₊ ≤ (⟪a n, b n⟫_ℝ : EReal)) :
    Tendsto s atTop (𝓝 p) := by
  have hinner_tendsto :
      Tendsto (fun n ↦ ⟪a n, b n⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    -- Feed the weak term to Lemma 2.51(iii) and then commute the real inner product once.
    simpa [real_inner_comm] using
      tendsto_inner_of_tendsto_weakly_of_tendsto b a (0 : H) (0 : H) hb_tendsto ha_tendsto
  by_contra hnot
  rw [Metric.tendsto_atTop] at hnot
  push Not at hnot
  rcases hnot with ⟨ε, hε, hbad⟩
  have hfreq : ∃ᶠ n in atTop, ε ≤ dist (s n) p := by
    rw [frequently_atTop]
    intro N
    rcases hbad N with ⟨n, hnN, hndist⟩
    exact ⟨n, hnN, hndist⟩
  rcases extraction_of_frequently_atTop hfreq with ⟨ψ, hψmono, hψdist⟩
  let εNN : NNReal := ⟨ε, hε.le⟩
  have hφ_nonneg : (0 : EReal) ≤ φ εNN := by
    rw [← (hφ_zero 0).2 rfl]
    exact hφ_mono bot_le
  have hφ_ne_zero : φ εNN ≠ 0 := by
    intro hzero
    have hεNN_zero : εNN = 0 := (hφ_zero εNN).1 hzero
    exact (ne_of_gt hε) <| by
      simpa [εNN] using congrArg (fun r : NNReal ↦ (r : ℝ)) hεNN_zero
  have hφ_subseq :
      ∀ n, φ εNN ≤ (⟪a (ψ n), b (ψ n)⟫_ℝ : EReal) := by
    intro n
    have hε_le : εNN ≤ ‖s (ψ n) - p‖₊ := by
      exact_mod_cast (show ε ≤ ‖s (ψ n) - p‖ by simpa [dist_eq_norm] using hψdist n)
    exact le_trans (hφ_mono hε_le) (hineq (ψ n))
  have hφ_top : φ εNN ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hφ_subseq 0)
  have hφ_bot : φ εNN ≠ ⊥ := by
    intro hbot
    rw [hbot] at hφ_nonneg
    simp at hφ_nonneg
  let c : ℝ := (φ εNN).toReal
  have hc_pos : 0 < c := by
    have hφ_pos : (0 : EReal) < φ εNN := lt_of_le_of_ne hφ_nonneg (Ne.symm hφ_ne_zero)
    simpa [c] using EReal.toReal_pos hφ_pos hφ_top
  have hinner_subseq :
      Tendsto (fun n ↦ ⟪a (ψ n), b (ψ n)⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    exact hinner_tendsto.comp hψmono.tendsto_atTop
  have hlow_real : ∀ n, c ≤ ⟪a (ψ n), b (ψ n)⟫_ℝ := by
    intro n
    simpa [c] using
      EReal.toReal_le_toReal (hφ_subseq n) hφ_bot (by simp)
  rcases (Metric.tendsto_atTop.1 hinner_subseq) (c / 2) (by linarith) with ⟨N, hN⟩
  have htail : dist (⟪a (ψ N), b (ψ N)⟫_ℝ) 0 < c / 2 := hN N le_rfl
  have habs_lt : |⟪a (ψ N), b (ψ N)⟫_ℝ| < c / 2 := by
    simpa [dist_eq_norm] using htail
  have habs_ge : c ≤ |⟪a (ψ N), b (ψ N)⟫_ℝ| := by
    exact le_trans (hlow_real N) (le_abs_self _)
  linarith

/-- Helper for Theorem 26.11: under branch (6b), weak convergence plus localized uniform
monotonicity of `B` upgrades the primal and auxiliary Douglas--Rachford sequences to strong
convergence. -/
theorem douglasRachfordAlgorithm_primal_auxiliary_tendsto_of_uniformlyMonotoneBOnEveryBoundedSubset
    (hx_weak :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordPrimalSequence A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))))
    (hz_weak :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordAuxiliarySequence A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H (resolventMap B hB γ y))))
    (hu_weak :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordDualSequence A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H (yosidaApproximationMap B hB γ y))))
    (hgap :
      Tendsto
        (fun n ↦
          douglasRachfordPrimalSequence A B hA hB γ lam y0 n -
            douglasRachfordAuxiliarySequence A B hA hB γ lam y0 n)
        atTop (𝓝 (0 : H)))
    (hgap_neg :
      Tendsto
        (fun n ↦
          douglasRachfordAuxiliarySequence A B hA hB γ lam y0 n -
            douglasRachfordPrimalSequence A B hA hB γ lam y0 n)
        atTop (𝓝 (0 : H)))
    (hxA : -yosidaApproximationMap B hB γ y ∈ A (resolventMap B hB γ y))
    (hxB : yosidaApproximationMap B hB γ y ∈ B (resolventMap B hB γ y))
    (hA_mono : A.IsMonotone)
    (hUniformB :
      ∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S) :
    Tendsto
      (douglasRachfordPrimalSequence A B hA hB γ lam y0)
      atTop (𝓝 (resolventMap B hB γ y)) ∧
      Tendsto
        (douglasRachfordAuxiliarySequence A B hA hB γ lam y0)
        atTop (𝓝 (resolventMap B hB γ y)) := by
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  let w_n := fun n : ℕ ↦
    (γ : ℝ)⁻¹ •
      ((2 : ℝ) • x_n n - douglasRachfordIteration A B hA hB γ lam y0 n - z_n n)
  let x : H := resolventMap B hB γ y
  let u : H := yosidaApproximationMap B hB γ y
  have hx_bounded : Bornology.IsBounded (Set.range x_n) :=
    bounded_range_of_tendsto_weakly <| by simpa [x_n, x] using hx_weak
  let S : Set H := Set.insert x (Set.range x_n)
  have hpS : x ∈ S := by
    exact Set.mem_insert x (Set.range x_n)
  have hx_memS : ∀ n, x_n n ∈ S := by
    intro n
    exact Set.mem_insert_of_mem x (Set.mem_range_self n)
  have hBx : ∀ n, u_n n ∈ B (x_n n) := by
    intro n
    simpa [x_n, u_n] using (douglasRachfordGraphData A B hA hB lam γ y0 n).1
  have hAz : ∀ n, w_n n ∈ A (z_n n) := by
    intro n
    simpa [z_n, w_n] using (douglasRachfordGraphData A B hA hB lam γ y0 n).2.1
  have hS_nonempty : S.Nonempty := ⟨x, hpS⟩
  have hS_bounded : Bornology.IsBounded S := by
    exact (Bornology.isBounded_insert (x := x) (s := Set.range x_n)).2 hx_bounded
  have hS_subB : S ⊆ B.dom := by
    intro q hq
    rcases Set.mem_insert_iff.mp hq with hq | hq
    · subst q
      exact (SetValuedOperator.mem_dom_iff B x).2 ⟨u, by simpa [u, x] using hxB⟩
    · rcases hq with ⟨n, rfl⟩
      exact (SetValuedOperator.mem_dom_iff B (x_n n)).2 ⟨u_n n, hBx n⟩
  rcases hUniformB S hS_nonempty hS_bounded hS_subB with ⟨φ, hφ⟩
  have hcomp_weak :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (u_n n + (γ : ℝ)⁻¹ • (z_n n - y)))
        atTop (𝓝 (toWeakSpace ℝ H (0 : H))) := by
    have hu_eq : u = (γ : ℝ)⁻¹ • (y - x) := by
      simp [u, x, yosidaApproximationMap_apply]
    have hz_shift :
        Tendsto
          (fun n ↦ toWeakSpace ℝ H ((γ : ℝ)⁻¹ • (z_n n - y)))
          atTop (𝓝 (toWeakSpace ℝ H ((γ : ℝ)⁻¹ • (x - y)))) := by
      have hz_sub :
          Tendsto (fun n ↦ toWeakSpace ℝ H (z_n n - y)) atTop
            (𝓝 (toWeakSpace ℝ H (x - y))) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          hz_weak.sub
            (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H y) atTop
              (𝓝 (toWeakSpace ℝ H y)))
      simpa [toWeakSpaceCLM_eq_toWeakSpace] using hz_sub.const_smul ((γ : ℝ)⁻¹)
    have hsum := hu_weak.add hz_shift
    have hsum_zero :
        Tendsto
          (fun n ↦ toWeakSpace ℝ H (u_n n + (γ : ℝ)⁻¹ • (z_n n - y)))
          atTop
          (𝓝
            (toWeakSpace ℝ H
              (u + (γ : ℝ)⁻¹ • (x - y)))) := by
      simpa [toWeakSpaceCLM_eq_toWeakSpace] using hsum
    have hu_cancel : u + (γ : ℝ)⁻¹ • (x - y) = 0 := by
      rw [hu_eq]
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    simpa [hu_cancel] using hsum_zero
  have hx_tendsto : Tendsto x_n atTop (𝓝 x) := by
    have hineq_seq :
        ∀ n,
          φ ‖x_n n - x‖₊ ≤
            (⟪x_n n - z_n n, u_n n + (γ : ℝ)⁻¹ • (z_n n - y)⟫_ℝ : EReal) := by
      intro n
      have hBineq :
          φ ‖x_n n - x‖₊ ≤ (⟪x_n n - x, u_n n - u⟫_ℝ : EReal) := by
        simpa [x_n, x, u_n, u] using hφ.ineq (hx_memS n) hpS (hBx n) (by simpa [u, x] using hxB)
      have hApair : 0 ≤ ⟪z_n n - x, w_n n - (-u)⟫_ℝ := by
        exact (SetValuedOperator.isMonotone_iff A).1 hA_mono (hAz n) (by simpa [u, x] using hxA)
      have huw_eq : u_n n + w_n n = (γ : ℝ)⁻¹ • (x_n n - z_n n) := by
        have hgraph := (douglasRachfordGraphData A B hA hB lam γ y0 n).2.2
        have hgraph_eq : (γ : ℝ) • (u_n n + w_n n) = x_n n - z_n n := by
          simpa [smul_add, add_assoc, add_left_comm, add_comm] using hgraph.symm
        calc
          u_n n + w_n n = (γ : ℝ)⁻¹ • ((γ : ℝ) • (u_n n + w_n n)) := by
            simp [smul_smul, γ.2.ne']
          _ = (γ : ℝ)⁻¹ • (x_n n - z_n n) := by
            rw [hgraph_eq]
      have hu_eq : u = (γ : ℝ)⁻¹ • (y - x) := by
        simp [u, x, yosidaApproximationMap_apply]
      have hsum_eq :
          ⟪x_n n - x, u_n n - u⟫_ℝ + ⟪z_n n - x, w_n n - (-u)⟫_ℝ =
            ⟪x_n n - z_n n, u_n n + (γ : ℝ)⁻¹ • (z_n n - y)⟫_ℝ := by
        have hsplit_left :
            x_n n - x = (x_n n - z_n n) + (z_n n - x) := by
          abel_nf
        have hcombine_right :
            ⟪z_n n - x, u_n n - u⟫_ℝ + ⟪z_n n - x, w_n n - (-u)⟫_ℝ =
              ⟪z_n n - x, u_n n + w_n n⟫_ℝ := by
          have hsum_right : (u_n n - u) + (w_n n - (-u)) = u_n n + w_n n := by
            abel_nf
          rw [← inner_add_right, hsum_right]
        have hresidual_inner :
            ⟪z_n n - x, u_n n + w_n n⟫_ℝ =
              ⟪x_n n - z_n n, (γ : ℝ)⁻¹ • (z_n n - x)⟫_ℝ := by
          rw [huw_eq]
          calc
            ⟪z_n n - x, (γ : ℝ)⁻¹ • (x_n n - z_n n)⟫_ℝ
                = (γ : ℝ)⁻¹ * ⟪z_n n - x, x_n n - z_n n⟫_ℝ := by
                  rw [real_inner_smul_right]
            _ = (γ : ℝ)⁻¹ * ⟪x_n n - z_n n, z_n n - x⟫_ℝ := by
                  rw [real_inner_comm]
            _ = ⟪x_n n - z_n n, (γ : ℝ)⁻¹ • (z_n n - x)⟫_ℝ := by
                  rw [real_inner_smul_right]
        have htmp :=
          congrArg
            (fun t : ℝ ↦ ⟪x_n n - z_n n, u_n n - u⟫_ℝ + t)
            hcombine_right
        calc
          ⟪x_n n - x, u_n n - u⟫_ℝ + ⟪z_n n - x, w_n n - (-u)⟫_ℝ
              = ⟪x_n n - z_n n, u_n n - u⟫_ℝ +
                  (⟪z_n n - x, u_n n - u⟫_ℝ + ⟪z_n n - x, w_n n - (-u)⟫_ℝ) := by
                    rw [hsplit_left, inner_add_left]
                    abel_nf
          _ = ⟪x_n n - z_n n, u_n n - u⟫_ℝ + ⟪z_n n - x, u_n n + w_n n⟫_ℝ := by
                simpa [add_assoc] using htmp
          _ = ⟪x_n n - z_n n, u_n n - u⟫_ℝ +
                ⟪x_n n - z_n n, (γ : ℝ)⁻¹ • (z_n n - x)⟫_ℝ := by
                  rw [hresidual_inner]
          _ = ⟪x_n n - z_n n, u_n n - u + (γ : ℝ)⁻¹ • (z_n n - x)⟫_ℝ := by
                rw [inner_add_right]
          _ = ⟪x_n n - z_n n, u_n n + (γ : ℝ)⁻¹ • (z_n n - y)⟫_ℝ := by
                have harg_eq :
                    u_n n - u + (γ : ℝ)⁻¹ • (z_n n - x) =
                      u_n n + (γ : ℝ)⁻¹ • (z_n n - y) := by
                  rw [hu_eq]
                  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
                rw [harg_eq]
      have hcore_le_real :
          ⟪x_n n - x, u_n n - u⟫_ℝ ≤
            ⟪x_n n - z_n n, u_n n + (γ : ℝ)⁻¹ • (z_n n - y)⟫_ℝ := by
        linarith [hApair, hsum_eq]
      have hcore_le :
          (⟪x_n n - x, u_n n - u⟫_ℝ : EReal) ≤
            (⟪x_n n - z_n n, u_n n + (γ : ℝ)⁻¹ • (z_n n - y)⟫_ℝ : EReal) := by
        exact_mod_cast hcore_le_real
      exact le_trans hBineq hcore_le
    exact tendsto_of_modulusPairing_of_tendsto_zero_of_tendsto_weakly
      hgap hcomp_weak hφ.monotone hφ.modulus_eq_zero_iff hineq_seq
  have hz_tendsto : Tendsto z_n atTop (𝓝 x) := by
    have hsum :
        Tendsto (fun n ↦ (z_n n - x_n n) + x_n n) atTop (𝓝 ((0 : H) + x)) :=
      hgap_neg.add hx_tendsto
    have hsplit : (fun n ↦ (z_n n - x_n n) + x_n n) = z_n := by
      funext n
      simp [sub_eq_add_neg, add_assoc]
    simpa [hsplit] using hsum
  exact ⟨by simpa [x_n, x] using hx_tendsto, by simpa [z_n, x] using hz_tendsto⟩

/-- Helper for Theorem 26.11: the A-branch transport reduces the two monotonicity pairings to
one residual pairing against the weakly null companion. -/
theorem aBranchResidualPairingEq
    (n : ℕ) :
    let y_n := douglasRachfordIteration A B hA hB γ lam y0
    let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
    let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
    let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
    let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
    let x : H := resolventMap B hB γ y
    let u : H := yosidaApproximationMap B hB γ y
    ⟪z_n n - x, w_n n + u⟫_ℝ + ⟪x_n n - x, u_n n - u⟫_ℝ =
      ⟪z_n n - x_n n, w_n n + (γ : ℝ)⁻¹ • (y - x_n n)⟫_ℝ := by
  let y_n := douglasRachfordIteration A B hA hB γ lam y0
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
  let x : H := resolventMap B hB γ y
  let u : H := yosidaApproximationMap B hB γ y
  have huw_eq : u_n n + w_n n = (γ : ℝ)⁻¹ • (x_n n - z_n n) := by
    -- Rewrite the summed dual residual through the scaled primal-auxiliary gap.
    simpa [x_n, u_n, z_n, y_n, w_n, add_comm] using
      (douglasRachfordScaledGap_eq_dualResidual
        (A := A) (B := B) hA hB (lam := lam) (γ := γ) (y0 := y0) (n := n)).symm
  have hu_eq : u = (γ : ℝ)⁻¹ • (y - x) := by
    -- Normalize the limit dual point to the same residual spelling as the orbit.
    simp [u, x, yosidaApproximationMap_apply]
  have hsplit_left :
      z_n n - x = (z_n n - x_n n) + (x_n n - x) := by
    abel_nf
  have hcombine_right :
      ⟪x_n n - x, w_n n + u⟫_ℝ + ⟪x_n n - x, u_n n - u⟫_ℝ =
        ⟪x_n n - x, w_n n + u_n n⟫_ℝ := by
    simp [inner_add_right, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hresidual_inner :
      ⟪x_n n - x, w_n n + u_n n⟫_ℝ =
        ⟪z_n n - x_n n, (γ : ℝ)⁻¹ • (x - x_n n)⟫_ℝ := by
    rw [add_comm, huw_eq]
    calc
      ⟪x_n n - x, (γ : ℝ)⁻¹ • (x_n n - z_n n)⟫_ℝ
          = (γ : ℝ)⁻¹ * ⟪x_n n - x, x_n n - z_n n⟫_ℝ := by
              rw [real_inner_smul_right]
      _ = (γ : ℝ)⁻¹ * ⟪x_n n - z_n n, x_n n - x⟫_ℝ := by
            rw [real_inner_comm]
      _ = ⟪x_n n - z_n n, (γ : ℝ)⁻¹ • (x_n n - x)⟫_ℝ := by
            rw [real_inner_smul_right]
      _ = ⟪z_n n - x_n n, (γ : ℝ)⁻¹ • (x - x_n n)⟫_ℝ := by
            calc
              ⟪x_n n - z_n n, (γ : ℝ)⁻¹ • (x_n n - x)⟫_ℝ
                  = -⟪x_n n - z_n n, (γ : ℝ)⁻¹ • (x - x_n n)⟫_ℝ := by
                      have hright :
                          (γ : ℝ)⁻¹ • (x_n n - x) = -((γ : ℝ)⁻¹ • (x - x_n n)) := by
                        simp [sub_eq_add_neg]
                      rw [hright, inner_neg_right]
              _ = ⟪z_n n - x_n n, (γ : ℝ)⁻¹ • (x - x_n n)⟫_ℝ := by
                    have hleft : z_n n - x_n n = -(x_n n - z_n n) := by
                      abel_nf
                    rw [hleft, inner_neg_left]
  -- Split off the `x_n - x` contribution, then rewrite it through the scaled residual.
  calc
    ⟪z_n n - x, w_n n + u⟫_ℝ + ⟪x_n n - x, u_n n - u⟫_ℝ
        = (⟪z_n n - x_n n, w_n n + u⟫_ℝ + ⟪x_n n - x, w_n n + u⟫_ℝ) +
            ⟪x_n n - x, u_n n - u⟫_ℝ := by
              rw [hsplit_left, inner_add_left]
    _ = ⟪z_n n - x_n n, w_n n + u⟫_ℝ +
        (⟪x_n n - x, w_n n + u⟫_ℝ + ⟪x_n n - x, u_n n - u⟫_ℝ) := by
          abel_nf
    _ = ⟪z_n n - x_n n, w_n n + u⟫_ℝ + ⟪x_n n - x, w_n n + u_n n⟫_ℝ := by
          rw [hcombine_right]
    _ = ⟪z_n n - x_n n, w_n n + u⟫_ℝ +
          ⟪z_n n - x_n n, (γ : ℝ)⁻¹ • (x - x_n n)⟫_ℝ := by
            rw [hresidual_inner]
    _ = ⟪z_n n - x_n n, w_n n + u + (γ : ℝ)⁻¹ • (x - x_n n)⟫_ℝ := by
          simp [inner_add_right, add_assoc]
    _ = ⟪z_n n - x_n n, w_n n + (γ : ℝ)⁻¹ • (y - x_n n)⟫_ℝ := by
          have harg_eq :
              w_n n + u + (γ : ℝ)⁻¹ • (x - x_n n) =
                w_n n + (γ : ℝ)⁻¹ • (y - x_n n) := by
            rw [hu_eq]
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          rw [harg_eq]

/-- Clause (7) of Theorem 26.11: if, in addition, `A` or `B` is uniformly monotone on every
nonempty bounded subset of its domain, then both `xₙ` and `zₙ` converge strongly to
`J_{γ B} y`. -/
theorem douglasRachfordAlgorithm_primal_auxiliary_tendsto_of_uniformlyMonotoneOnEveryBoundedSubset
    (hzero : (primal_inclusion_solution_set A B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hy_fix : y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ))
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y)))
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ A.dom → A.IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S) :
    Tendsto
      (douglasRachfordPrimalSequence A B hA hB γ lam y0)
      atTop (𝓝 (resolventMap B hB γ y)) ∧
      Tendsto
        (douglasRachfordAuxiliarySequence A B hA hB γ lam y0)
        atTop (𝓝 (resolventMap B hB γ y)) :=
by
  let y_n := douglasRachfordIteration A B hA hB γ lam y0
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  let w_n := fun n : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n n - y_n n - z_n n)
  let x : H := resolventMap B hB γ y
  let u : H := yosidaApproximationMap B hB γ y
  have hxz_weak :=
    douglasRachfordAlgorithm_primal_auxiliary_tendsto_weakly
      (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
      (hdiv := hdiv) (γ := γ) (y0 := y0) (hy_fix := hy_fix) (hy_tendsto := hy_tendsto)
  have hx_weak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (x_n n)) atTop (𝓝 (toWeakSpace ℝ H x)) := by
    simpa [x_n, x] using hxz_weak.1
  have hz_weak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (z_n n)) atTop (𝓝 (toWeakSpace ℝ H x)) := by
    simpa [z_n, x] using hxz_weak.2
  have hu_weak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (u_n n)) atTop (𝓝 (toWeakSpace ℝ H u)) := by
    simpa [u_n, u] using
      douglasRachfordAlgorithm_dual_tendsto_weakly
        (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
        (hdiv := hdiv) (γ := γ) (y0 := y0) (hy_fix := hy_fix) (hy_tendsto := hy_tendsto)
  have hgap :
      Tendsto (fun n ↦ x_n n - z_n n) atTop (𝓝 (0 : H)) := by
    simpa [x_n, z_n] using
      douglasRachfordAlgorithm_primal_auxiliary_gap_tendsto_zero
        (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
        (hdiv := hdiv) (γ := γ) (y0 := y0)
  have hgap_neg :
      Tendsto (fun n ↦ z_n n - x_n n) atTop (𝓝 (0 : H)) := by
    -- The source A-branch uses the reversed residual `zₙ - xₙ`.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hgap.neg
  have hlimitGraph := douglasRachfordLimitGraphData A B hA hB γ hy_fix
  have hxA : -u ∈ A x := by
    simpa [x, u] using hlimitGraph.1
  have hxB : u ∈ B x := by
    simpa [x, u] using hlimitGraph.2
  have hA_mono : A.IsMonotone := SetValuedOperator.Maximal.isMonotone hA
  have hB_mono : B.IsMonotone := SetValuedOperator.Maximal.isMonotone hB
  rcases hUniform with hUniformA | hUniformB
  · have hz_bounded : Bornology.IsBounded (Set.range z_n) :=
      bounded_range_of_tendsto_weakly hz_weak
    let S : Set H := Set.insert x (Set.range z_n)
    have hpS : x ∈ S := by
      exact Set.mem_insert x (Set.range z_n)
    have hz_memS : ∀ n, z_n n ∈ S := by
      intro n
      exact Set.mem_insert_of_mem x (Set.mem_range_self n)
    have hS_nonempty : S.Nonempty := ⟨x, hpS⟩
    have hS_bounded : Bornology.IsBounded S := by
      exact (Bornology.isBounded_insert (x := x) (s := Set.range z_n)).2 hz_bounded
    have hAz : ∀ n, w_n n ∈ A (z_n n) := by
      intro n
      simpa [z_n, w_n] using (douglasRachfordGraphData A B hA hB lam γ y0 n).2.1
    have hBx : ∀ n, u_n n ∈ B (x_n n) := by
      intro n
      simpa [x_n, u_n] using (douglasRachfordGraphData A B hA hB lam γ y0 n).1
    have hS_subA : S ⊆ A.dom := by
      intro q hq
      rcases Set.mem_insert_iff.mp hq with hq | hq
      · subst q
        exact (SetValuedOperator.mem_dom_iff A x).2 ⟨-u, hxA⟩
      · rcases hq with ⟨n, rfl⟩
        exact (SetValuedOperator.mem_dom_iff A (z_n n)).2 ⟨w_n n, hAz n⟩
    rcases hUniformA S hS_nonempty hS_bounded hS_subA with ⟨φ, hφ⟩
    have hcomp_weak :
        Tendsto
          (fun n ↦ toWeakSpace ℝ H (w_n n + (γ : ℝ)⁻¹ • (y - x_n n)))
          atTop (𝓝 (toWeakSpace ℝ H (0 : H))) := by
      have hraw :
          Tendsto
            (fun n ↦ toWeakSpace ℝ H (x_n n - y_n n - z_n n + y))
            atTop (𝓝 (toWeakSpace ℝ H (0 : H))) := by
        -- Normalize the companion term to a weakly null combination of the clause-(3) limits.
        simpa [x, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          ((hx_weak.sub hy_tendsto).sub hz_weak).add
            (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H y) atTop
              (𝓝 (toWeakSpace ℝ H y)))
      simpa [w_n, x_n, y_n, z_n, sub_eq_add_neg, smul_sub, smul_add, smul_smul, two_smul,
        add_assoc, add_left_comm, add_comm] using hraw.const_smul ((γ : ℝ)⁻¹)
    have hz_tendsto : Tendsto z_n atTop (𝓝 x) := by
      have hineq_seq :
          ∀ n,
            φ ‖z_n n - x‖₊ ≤
              (⟪z_n n - x_n n, w_n n + (γ : ℝ)⁻¹ • (y - x_n n)⟫_ℝ : EReal) := by
        intro n
        have hAineq :
            φ ‖z_n n - x‖₊ ≤ (⟪z_n n - x, w_n n + u⟫_ℝ : EReal) := by
          -- Apply the localized A-modulus to `(zₙ, wₙ)` and the limit graph point `(x, -u)`.
          simpa [sub_eq_add_neg] using hφ.ineq (hz_memS n) hpS (hAz n) hxA
        have hBpair : 0 ≤ ⟪x_n n - x, u_n n - u⟫_ℝ := by
          exact (SetValuedOperator.isMonotone_iff B).1 hB_mono (hBx n) hxB
        have hsum_eq :
            ⟪z_n n - x, w_n n + u⟫_ℝ + ⟪x_n n - x, u_n n - u⟫_ℝ =
              ⟪z_n n - x_n n, w_n n + (γ : ℝ)⁻¹ • (y - x_n n)⟫_ℝ := by
          -- Route correction: use the dedicated A-branch pairing rewrite instead of repeating
          -- the full residual transport inline.
          simpa [y_n, x_n, u_n, z_n, w_n, x, u] using
            (aBranchResidualPairingEq
              (A := A) (B := B) hA hB (lam := lam) (γ := γ) (y0 := y0) (y := y) (n := n))
        have hcore_le_real :
            ⟪z_n n - x, w_n n + u⟫_ℝ ≤
              ⟪z_n n - x_n n, w_n n + (γ : ℝ)⁻¹ • (y - x_n n)⟫_ℝ := by
          linarith [hBpair, hsum_eq]
        have hcore_le :
            (⟪z_n n - x, w_n n + u⟫_ℝ : EReal) ≤
              (⟪z_n n - x_n n, w_n n + (γ : ℝ)⁻¹ • (y - x_n n)⟫_ℝ : EReal) := by
          exact_mod_cast hcore_le_real
        exact le_trans hAineq hcore_le
      -- The A-branch closes once the residual is strong-null and the companion is weak-null.
      exact tendsto_of_modulusPairing_of_tendsto_zero_of_tendsto_weakly
        hgap_neg hcomp_weak hφ.monotone hφ.modulus_eq_zero_iff hineq_seq
    have hx_tendsto : Tendsto x_n atTop (𝓝 x) := by
      -- Recover the primal limit from the strong gap `xₙ - zₙ → 0`.
      have hsum :
          Tendsto (fun n ↦ (x_n n - z_n n) + z_n n) atTop (𝓝 ((0 : H) + x)) :=
        hgap.add hz_tendsto
      have hsplit : (fun n ↦ (x_n n - z_n n) + z_n n) = x_n := by
        funext n
        abel_nf
      simpa [hsplit] using hsum
    exact ⟨by simpa [x_n, x] using hx_tendsto, by simpa [z_n, x] using hz_tendsto⟩
  · exact
      douglasRachfordAlgorithm_primal_auxiliary_tendsto_of_uniformlyMonotoneBOnEveryBoundedSubset
        (A := A) (B := B) hA hB (lam := lam) (γ := γ) (y0 := y0) (y := y)
        hx_weak hz_weak hu_weak
        (by simpa [x_n, z_n] using hgap)
        (by simpa [z_n, x_n] using hgap_neg)
        (by simpa [u, x] using hxA)
        (by simpa [u, x] using hxB)
        hA_mono hUniformB

/-- Companion projection for clause (7) of Theorem 26.11: under the same uniform-monotonicity
hypothesis, `xₙ` converges strongly to `J_{γ B} y`. -/
theorem douglasRachfordAlgorithm_primal_tendsto_of_uniformlyMonotoneOnEveryBoundedSubset
    (hzero : (primal_inclusion_solution_set A B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hy_fix : y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ))
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y)))
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ A.dom → A.IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S) :
    Tendsto
      (douglasRachfordPrimalSequence A B hA hB γ lam y0)
      atTop (𝓝 (resolventMap B hB γ y)) :=
  (douglasRachfordAlgorithm_primal_auxiliary_tendsto_of_uniformlyMonotoneOnEveryBoundedSubset
    (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
    (hdiv := hdiv) (γ := γ) (y0 := y0) (hy_fix := hy_fix) (hy_tendsto := hy_tendsto)
    (hUniform := hUniform)).1

/-- Companion projection for clause (7) of Theorem 26.11: under the same uniform-monotonicity
hypothesis, `zₙ` converges strongly to `J_{γ B} y`. -/
theorem douglasRachfordAlgorithm_auxiliary_tendsto_of_uniformlyMonotoneOnEveryBoundedSubset
    (hzero : (primal_inclusion_solution_set A B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hy_fix : y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ))
    (hy_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y)))
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ A.dom → A.IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S) :
    Tendsto
      (douglasRachfordAuxiliarySequence A B hA hB γ lam y0)
      atTop (𝓝 (resolventMap B hB γ y)) :=
  (douglasRachfordAlgorithm_primal_auxiliary_tendsto_of_uniformlyMonotoneOnEveryBoundedSubset
    (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
    (hdiv := hdiv) (γ := γ) (y0 := y0) (hy_fix := hy_fix) (hy_tendsto := hy_tendsto)
    (hUniform := hUniform)).2

end UniformMonotoneConsequences

end

end SetValuedOperator
