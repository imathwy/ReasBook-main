import BauschkeLean.Chap02.Lemma_2_46
import BauschkeLean.Chap02.Lemma_2_51
import BauschkeLean.Chap03.Corollary_3_22
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_1
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap15.Definition_15_19
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap19.Theorem_19_1
import BauschkeLean.Chap22.Example_22_5
import BauschkeLean.Chap23.Definition_23_1
import BauschkeLean.Chap23.Proposition_23_2
import BauschkeLean.Chap23.ResolventRealizer
import BauschkeLean.Chap26.Proposition_26_1
import BauschkeLean.Chap26.Proposition_26_5
import BauschkeLean.Chap04.Corollary_4_28
import BauschkeLean.Chap04.Proposition_4_19
import BauschkeLean.Chap05.Corollary_5_17
import BauschkeLean.Chap06.Example_6_43
import BauschkeLean.Chap20.Example_20_26
import BauschkeLean.Chap22.Remark_22_3

open Function
open Filter
open ERealFunction
open SetValuedOperator
open scoped InnerProductSpace Pointwise Set SetValuedOperator Topology

noncomputable section

universe u

namespace SetValuedOperator

section LocalDouglasRachfordOwner

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Corollary 28.3: the relaxed Douglas--Rachford `y`-orbit from `(26.29)`. -/
def douglasRachfordIteration
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  relaxedOperatorIteration
    (fun _ ↦ douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ))
    lam y0

/-- Helper for Corollary 28.3: the shadow sequence `xₙ = J_{γ B} yₙ`. -/
def douglasRachfordPrimalSequence
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  fun n ↦ resolventMap B hB γ (douglasRachfordIteration A B hA hB γ lam y0 n)

/-- Helper for Corollary 28.3: the dual sequence `uₙ = {}^[γ] B yₙ`. -/
def douglasRachfordDualSequence
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  fun n ↦ yosidaApproximationMap B hB γ (douglasRachfordIteration A B hA hB γ lam y0 n)

/-- Helper for Corollary 28.3: the auxiliary sequence `zₙ = J_{γ A}(2xₙ - yₙ)`. -/
def douglasRachfordAuxiliarySequence
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  fun n ↦
    resolventMap A hA γ
      ((2 : ℝ) • douglasRachfordPrimalSequence A B hA hB γ lam y0 n -
        douglasRachfordIteration A B hA hB γ lam y0 n)

section FixedPointConsequences

variable (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
variable (γ : PosReal) {y : H}

/-- Helper for Corollary 28.3: the fixed-point limit produces canonical primal and dual
inclusion solutions. -/
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

/-- Helper for Corollary 28.3: a fixed point `y` determines the canonical graph witnesses
`(x, -u) ∈ gra A` and `(x, u) ∈ gra B`. -/
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

section RemainingOwners

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

/-- Helper for Corollary 28.3: the Douglas--Rachford residual `T yₙ - yₙ` is exactly the
auxiliary-minus-primal gap `zₙ - xₙ`. -/
theorem douglasRachfordResidual_eq_auxiliary_sub_primal
    (n : ℕ) :
    douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ)
        (douglasRachfordIteration A B hA hB γ lam y0 n) -
      douglasRachfordIteration A B hA hB γ lam y0 n =
        douglasRachfordAuxiliarySequence A B hA hB γ lam y0 n -
          douglasRachfordPrimalSequence A B hA hB γ lam y0 n := by
  -- Expand the Douglas--Rachford operator once and cancel the orbit term appearing with both
  -- signs.
  simp only [douglasRachfordPrimalSequence, douglasRachfordAuxiliarySequence]
  rw [douglasRachfordOperator_apply]
  abel_nf

/-- Helper for Corollary 28.3: a nonempty primal solution set yields a nonempty Douglas--Rachford
fixed-point set. -/
theorem douglasRachfordFixedPointsNonempty
    (hzero : (primal_inclusion_solution_set A B).Nonempty) :
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

section

omit [CompleteSpace H]

/-- Helper for Corollary 28.3: subtracting a strongly null residual preserves the weak limit of a
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

end

section

omit [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Corollary 28.3: a localized modulus forced below `0` identifies the two points. -/
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

end

/-- Helper for Corollary 28.3: the Douglas--Rachford iterates produce the graph data
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

/-- Helper for Corollary 28.3: scaling the primal-auxiliary gap by `γ⁻¹` gives the summed dual
residual `uₙ + wₙ`. -/
theorem douglasRachfordScaledGap_eq_dualResidual
    (n : ℕ) :
    let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
    let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
    let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
    let w_n := fun k : ℕ ↦
      (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - douglasRachfordIteration A B hA hB γ lam y0 k - z_n k)
    (γ : ℝ)⁻¹ • (x_n n - z_n n) = u_n n + w_n n := by
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
  let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
  let w_n := fun k : ℕ ↦
    (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - douglasRachfordIteration A B hA hB γ lam y0 k - z_n k)
  have hgraph := (douglasRachfordGraphData A B hA hB lam γ y0 n).2.2
  have hscaled :
      (γ : ℝ)⁻¹ • (x_n n - z_n n) = (γ : ℝ)⁻¹ • ((γ : ℝ) • (u_n n + w_n n)) := by
    -- Rewrite the primal-auxiliary gap using the canonical graph residual identity.
    rw [show x_n n - z_n n = (γ : ℝ) • (u_n n + w_n n) by
      simpa [x_n, u_n, z_n, w_n] using hgraph]
  calc
    (γ : ℝ)⁻¹ • (x_n n - z_n n) = (γ : ℝ)⁻¹ • ((γ : ℝ) • (u_n n + w_n n)) := hscaled
    _ = u_n n + w_n n := by
      simp [smul_smul, γ.2.ne']

section

omit [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Corollary 28.3: a firmly nonexpansive self-map on the whole space is
`1`-Lipschitz. -/
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

end

/-- Helper for Corollary 28.3: the weakly convergent Douglas--Rachford orbit has a bounded primal
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
  have hLip : LipschitzWith 1 (resolventMap B hB γ) := by
    -- Repackage whole-space firm nonexpansiveness as a `1`-Lipschitz estimate.
    exact
      lipschitzWith_one_of_firmlyNonexpansiveOn_univ <| by
        simpa [FirmlyNonexpansive] using resolventMap_firmlyNonexpansiveOn_univ B hB γ
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

/-- Helper for Corollary 28.3: the primal-auxiliary gap is already strongly null before the weak
cluster-point closure arguments begin. -/
theorem douglasRachfordPrimalAuxiliaryGapTendstoZeroCore
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
        douglasRachfordResidual_eq_auxiliary_sub_primal
          A B hA hB lam γ y0 n
    -- Proposition 5.16 gives asymptotic regularity of the Douglas-Rachford residual.
    rwa [hresidual_eq] at hbase
  -- Negate the residual limit to match the source orientation `xₙ - zₙ`.
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hresidual.neg

/-- Helper for Corollary 28.3: along a weakly convergent primal subsequence, the auxiliary
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
      douglasRachfordPrimalAuxiliaryGapTendstoZeroCore
        (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
        (hdiv := hdiv) (γ := γ) (y0 := y0)
  have hgap_sub :
      Tendsto (fun n ↦ x_n (φ n) - z_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- Restrict the strong gap to the extracted subsequence.
    simpa [Function.comp, x_n, z_n] using hgap.comp hφmono.tendsto_atTop
  -- Route correction: transport the weak limit through the small residual bridge first.
  exact tendstoWeaklyOfSubTendstoZeroSeq hφx hgap_sub

/-- Helper for Corollary 28.3: along a primal cluster subsequence, the dual sequence converges
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
    -- Restrict the weak limit of the Douglas-Rachford orbit to the chosen subsequence.
    simpa [y_n, Function.comp] using hy_tendsto.comp hφmono.tendsto_atTop
  have hdiff :=
    (hy_subseq.sub hφx).const_smul ((γ : ℝ)⁻¹)
  -- Normalize the dual subsequence through `u_n = γ⁻¹ • (y_n - x_n)`.
  simpa [u_n, y_n, x_n, douglasRachfordDualSequence, yosidaApproximationMap_apply,
    Function.comp, smul_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdiff

/-- Helper for Corollary 28.3: along a primal cluster subsequence, the dual residual
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
  have hgraph := (douglasRachfordGraphData A B hA hB lam γ y0 (φ n)).2.2
  calc
    (γ : ℝ)⁻¹ • (x_n (φ n) - z_n (φ n))
        = (γ : ℝ)⁻¹ • ((γ : ℝ) • (u_n (φ n) + w_n (φ n))) := by
            -- Rewrite the scaled gap through the packaged graph residual identity.
            rw [show x_n (φ n) - z_n (φ n) = (γ : ℝ) • (u_n (φ n) + w_n (φ n)) by
              simpa [x_n, u_n, z_n, w_n] using hgraph]
    _ = u_n (φ n) + w_n (φ n) := by
          -- Cancel the positive scalar `γ` against its inverse.
          simp [smul_smul, γ.2.ne']
    _ = w_n (φ n) + u_n (φ n) := by
          -- Put the residual in the Proposition 26.5 summand order.
          abel_nf

/-- Helper for Corollary 28.3: along a primal cluster subsequence, the dual residual
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
      douglasRachfordPrimalAuxiliaryGapTendstoZeroCore
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
    -- Route correction: consume the pointwise normalization once, then reuse it by rewriting.
    simpa [x_n, u_n, z_n, y_n, w_n] using
      douglasRachfordDualResidualSubsequence_eq
        (A := A) (B := B) hA hB (lam := lam) (γ := γ) (y0 := y0) (φ := φ) n
  rw [← hscaled_eq]
  exact hscaled

/-- Helper for Corollary 28.3: the `A`-graph witnesses persist along any extracted subsequence. -/
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
  -- Read the `A`-graph point directly from the packaged Douglas-Rachford graph data.
  simpa [z_n, w_n] using (douglasRachfordGraphData A B hA hB lam γ y0 (φ n)).2.1

/-- Helper for Corollary 28.3: the `B`-graph witnesses persist along any extracted subsequence. -/
theorem douglasRachfordPrimalGraphSubsequence_mem
    {φ : ℕ → ℕ} :
    ∀ n,
      let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
      let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
      (x_n (φ n), u_n (φ n)) ∈ gra B := by
  intro n
  let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
  let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
  -- Read the `B`-graph point directly from the packaged Douglas-Rachford graph data.
  simpa [x_n, u_n] using (douglasRachfordGraphData A B hA hB lam γ y0 (φ n)).1

/-- Helper for Corollary 28.3: along any extracted subsequence, the residual in the
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
      douglasRachfordPrimalAuxiliaryGapTendstoZeroCore
        (A := A) (B := B) hA hB (hzero := hzero) (lam := lam) (hlam := hlam)
        (hdiv := hdiv) (γ := γ) (y0 := y0)
  have hgap_sub :
      Tendsto (fun n ↦ x_n (φ n) - z_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- Restrict the strong gap to the extracted subsequence.
    simpa [Function.comp, x_n, z_n] using hgap.comp hφmono.tendsto_atTop
  -- Proposition 26.5 uses the residual in the `z_n - x_n` orientation.
  simpa [x_n, z_n, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hgap_sub.neg

/-- Helper for Corollary 28.3: the `L = id` specialization of Proposition 26.5 closes the
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
    -- Normalize the dual residual to the exact coupled Proposition 26.5 interface.
    simpa [ContinuousLinearMap.adjoint_id] using huv
  -- Route correction: freeze the identity-map specialization once so the Douglas--Rachford
  -- closure theorem only passes explicit subsequence data to Proposition 26.5.
  simpa [ContinuousLinearMap.id_apply, ContinuousLinearMap.adjoint_id] using
    (mem_graph_B_of_weak_primal_dual_residual_zero
      (L := ContinuousLinearMap.id ℝ H)
      (xSeq := xSeq)
      (uSeq := uSeq)
      (ySeq := ySeq)
      (vSeq := vSeq)
      (x := x)
      (v := v)
      hA hB hxu hyv hx hv hxy huv_id)

/-- Corollary 28.3: once the subsequence weak limits, graph memberships, and residual limits are
prepared, Proposition 26.5 closes the `B`-graph limit. -/
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
  -- Route correction: the closing step now goes through the frozen `L = id` bridge, so this
  -- theorem only supplies the subsequence weak limits, graph data, and residual limits.
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

/-- Helper for Corollary 28.3: weak Douglas--Rachford convergence to a fixed point. -/
theorem weakClusterPoint_mem_graphBLimit
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
    -- Reuse the standalone `A`-branch graph helper to refresh the elaboration budget.
    simpa [z_n, w_n] using
      (douglasRachfordAuxiliaryGraphSubsequence_mem
        (A := A) (B := B) hA hB (lam := lam) (γ := γ) (y0 := y0) (φ := φ))
  have hgraphB :
      ∀ n, (x_n (φ n), u_n (φ n)) ∈ gra B := by
    -- Reuse the standalone `B`-branch graph helper to refresh the elaboration budget.
    simpa [x_n, u_n] using
      (douglasRachfordPrimalGraphSubsequence_mem
        (A := A) (B := B) hA hB (lam := lam) (γ := γ) (y0 := y0) (φ := φ))
  have hresidual :
      Tendsto (fun n ↦ z_n (φ n) - x_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- Reuse the standalone residual helper to keep the final specialization transport-light.
    simpa [x_n, z_n] using
      douglasRachfordAuxiliaryMinusPrimalSubsequence_tendsto_zero
        (A := A) (B := B) hA hB (lam := lam) hzero hlam hdiv
        (γ := γ) (y0 := y0) (φ := φ) hφmono
  have hdualResidual :
      Tendsto (fun n ↦ w_n (φ n) + u_n (φ n)) atTop (𝓝 (0 : H)) := by
    -- Close the last transport bridge with the normalized residual identity.
    simpa [w_n, u_n, x_n, y_n, z_n] using
      douglasRachfordDualResidualSubsequence_tendsto_zero
        (A := A) (B := B) hA hB (lam := lam) hzero hlam hdiv
        (γ := γ) (y0 := y0) (φ := φ) hφmono
  -- Route correction: reduce the main theorem to the fixed-subsequence graph-limit helper.
  exact
    weakClusterPoint_mem_graphBLimit_of_subsequence
      (A := A) (B := B) hA hB (lam := lam) (γ := γ) (y0 := y0) (y := y) (z := z) (φ := φ)
      hz_subseq hu_subseq hgraphA hgraphB hresidual hdualResidual

/-- Helper for Corollary 28.3: every weak cluster point of the primal sequence is the resolvent
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

/-- Helper for Corollary 28.3: weak Douglas--Rachford convergence to a fixed point. -/
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
    rw [← fixedPoints_douglasRachfordOperator_resolvent_eq_fixedPoints_reflectedResolventComposition
      A B hA hB γ]
    exact hy
  · -- The named Douglas-Rachford orbit is the constant relaxed iteration of `T`.
    simpa [douglasRachfordIteration, T] using hy_tendsto

/-- Helper for Corollary 28.3: the primal-auxiliary gap converges strongly to `0`. -/
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
        douglasRachfordResidual_eq_auxiliary_sub_primal
          A B hA hB lam γ y0 n
    -- Proposition 5.16 gives asymptotic regularity of the Douglas-Rachford residual.
    rwa [hresidual_eq] at hbase
  -- Negate the residual limit to match the source orientation `xₙ - zₙ`.
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hresidual.neg

/-- Helper for Corollary 28.3: the primal and auxiliary sequences converge weakly to the
resolvent limit. -/
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

/-- Helper for Corollary 28.3: the dual sequence converges weakly to the Yosida limit. -/
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

/-- Helper for Corollary 28.3: under the localized uniform-monotonicity branch, every primal
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
        have hpair_nonneg : 0 ≤ -⟪q - x, uq - u⟫_ℝ := by
          have hpairA : 0 ≤ ⟪q - x, (-uq) - (-u)⟫_ℝ := hA_mono hqA hxA
          have hneg_eq : ⟪q - x, (-uq) - (-u)⟫_ℝ = -⟪q - x, uq - u⟫_ℝ := by
            have hterm : (-uq) - (-u) = -(uq - u) := by
              abel_nf
            rw [hterm, inner_neg_right]
          rwa [hneg_eq] at hpairA
        linarith
      have hupper : (⟪q - x, uq - u⟫_ℝ : EReal) ≤ 0 := by
        exact_mod_cast hupper_real
      exact le_trans hBineq hupper
    exact eq_of_modulus_le_zero hφ.monotone hφ.modulus_eq_zero_iff hineq

namespace DouglasRachfordAlgorithm
/-- Helper for Corollary 28.3: uniform monotonicity forces uniqueness of the primal solution. -/
theorem unique_primal_solution_of_uniformlyMonotoneOnEveryBoundedSubset
    {y : H}
    (hy_fix : y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ))
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ A.dom → A.IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ B.dom → B.IsUniformlyMonotoneOn S) :
    primal_inclusion_solution_set A B = {resolventMap B hB γ y} := by
  ext q
  constructor
  · intro hq
    -- Localize the uniform monotonicity branch to the two-point set `{q, J_{γ B} y}`.
    exact Set.mem_singleton_iff.mpr <|
      primalSolution_eq_resolventLimit_of_uniformBranch
        A B hA hB γ hy_fix hUniform hq
  · intro hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    -- The fixed-point resolvent image is always a primal inclusion solution.
    exact (douglasRachfordAlgorithm_limit_primal_dual_solution A B hA hB γ hy_fix).1

/-- Helper for Corollary 28.3: if a localized modulus is controlled by pairings of a strongly
null residual and a weakly null companion, then the base sequence converges strongly. -/
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

/-- Helper for Corollary 28.3: the A-branch transport reduces the two monotonicity pairings to
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

/-- Helper for Corollary 28.3: the B-branch transport reduces the two monotonicity pairings to
one residual pairing against the weakly null companion. -/
theorem bBranchResidualPairingEq
    (n : ℕ) :
    let y_n := douglasRachfordIteration A B hA hB γ lam y0
    let x_n := douglasRachfordPrimalSequence A B hA hB γ lam y0
    let u_n := douglasRachfordDualSequence A B hA hB γ lam y0
    let z_n := douglasRachfordAuxiliarySequence A B hA hB γ lam y0
    let w_n := fun k : ℕ ↦ (γ : ℝ)⁻¹ • ((2 : ℝ) • x_n k - y_n k - z_n k)
    let x : H := resolventMap B hB γ y
    let u : H := yosidaApproximationMap B hB γ y
    ⟪x_n n - x, u_n n - u⟫_ℝ + ⟪z_n n - x, w_n n - (-u)⟫_ℝ =
      ⟪x_n n - z_n n, u_n n + (γ : ℝ)⁻¹ • (z_n n - y)⟫_ℝ := by
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
      x_n n - x = (x_n n - z_n n) + (z_n n - x) := by
    abel_nf
  have hcombine_right :
      ⟪z_n n - x, u_n n - u⟫_ℝ + ⟪z_n n - x, w_n n - (-u)⟫_ℝ =
        ⟪z_n n - x, u_n n + w_n n⟫_ℝ := by
    have harg : (u_n n - u) + (w_n n - (-u)) = u_n n + w_n n := by
      abel_nf
    calc
      ⟪z_n n - x, u_n n - u⟫_ℝ + ⟪z_n n - x, w_n n - (-u)⟫_ℝ
          = ⟪z_n n - x, (u_n n - u) + (w_n n - (-u))⟫_ℝ := by
              rw [← inner_add_right]
      _ = ⟪z_n n - x, u_n n + w_n n⟫_ℝ := by
            rw [harg]
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
  -- Split off the `z_n - x` contribution, then rewrite it through the scaled residual.
  calc
    ⟪x_n n - x, u_n n - u⟫_ℝ + ⟪z_n n - x, w_n n - (-u)⟫_ℝ
        = ⟪x_n n - z_n n, u_n n - u⟫_ℝ +
            (⟪z_n n - x, u_n n - u⟫_ℝ + ⟪z_n n - x, w_n n - (-u)⟫_ℝ) := by
              rw [hsplit_left, inner_add_left]
              abel_nf
    _ = ⟪x_n n - z_n n, u_n n - u⟫_ℝ + ⟪z_n n - x, u_n n + w_n n⟫_ℝ := by
          rw [hcombine_right]
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

/-- Helper for Corollary 28.3: under uniform monotonicity, the primal and auxiliary sequences
converge strongly to the resolvent limit. -/
theorem primal_auxiliary_tendsto_of_uniformlyMonotoneOnEveryBoundedSubset
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
        atTop (𝓝 (resolventMap B hB γ y)) := by
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
    -- The A-branch uses the reversed residual `zₙ - xₙ`.
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
        -- Normalize the companion term to a weakly null combination of the orbit, primal, and
        -- auxiliary weak limits.
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
          -- Apply the localized A-modulus to `(zₙ, wₙ)` and the limiting graph point `(x, -u)`.
          simpa [sub_eq_add_neg] using hφ.ineq (hz_memS n) hpS (hAz n) hxA
        have hBpair : 0 ≤ ⟪x_n n - x, u_n n - u⟫_ℝ := by
          exact (SetValuedOperator.isMonotone_iff B).1 hB_mono (hBx n) hxB
        have hsum_eq :
            ⟪z_n n - x, w_n n + u⟫_ℝ + ⟪x_n n - x, u_n n - u⟫_ℝ =
              ⟪z_n n - x_n n, w_n n + (γ : ℝ)⁻¹ • (y - x_n n)⟫_ℝ := by
          -- Use the named branch transport instead of redoing the long residual normalization.
          simpa [y_n, x_n, u_n, z_n, w_n, x, u] using
            aBranchResidualPairingEq
              (A := A) (B := B) hA hB (γ := γ) (lam := lam) (y0 := y0) (y := y) n
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
  · have hx_bounded : Bornology.IsBounded (Set.range x_n) :=
      bounded_range_of_tendsto_weakly hx_weak
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
        exact (SetValuedOperator.mem_dom_iff B x).2 ⟨u, hxB⟩
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
            (fun n ↦ (toWeakSpace ℝ H) (u_n n) +
              ((γ : ℝ)⁻¹) • ((toWeakSpace ℝ H) (z_n n) - (toWeakSpace ℝ H) y))
            atTop
              (𝓝 ((toWeakSpace ℝ H) u +
                ((γ : ℝ)⁻¹) • ((toWeakSpace ℝ H) x - (toWeakSpace ℝ H) y))) := by
        simpa [toWeakSpaceCLM_eq_toWeakSpace] using hsum
      have hu_cancel : u + (γ : ℝ)⁻¹ • (x - y) = 0 := by
        rw [hu_eq]
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      have hu_cancel_weak :
          (toWeakSpace ℝ H) u + ((γ : ℝ)⁻¹) • ((toWeakSpace ℝ H) x - (toWeakSpace ℝ H) y) =
            toWeakSpace ℝ H (0 : H) := by
        simpa [toWeakSpaceCLM_eq_toWeakSpace, hu_cancel]
      simpa [hu_cancel_weak] using hsum_zero
    have hx_tendsto : Tendsto x_n atTop (𝓝 x) := by
      have hineq_seq :
          ∀ n,
            φ ‖x_n n - x‖₊ ≤
              (⟪x_n n - z_n n, u_n n + (γ : ℝ)⁻¹ • (z_n n - y)⟫_ℝ : EReal) := by
        intro n
        have hBineq :
            φ ‖x_n n - x‖₊ ≤ (⟪x_n n - x, u_n n - u⟫_ℝ : EReal) := by
          -- Apply the localized B-modulus to `(xₙ, uₙ)` and the limiting graph point `(x, u)`.
          simpa [x_n, x, u_n, u] using hφ.ineq (hx_memS n) hpS (hBx n) hxB
        have hApair : 0 ≤ ⟪z_n n - x, w_n n - (-u)⟫_ℝ := by
          exact (SetValuedOperator.isMonotone_iff A).1 hA_mono (hAz n) hxA
        have hsum_eq :
            ⟪x_n n - x, u_n n - u⟫_ℝ + ⟪z_n n - x, w_n n - (-u)⟫_ℝ =
              ⟪x_n n - z_n n, u_n n + (γ : ℝ)⁻¹ • (z_n n - y)⟫_ℝ := by
          -- Use the named symmetric branch transport instead of redoing the normalization.
          simpa [y_n, x_n, u_n, z_n, w_n, x, u] using
            bBranchResidualPairingEq
              (A := A) (B := B) hA hB (γ := γ) (lam := lam) (y0 := y0) (y := y) n
        have hcore_le_real :
            ⟪x_n n - x, u_n n - u⟫_ℝ ≤
              ⟪x_n n - z_n n, u_n n + (γ : ℝ)⁻¹ • (z_n n - y)⟫_ℝ := by
          linarith [hApair, hsum_eq]
        have hcore_le :
            (⟪x_n n - x, u_n n - u⟫_ℝ : EReal) ≤
              (⟪x_n n - z_n n, u_n n + (γ : ℝ)⁻¹ • (z_n n - y)⟫_ℝ : EReal) := by
          exact_mod_cast hcore_le_real
        exact le_trans hBineq hcore_le
      -- The B-branch is the symmetric modulus-pairing argument on the primal orbit.
      exact tendsto_of_modulusPairing_of_tendsto_zero_of_tendsto_weakly
        hgap hcomp_weak hφ.monotone hφ.modulus_eq_zero_iff hineq_seq
    have hz_tendsto : Tendsto z_n atTop (𝓝 x) := by
      -- Recover the auxiliary limit from the strong gap `zₙ - xₙ → 0`.
      have hsum :
          Tendsto (fun n ↦ (z_n n - x_n n) + x_n n) atTop (𝓝 ((0 : H) + x)) :=
        hgap_neg.add hx_tendsto
      have hsplit : (fun n ↦ (z_n n - x_n n) + x_n n) = z_n := by
        funext n
        abel_nf
      simpa [hsplit] using hsum
    exact ⟨by simpa [x_n, x] using hx_tendsto, by simpa [z_n, x] using hz_tendsto⟩

end DouglasRachfordAlgorithm

end RemainingOwners

end LocalDouglasRachfordOwner

end SetValuedOperator

namespace ERealFunction

-- Semantic recall note: `lean_leansearch` did not return a useful Douglas--Rachford
-- formalization for this item. The public surface therefore keeps the source recursion `(28.13)`
-- while exposing explicit bridge theorems to the verified Chapter 26 Douglas--Rachford sequence
-- owners and their fixed-point convergence API.

section DouglasRachfordAlgorithm

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Corollary 28.3: the resolvent realizer of `∂ f` is exactly the scaled proximity
operator `Prox[γ, f, hf]`. -/
private theorem resolventMapSubdifferential_eq_scaledProximityOperator
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    resolventMap (∂ f) (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ =
      Prox[γ, f, hf] := by
  -- Compare the single-valued resolvent and proximal realizers through their set-valued owners.
  have hrealizer :
      Function.toSetValuedOperator
          (resolventMap (∂ f) (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ) =
        Function.toSetValuedOperator (Prox[γ, f, hf]) := by
    calc
      Function.toSetValuedOperator
          (resolventMap (∂ f) (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ) =
          J[((γ : ℝ) • (∂ f : SetValuedOperator H H))] := by
            simpa using
              SetValuedOperator.resolventMap_toSetValuedOperator_eq
                (∂ f) (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) γ
      _ = Function.toSetValuedOperator (Prox[γ, f, hf]) := by
            rw [← subdifferential_posReal_smul_eq_smul f γ, resolvent_def]
            simpa [scaledProximityOperator] using
              (singleton_proximityOperator_eq_inverse_add_subdifferential
                (smul_mem_gammaZero f hf γ)).symm
  ext x
  have hx := congrArg (fun T : SetValuedOperator H H ↦ T x) hrealizer
  simpa [Function.toSetValuedOperator_apply, Set.singleton_eq_singleton_iff] using hx

/-- A quadruple of sequences `x`, `u`, `z`, and `y` satisfies the Douglas--Rachford recursion
`(28.13)` for `f`, `g`, step size `γ`, relaxation parameters `lam`, and initial point `y0`. -/
structure IsDouglasRachfordProximalOrbit
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) (x u z y : ℕ → H) : Prop where
  /-- The orbit starts at the prescribed point `y0`. -/
  y_zero : y 0 = y0
  /-- The first proximal step is `x_n = Prox_{γ g}(y_n)`. -/
  x_eq : ∀ n : ℕ, x n = Prox[γ, g, hg] (y n)
  /-- The dual shadow is `u_n = γ⁻¹ (y_n - x_n)`. -/
  u_eq : ∀ n : ℕ, u n = (γ : ℝ)⁻¹ • (y n - x n)
  /-- The reflected proximal step is `z_n = Prox_{γ f}(2 x_n - y_n)`. -/
  z_eq : ∀ n : ℕ, z n = Prox[γ, f, hf] ((2 : ℝ) • x n - y n)
  /-- The relaxed update is `y_(n+1) = y_n + λ_n (z_n - x_n)`. -/
  y_succ_eq : ∀ n : ℕ, y (n + 1) = y n + lam n • (z n - x n)

namespace IsDouglasRachfordProximalOrbit

variable {f g : H → Set.Ioi (⊥ : EReal)} {hf : f ∈ Γ₀(H)} {hg : g ∈ Γ₀(H)}
variable {γ : PosReal} {lam : ℕ → ℝ} {y0 : H} {x u z y : ℕ → H}

local notation "hSubf" => subdifferential_isMaximallyMonotone_of_mem_gammaZero hf
local notation "hSubg" => subdifferential_isMaximallyMonotone_of_mem_gammaZero hg

/-- The `y`-sequence of the source proximal recursion is the Chapter 26
Douglas--Rachford orbit for the subdifferential pair `(∂ f, ∂ g)`. -/
theorem y_eq_douglasRachfordIteration
    (hOrbit : IsDouglasRachfordProximalOrbit hf hg γ lam y0 x u z y) :
    y = douglasRachfordIteration (∂ f) (∂ g) hSubf hSubg γ lam y0 := by
  -- Route correction: normalize the relaxed-iteration prefix first, then rewrite both successor
  -- formulas to the same Douglas--Rachford operator update.
  funext n
  induction n with
  | zero =>
      -- Both recursions start from the prescribed initial point `y0`.
      simpa using hOrbit.y_zero
  | succ n ih =>
      have ih' :
          relaxedOperatorIteration
            (fun _ ↦
              douglasRachfordOperator
                (resolventMap (∂ f) hSubf γ)
                (resolventMap (∂ g) hSubg γ))
            lam y0 n =
            y n := by
        -- Rewrite the induction hypothesis into the raw relaxed-iteration owner.
        simpa [douglasRachfordIteration] using ih.symm
      have hx :
          resolventMap (∂ g) hSubg γ (y n) = x n := by
        -- The source proximal shadow is exactly the subdifferential resolvent realizer.
        simpa [resolventMapSubdifferential_eq_scaledProximityOperator hg γ] using
          (hOrbit.x_eq n).symm
      have hz :
          resolventMap (∂ f) hSubf γ ((2 : ℝ) • x n - y n) = z n := by
        -- The reflected proximal step is the companion resolvent realizer for `∂ f`.
        simpa [resolventMapSubdifferential_eq_scaledProximityOperator hf γ] using
          (hOrbit.z_eq n).symm
      -- Rewrite the source successor rule through the canonical Douglas--Rachford operator.
      rw [hOrbit.y_succ_eq n, douglasRachfordIteration, relaxedOperatorIteration_succ, ih']
      change
        y n + lam n • (z n - x n) =
          y n + lam n •
            (douglasRachfordOperator
                (resolventMap (∂ f) hSubf γ)
                (resolventMap (∂ g) hSubg γ)
                (y n) -
              y n)
      rw [douglasRachfordOperator_apply, hx, hz]
      abel_nf

/-- The `x`-sequence of the source proximal recursion is the Chapter 26
Douglas--Rachford primal sequence for `(∂ f, ∂ g)`. -/
theorem x_eq_douglasRachfordPrimalSequence
    (hOrbit : IsDouglasRachfordProximalOrbit hf hg γ lam y0 x u z y) :
    x = douglasRachfordPrimalSequence (∂ f) (∂ g) hSubf hSubg γ lam y0 := by
  funext n
  -- Rewrite the source primal shadow through the already identified Douglas--Rachford orbit.
  calc
    x n = Prox[γ, g, hg] (y n) := hOrbit.x_eq n
    _ = resolventMap (∂ g) hSubg γ (y n) := by
      rw [← resolventMapSubdifferential_eq_scaledProximityOperator hg γ]
    _ =
        resolventMap (∂ g) hSubg γ
          (douglasRachfordIteration (∂ f) (∂ g) hSubf hSubg γ lam y0 n) := by
            rw [hOrbit.y_eq_douglasRachfordIteration]
    _ = douglasRachfordPrimalSequence (∂ f) (∂ g) hSubf hSubg γ lam y0 n := by
      rfl

/-- The `u`-sequence of the source proximal recursion is the Chapter 26
Douglas--Rachford dual sequence for `(∂ f, ∂ g)`. -/
theorem u_eq_douglasRachfordDualSequence
    (hOrbit : IsDouglasRachfordProximalOrbit hf hg γ lam y0 x u z y) :
    u = douglasRachfordDualSequence (∂ f) (∂ g) hSubf hSubg γ lam y0 := by
  funext n
  -- Rewrite the source residual formula into the canonical Yosida realizer of `∂ g`.
  calc
    u n = (γ : ℝ)⁻¹ • (y n - x n) := hOrbit.u_eq n
    _ = (γ : ℝ)⁻¹ • (y n - resolventMap (∂ g) hSubg γ (y n)) := by
      congr 1
      rw [hOrbit.x_eq n, ← resolventMapSubdifferential_eq_scaledProximityOperator hg γ]
    _ = yosidaApproximationMap (∂ g) hSubg γ (y n) := by
      rw [yosidaApproximationMap_apply]
    _ =
        yosidaApproximationMap (∂ g) hSubg γ
          (douglasRachfordIteration (∂ f) (∂ g) hSubf hSubg γ lam y0 n) := by
            rw [hOrbit.y_eq_douglasRachfordIteration]
    _ = douglasRachfordDualSequence (∂ f) (∂ g) hSubf hSubg γ lam y0 n := by
      rfl

/-- The `z`-sequence of the source proximal recursion is the Chapter 26
Douglas--Rachford auxiliary sequence for `(∂ f, ∂ g)`. -/
theorem z_eq_douglasRachfordAuxiliarySequence
    (hOrbit : IsDouglasRachfordProximalOrbit hf hg γ lam y0 x u z y) :
    z = douglasRachfordAuxiliarySequence (∂ f) (∂ g) hSubf hSubg γ lam y0 := by
  funext n
  -- Rewrite the source reflected proximal step through the canonical resolvent owners.
  calc
    z n = Prox[γ, f, hf] ((2 : ℝ) • x n - y n) := hOrbit.z_eq n
    _ = resolventMap (∂ f) hSubf γ ((2 : ℝ) • x n - y n) := by
      rw [← resolventMapSubdifferential_eq_scaledProximityOperator hf γ]
    _ =
        resolventMap (∂ f) hSubf γ
          ((2 : ℝ) • douglasRachfordPrimalSequence (∂ f) (∂ g) hSubf hSubg γ lam y0 n -
            douglasRachfordIteration (∂ f) (∂ g) hSubf hSubg γ lam y0 n) := by
              rw [hOrbit.x_eq_douglasRachfordPrimalSequence, hOrbit.y_eq_douglasRachfordIteration]
    _ = douglasRachfordAuxiliarySequence (∂ f) (∂ g) hSubf hSubg γ lam y0 n := by
      rfl

end IsDouglasRachfordProximalOrbit

section OrbitConsequences

variable {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
variable (hzero : (((∂ f) + (∂ g)).zeros).Nonempty)
variable (lam : ℕ → ℝ) (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
variable
  (hdiv :
    Tendsto
      (fun N : ℕ ↦
        (Finset.range N).sum (fun n : ℕ ↦ lam n * (2 - lam n)))
      atTop atTop)
variable (γ : PosReal) (y0 : H) {x u z ySeq : ℕ → H}
variable (hOrbit : IsDouglasRachfordProximalOrbit hf hg γ lam y0 x u z ySeq)

local notation "hSubf" => subdifferential_isMaximallyMonotone_of_mem_gammaZero hf
local notation "hSubg" => subdifferential_isMaximallyMonotone_of_mem_gammaZero hg

section

omit [CompleteSpace H]

/-- Helper for Corollary 28.3: the source uniform-convexity alternative implies the Chapter 26
uniform-monotonicity alternative for `∂ f` or `∂ g`. -/
private theorem uniformConvexAlternative_to_subdifferentialUniformMonotoneAlternative
    (hfGamma : f ∈ Γ₀(H)) (hgGamma : g ∈ Γ₀(H))
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          ∃ φ : NNReal → EReal, UniformlyConvexOn f S φ) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ g).dom →
            ∃ φ : NNReal → EReal, UniformlyConvexOn g S φ) :
    (∀ S : Set H,
      S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
        (∂ f).IsUniformlyMonotoneOn S) ∨
      ∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ g).dom →
          (∂ g).IsUniformlyMonotoneOn S := by
  rcases hUniform with hUniform | hUniform
  · left
    intro S hS hS_bounded hS_sub
    obtain ⟨φ, hφ⟩ := hUniform S hS hS_bounded hS_sub
    -- Example 22.5 turns the source uniform convexity modulus into uniform monotonicity of `∂ f`.
    exact
      subdifferential_isUniformlyMonotoneOn_of_convexOn_of_uniformlyConvexOn
        f (mem_gammaZero_iff.mp hfGamma).2 hS_sub hφ
  · right
    intro S hS hS_bounded hS_sub
    obtain ⟨φ, hφ⟩ := hUniform S hS hS_bounded hS_sub
    -- Apply the same Example 22.5 bridge on the `g` branch.
    exact
      subdifferential_isUniformlyMonotoneOn_of_convexOn_of_uniformlyConvexOn
        g (mem_gammaZero_iff.mp hgGamma).2 hS_sub hφ

/-- Helper for Corollary 28.3: the source zero-set hypothesis is exactly nonemptiness of the
Chapter 26 primal solution set for the subdifferential pair. -/
private theorem subdifferentialPrimalSolutionSet_nonempty :
    (((∂ f) + (∂ g)).zeros).Nonempty →
      (primal_inclusion_solution_set (∂ f) (∂ g)).Nonempty := by
  intro hzero
  simpa [SetValuedOperator.primal_inclusion_solution_set] using hzero

end

/-- Helper theorem: the source Douglas--Rachford orbit yields a weakly convergent `y`-sequence
whose limit is a fixed point of the operator-level reflected resolvent composition. -/
theorem douglasRachfordAlgorithm_exists_fixedPoint_tendsto_weakly
    (hzero : (((∂ f) + (∂ g)).zeros).Nonempty)
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum (fun n : ℕ ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hOrbit : IsDouglasRachfordProximalOrbit hf hg γ lam y0 x u z ySeq) :
    ∃ ybar ∈ fixedPoints (reflectedResolventComposition (∂ f) (∂ g) hSubf hSubg γ),
      Tendsto
        (fun n : ℕ ↦ toWeakSpace ℝ H (ySeq n))
        atTop (𝓝 (toWeakSpace ℝ H ybar)) := by
  have hzero' :
      (primal_inclusion_solution_set (∂ f) (∂ g)).Nonempty :=
    subdifferentialPrimalSolutionSet_nonempty (f := f) (g := g) hzero
  obtain ⟨ybar, hybar_fix, hybar_tendsto⟩ :=
    SetValuedOperator.douglasRachfordAlgorithm_exists_fixedPoint_tendsto_weakly
      (A := ∂ f) (B := ∂ g) hSubf hSubg
      (hzero := hzero') (lam := lam) (hlam := hlam) (hdiv := hdiv) (γ := γ) (y0 := y0)
  refine ⟨ybar, hybar_fix, ?_⟩
  -- Transport the operator-level weak limit back through the source orbit identification.
  simpa [hOrbit.y_eq_douglasRachfordIteration] using hybar_tendsto

/-- Helper theorem: a fixed point `ȳ` of the operator-level Douglas--Rachford map yields the
canonical primal and dual inclusion solutions `x̄ = Prox_{γ g} ȳ` and
`ū = γ⁻¹ (ȳ - x̄)`. -/
theorem douglasRachfordAlgorithm_limit_point_mem_inclusion_solution_sets
    {ybar : H}
    (hy_fix : ybar ∈ fixedPoints (reflectedResolventComposition (∂ f) (∂ g) hSubf hSubg γ)) :
    Prox[γ, g, hg] ybar ∈ primal_inclusion_solution_set (∂ f) (∂ g) ∧
      (γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar) ∈ dual_inclusion_solution_set (∂ f) (∂ g) :=
  by
  -- Repackage the local operator-level fixed-point theorem through the prox/resolvent bridge.
  simpa [resolventMapSubdifferential_eq_scaledProximityOperator hg γ,
    yosidaApproximationMap_apply] using
    (SetValuedOperator.douglasRachfordAlgorithm_limit_primal_dual_solution
      (∂ f) (∂ g) hSubf hSubg γ hy_fix)

/-- Result for Corollary 28.3 (1): let `f, g ∈ Γ₀(H)` with `((∂ f) + (∂ g)).zeros` nonempty, let
`(λ_n)` lie in `[0, 2]` with `∑ λ_n (2 - λ_n) = +∞`, let `γ ∈ ℝ_{++}`, and let `x`, `u`, `z`,
and `y` satisfy the Douglas--Rachford recursion `(28.13)` from `y0`. Then `(y_n)` converges
weakly to some `ȳ`. -/
theorem douglasRachfordAlgorithm_exists_weakLimit
    (hzero : (((∂ f) + (∂ g)).zeros).Nonempty)
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum (fun n : ℕ ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hOrbit : IsDouglasRachfordProximalOrbit hf hg γ lam y0 x u z ySeq)
    :
    ∃ ybar : H,
      Tendsto
        (fun n : ℕ ↦ toWeakSpace ℝ H (ySeq n))
        atTop (𝓝 (toWeakSpace ℝ H ybar)) := by
  obtain ⟨ybar, _hybar_fix, hybar_tendsto⟩ :=
    douglasRachfordAlgorithm_exists_fixedPoint_tendsto_weakly
      (hf := hf) (hg := hg) (hzero := hzero) (lam := lam) (hlam := hlam)
      (hdiv := hdiv) (γ := γ) (y0 := y0) hOrbit
  -- Forget the fixed-point witness and keep the weak convergence conclusion.
  exact ⟨ybar, hybar_tendsto⟩

/-- Result for Corollary 28.3 (2): if `ȳ` is the fixed-point limit associated with the
Douglas--Rachford
orbit and we set `x̄ = Prox_{γ g} ȳ` and `ū = γ⁻¹ (ȳ - x̄)`, then `x̄` solves the primal problem
and `ū` solves the identity-map dual problem `v ↦ f^*(-v) + g^*(v)`, represented here by the
canonical owner `compositeDualObjective f g (ContinuousLinearMap.id ℝ H)`. -/
theorem douglasRachfordAlgorithm_limit_point_mem_argmin_and_dualArgmin
    {ybar : H}
    (hzero : (((∂ f) + (∂ g)).zeros).Nonempty)
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum (fun n : ℕ ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hOrbit : IsDouglasRachfordProximalOrbit hf hg γ lam y0 x u z ySeq)
    (hy_fix : ybar ∈ fixedPoints (reflectedResolventComposition (∂ f) (∂ g) hSubf hSubg γ))
    (hy_tendsto :
      Tendsto
        (fun n : ℕ ↦ toWeakSpace ℝ H (ySeq n))
        atTop (𝓝 (toWeakSpace ℝ H ybar))) :
    Prox[γ, g, hg] ybar ∈ Argmin ((f + g).asEReal) ∧
      (γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar) ∈
        Argmin (compositeDualObjective f g (ContinuousLinearMap.id ℝ H)) := by
  -- Keep the standing source hypotheses explicit on this clause even though the fixed-point
  -- argument below only needs `hy_fix`.
  let _ := hzero
  let _ := hlam
  let _ := hdiv
  let _ := hOrbit
  let _ := hy_tendsto
  have hsubgrad :
      -(ContinuousLinearMap.id ℝ H).adjoint
          ((γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar)) ∈
        (∂ f) (Prox[γ, g, hg] ybar) ∧
      ((γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar)) ∈
        (∂ g) ((ContinuousLinearMap.id ℝ H) (Prox[γ, g, hg] ybar)) := by
    -- Rewrite the fixed-point graph witnesses into the source proximal/Yosida spelling.
    simpa [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply,
      resolventMapSubdifferential_eq_scaledProximityOperator hg γ,
      yosidaApproximationMap_apply] using
      (SetValuedOperator.douglasRachfordLimitGraphData
        (∂ f) (∂ g) hSubf hSubg γ hy_fix)
  have hargmin :
      Prox[γ, g, hg] ybar ∈
          Argmin (compositePrimalObjective f g (ContinuousLinearMap.id ℝ H)) ∧
        ((γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar)) ∈
          Argmin (compositeDualObjective f g (ContinuousLinearMap.id ℝ H)) ∧
        compositePrimalOptimalValue f g (ContinuousLinearMap.id ℝ H) =
          -compositeDualOptimalValue f g (ContinuousLinearMap.id ℝ H) :=
    ((ERealFunction.primal_dual_solution_tfae_for_composite_objective hf hg
      (ContinuousLinearMap.id ℝ H) (Prox[γ, g, hg] ybar)
      ((γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar))).out 1 0).mp hsubgrad
  exact
    ⟨by simpa [compositePrimalObjective_apply, ContinuousLinearMap.id_apply] using hargmin.1,
      hargmin.2.1⟩

/-- Result for Corollary 28.3 (3): under the Douglas--Rachford hypotheses, the gap sequence
`x_n - z_n` converges strongly to `0`. -/
theorem douglasRachfordAlgorithm_sub_tendsto_zero
    (hzero : (((∂ f) + (∂ g)).zeros).Nonempty)
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum (fun n : ℕ ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hOrbit : IsDouglasRachfordProximalOrbit hf hg γ lam y0 x u z ySeq) :
    Tendsto (fun n : ℕ ↦ x n - z n) atTop (𝓝 (0 : H)) := by
  have hzero' :
      (primal_inclusion_solution_set (∂ f) (∂ g)).Nonempty :=
    subdifferentialPrimalSolutionSet_nonempty (f := f) (g := g) hzero
  -- Rewrite the source sequences to the operator-level orbit, then apply the generic gap owner.
  simpa [hOrbit.x_eq_douglasRachfordPrimalSequence, hOrbit.z_eq_douglasRachfordAuxiliarySequence]
    using
      (SetValuedOperator.douglasRachfordAlgorithm_primal_auxiliary_gap_tendsto_zero
        (A := ∂ f) (B := ∂ g) hSubf hSubg
        (hzero := hzero') (lam := lam) (hlam := hlam) (hdiv := hdiv) (γ := γ) (y0 := y0))

/-- Result for Corollary 28.3 (4): if `ȳ` is the weak limit of the Douglas--Rachford orbit and
`x̄ = Prox_{γ g} ȳ`, then both `x_n` and `z_n` converge weakly to `x̄`. -/
theorem douglasRachfordAlgorithm_primal_auxiliary_tendsto_weakly
    {ybar : H}
    (hzero : (((∂ f) + (∂ g)).zeros).Nonempty)
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum (fun n : ℕ ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hOrbit : IsDouglasRachfordProximalOrbit hf hg γ lam y0 x u z ySeq)
    (hy_fix : ybar ∈ fixedPoints (reflectedResolventComposition (∂ f) (∂ g) hSubf hSubg γ))
    (hy_tendsto :
      Tendsto
        (fun n : ℕ ↦ toWeakSpace ℝ H (ySeq n))
        atTop (𝓝 (toWeakSpace ℝ H ybar))) :
    Tendsto
        (fun n : ℕ ↦ toWeakSpace ℝ H (x n))
        atTop (𝓝 (toWeakSpace ℝ H (Prox[γ, g, hg] ybar))) ∧
    Tendsto
        (fun n : ℕ ↦ toWeakSpace ℝ H (z n))
        atTop (𝓝 (toWeakSpace ℝ H (Prox[γ, g, hg] ybar))) := by
  have hzero' :
      (primal_inclusion_solution_set (∂ f) (∂ g)).Nonempty :=
    subdifferentialPrimalSolutionSet_nonempty (f := f) (g := g) hzero
  have hy_tendsto' :
      Tendsto
        (fun n : ℕ ↦
          toWeakSpace ℝ H
            (SetValuedOperator.douglasRachfordIteration (∂ f) (∂ g) hSubf hSubg γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H ybar)) := by
    -- Move the source weak limit onto the operator-level orbit owner.
    simpa [hOrbit.y_eq_douglasRachfordIteration] using hy_tendsto
  have hbase :=
    SetValuedOperator.douglasRachfordAlgorithm_primal_auxiliary_tendsto_weakly
      (A := ∂ f) (B := ∂ g) hSubf hSubg
      (hzero := hzero') (lam := lam) (hlam := hlam) (hdiv := hdiv)
      (γ := γ) (y0 := y0) (y := ybar) (hy_fix := hy_fix) (hy_tendsto := hy_tendsto')
  -- Rewrite the operator-level primal and auxiliary limits back to the source proximal recursion.
  simpa [hOrbit.x_eq_douglasRachfordPrimalSequence, hOrbit.z_eq_douglasRachfordAuxiliarySequence,
    resolventMapSubdifferential_eq_scaledProximityOperator hg γ] using hbase

/-- Result for Corollary 28.3 (5): if `ȳ` is the weak limit of the Douglas--Rachford orbit and
`ū = γ⁻¹ (ȳ - Prox_{γ g} ȳ)`, then `u_n` converges weakly to `ū`. -/
theorem douglasRachfordAlgorithm_dual_tendsto_weakly
    {ybar : H}
    (hzero : (((∂ f) + (∂ g)).zeros).Nonempty)
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum (fun n : ℕ ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hOrbit : IsDouglasRachfordProximalOrbit hf hg γ lam y0 x u z ySeq)
    (hy_fix : ybar ∈ fixedPoints (reflectedResolventComposition (∂ f) (∂ g) hSubf hSubg γ))
    (hy_tendsto :
      Tendsto
        (fun n : ℕ ↦ toWeakSpace ℝ H (ySeq n))
        atTop (𝓝 (toWeakSpace ℝ H ybar))) :
    Tendsto
      (fun n : ℕ ↦ toWeakSpace ℝ H (u n))
      atTop
        (𝓝 (toWeakSpace ℝ H ((γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar)))) := by
  have hzero' :
      (primal_inclusion_solution_set (∂ f) (∂ g)).Nonempty :=
    subdifferentialPrimalSolutionSet_nonempty (f := f) (g := g) hzero
  have hy_tendsto' :
      Tendsto
        (fun n : ℕ ↦
          toWeakSpace ℝ H
            (SetValuedOperator.douglasRachfordIteration (∂ f) (∂ g) hSubf hSubg γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H ybar)) := by
    -- Move the source weak limit onto the operator-level orbit owner.
    simpa [hOrbit.y_eq_douglasRachfordIteration] using hy_tendsto
  have hbase :=
    SetValuedOperator.douglasRachfordAlgorithm_dual_tendsto_weakly
      (A := ∂ f) (B := ∂ g) hSubf hSubg
      (hzero := hzero') (lam := lam) (hlam := hlam) (hdiv := hdiv)
      (γ := γ) (y0 := y0) (y := ybar) (hy_fix := hy_fix) (hy_tendsto := hy_tendsto')
  -- Rewrite the operator-level Yosida limit back to the source dual residual formula.
  simpa [hOrbit.u_eq_douglasRachfordDualSequence, yosidaApproximationMap_apply,
    resolventMapSubdifferential_eq_scaledProximityOperator hg γ] using hbase

namespace DouglasRachfordAlgorithm
/-- Result for Corollary 28.3 (6): under the Douglas--Rachford hypotheses, if `f` is
uniformly convex on
every nonempty bounded subset of `(∂ f).dom` or `g` is uniformly convex on every nonempty bounded
subset of `(∂ g).dom`, then the primal solution set is the singleton `{Prox_{γ g} ȳ}`. -/
theorem argmin_eq_singleton_of_uniformlyConvexOnEveryBoundedSubset
    {ybar : H}
    (hzero : (((∂ f) + (∂ g)).zeros).Nonempty)
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum (fun n : ℕ ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hOrbit : IsDouglasRachfordProximalOrbit hf hg γ lam y0 x u z ySeq)
    (hy_fix : ybar ∈ fixedPoints (reflectedResolventComposition (∂ f) (∂ g) hSubf hSubg γ))
    (hy_tendsto :
      Tendsto
        (fun n : ℕ ↦ toWeakSpace ℝ H (ySeq n))
        atTop (𝓝 (toWeakSpace ℝ H ybar)))
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          ∃ φ : NNReal → EReal, UniformlyConvexOn f S φ) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ g).dom →
            ∃ φ : NNReal → EReal, UniformlyConvexOn g S φ) :
    Argmin ((f + g).asEReal) = ({Prox[γ, g, hg] ybar} : Set H) := by
  have hUniform' :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          (∂ f).IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ g).dom →
            (∂ g).IsUniformlyMonotoneOn S :=
    uniformConvexAlternative_to_subdifferentialUniformMonotoneAlternative
      (f := f) (g := g) hf hg hUniform
  open SetValuedOperator.DouglasRachfordAlgorithm in
  have hprimal_singleton :
      primal_inclusion_solution_set (∂ f) (∂ g) = ({Prox[γ, g, hg] ybar} : Set H) := by
    -- Invoke the generic uniqueness owner and rewrite its resolvent point back to `Prox`.
    simpa [resolventMapSubdifferential_eq_scaledProximityOperator hg γ] using
      (unique_primal_solution_of_uniformlyMonotoneOnEveryBoundedSubset
        (A := ∂ f) (B := ∂ g) hSubf hSubg (γ := γ) (y := ybar) (hy_fix := hy_fix) hUniform')
  have hubar_primal_dual :
      Prox[γ, g, hg] ybar ∈ primal_inclusion_solution_set (∂ f) (∂ g) ∧
        (γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar) ∈
          dual_inclusion_solution_set (∂ f) (∂ g) :=
    douglasRachfordAlgorithm_limit_point_mem_inclusion_solution_sets
      (hf := hf) (hg := hg) (γ := γ) (hy_fix := hy_fix)
  have hsubgradLimit :
      -(ContinuousLinearMap.id ℝ H).adjoint
          ((γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar)) ∈
        (∂ f) (Prox[γ, g, hg] ybar) ∧
      ((γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar)) ∈
        (∂ g) ((ContinuousLinearMap.id ℝ H) (Prox[γ, g, hg] ybar)) := by
    -- Reuse the fixed-point graph witnesses in the source proximal spelling.
    simpa [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply,
      resolventMapSubdifferential_eq_scaledProximityOperator hg γ,
      yosidaApproximationMap_apply] using
      (SetValuedOperator.douglasRachfordLimitGraphData
        (∂ f) (∂ g) hSubf hSubg γ hy_fix)
  have hlimitTriple :
      Prox[γ, g, hg] ybar ∈ Argmin (compositePrimalObjective f g (ContinuousLinearMap.id ℝ H)) ∧
        ((γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar)) ∈
          Argmin (compositeDualObjective f g (ContinuousLinearMap.id ℝ H)) ∧
        compositePrimalOptimalValue f g (ContinuousLinearMap.id ℝ H) =
          -compositeDualOptimalValue f g (ContinuousLinearMap.id ℝ H) :=
    ((ERealFunction.primal_dual_solution_tfae_for_composite_objective hf hg
      (ContinuousLinearMap.id ℝ H) (Prox[γ, g, hg] ybar)
      ((γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar))).out 1 0).mp hsubgradLimit
  ext q
  constructor
  · intro hq
    have hq_subgrad :
        -(ContinuousLinearMap.id ℝ H).adjoint
            ((γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar)) ∈ (∂ f) q ∧
          ((γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar)) ∈
            (∂ g) ((ContinuousLinearMap.id ℝ H) q) := by
      have hq_triple :
          q ∈ Argmin (compositePrimalObjective f g (ContinuousLinearMap.id ℝ H)) ∧
            ((γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar)) ∈
              Argmin (compositeDualObjective f g (ContinuousLinearMap.id ℝ H)) ∧
            compositePrimalOptimalValue f g (ContinuousLinearMap.id ℝ H) =
              -compositeDualOptimalValue f g (ContinuousLinearMap.id ℝ H) := by
        -- Pair the current primal argmin with the fixed dual argmin and strong duality witness.
        refine ⟨?_, hlimitTriple.2.1, hlimitTriple.2.2⟩
        simpa [compositePrimalObjective_apply, ContinuousLinearMap.id_apply] using hq
      -- Combine the given primal argmin with the limit dual argmin and strong duality.
      exact
        ((ERealFunction.primal_dual_solution_tfae_for_composite_objective hf hg
          (ContinuousLinearMap.id ℝ H) q
          ((γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar))).out 0 1).mp hq_triple
    have hq_primal : q ∈ primal_inclusion_solution_set (∂ f) (∂ g) := by
      -- Package the shared dual witness into the Chapter 26 primal inclusion owner.
      refine
        (mem_primal_inclusion_solution_set_iff_exists_mem_dual_inclusion_solution_set
          (∂ f) (∂ g)).2 ?_
      exact
        ⟨(γ : ℝ)⁻¹ • (ybar - Prox[γ, g, hg] ybar), hubar_primal_dual.2,
          by simpa [ContinuousLinearMap.adjoint_id] using hq_subgrad.1,
          by simpa [ContinuousLinearMap.id_apply] using hq_subgrad.2⟩
    -- The generic uniqueness owner collapses the primal argmin to the single prox point.
    simpa [hprimal_singleton] using hq_primal
  · intro hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    -- The limit prox point is already known to solve the primal minimization problem.
    exact
      (douglasRachfordAlgorithm_limit_point_mem_argmin_and_dualArgmin
        (hf := hf) (hg := hg) (hzero := hzero) (lam := lam) (hlam := hlam)
        (hdiv := hdiv) (γ := γ) (y0 := y0) (hOrbit := hOrbit)
        (hy_fix := hy_fix) (hy_tendsto := hy_tendsto)).1

/-- Result for Corollary 28.3 (7): under the uniform-convexity alternative of Corollary 28.3, if
`x̄ = Prox_{γ g} ȳ`, then both `x_n` and `z_n` converge strongly to `x̄`. -/
theorem primal_auxiliary_tendsto_of_uniformlyConvexOnEveryBoundedSubset
    {ybar : H}
    (hzero : (((∂ f) + (∂ g)).zeros).Nonempty)
    (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum (fun n : ℕ ↦ lam n * (2 - lam n)))
        atTop atTop)
    (hOrbit : IsDouglasRachfordProximalOrbit hf hg γ lam y0 x u z ySeq)
    (hy_fix : ybar ∈ fixedPoints (reflectedResolventComposition (∂ f) (∂ g) hSubf hSubg γ))
    (hy_tendsto :
      Tendsto
        (fun n : ℕ ↦ toWeakSpace ℝ H (ySeq n))
        atTop (𝓝 (toWeakSpace ℝ H ybar)))
    (hUniform :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          ∃ φ : NNReal → EReal, UniformlyConvexOn f S φ) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ g).dom →
            ∃ φ : NNReal → EReal, UniformlyConvexOn g S φ) :
    Tendsto x atTop (𝓝 (Prox[γ, g, hg] ybar)) ∧
      Tendsto z atTop (𝓝 (Prox[γ, g, hg] ybar)) := by
  have hzero' :
      (primal_inclusion_solution_set (∂ f) (∂ g)).Nonempty :=
    subdifferentialPrimalSolutionSet_nonempty (f := f) (g := g) hzero
  have hy_tendsto' :
      Tendsto
        (fun n : ℕ ↦
          toWeakSpace ℝ H
            (SetValuedOperator.douglasRachfordIteration (∂ f) (∂ g) hSubf hSubg γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H ybar)) := by
    -- Move the source weak limit onto the operator-level orbit owner.
    simpa [hOrbit.y_eq_douglasRachfordIteration] using hy_tendsto
  have hUniform' :
      (∀ S : Set H,
        S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ f).dom →
          (∂ f).IsUniformlyMonotoneOn S) ∨
        ∀ S : Set H,
          S.Nonempty → Bornology.IsBounded S → S ⊆ (∂ g).dom →
            (∂ g).IsUniformlyMonotoneOn S :=
    uniformConvexAlternative_to_subdifferentialUniformMonotoneAlternative
      (f := f) (g := g) hf hg hUniform
  open SetValuedOperator.DouglasRachfordAlgorithm in
  have hbase :=
    primal_auxiliary_tendsto_of_uniformlyMonotoneOnEveryBoundedSubset
      (A := ∂ f) (B := ∂ g) hSubf hSubg
      (hzero := hzero') (lam := lam) (hlam := hlam) (hdiv := hdiv)
      (γ := γ) (y0 := y0) (y := ybar) (hy_fix := hy_fix) (hy_tendsto := hy_tendsto')
      (hUniform := hUniform')
  -- Rewrite the operator-level strong limits back to the source proximal recursion.
  simpa [hOrbit.x_eq_douglasRachfordPrimalSequence, hOrbit.z_eq_douglasRachfordAuxiliarySequence,
    resolventMapSubdifferential_eq_scaledProximityOperator hg γ] using hbase

end DouglasRachfordAlgorithm

end OrbitConsequences

end DouglasRachfordAlgorithm

end ERealFunction
