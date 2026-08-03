import BauschkeLean.Chap02.Example_2_32_1
import BauschkeLean.Chap02.Text_2_0_14
import BauschkeLean.Chap04.Corollary_4_28
import BauschkeLean.Chap16.Example_16_22
import BauschkeLean.Chap17.Corollary_17_42
import BauschkeLean.Chap17.Proposition_17_6
import BauschkeLean.Chap17.Proposition_17_22
import BauschkeLean.Chap29.Definition_29_40

open Filter
open SetValuedOperator
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

noncomputable section

local notation "L2pos" => ℓ²(ℕ+, ℝ)

/-- Every point of `ℓ²(ℕ+, ℝ)` is a source continuity point of the Example 16.22 weighted
even-power series. -/
private theorem positiveNatWeightedEvenPowerSeries_continuousPoint (x : L2pos) :
    ContinuousPoint positiveNatWeightedEvenPowerSeries x := by
  refine ⟨1, by norm_num, ?_, ?_⟩
  · rw [positiveNatWeightedEvenPowerSeries_effectiveDomain_eq_univ]
    simp
  · simpa using positiveNatWeightedEvenPowerSeries_continuous.continuousAt

private abbrev positiveNatWeightedEvenPowerSeriesReal : L2pos → ℝ :=
  fun x ↦ (positiveNatWeightedEvenPowerSeries x : EReal).toReal

@[simp] private theorem positiveNatWeightedEvenPowerSeriesReal_toEReal (x : L2pos) :
    ((positiveNatWeightedEvenPowerSeriesReal x : ℝ) : EReal) =
      (positiveNatWeightedEvenPowerSeries x : EReal) := by
  have hx : x ∈ effectiveDomain positiveNatWeightedEvenPowerSeries := by
    rw [positiveNatWeightedEvenPowerSeries_effectiveDomain_eq_univ]
    simp
  have htop : (positiveNatWeightedEvenPowerSeries x : EReal) ≠ ⊤ := ne_of_lt hx
  have hbot : (positiveNatWeightedEvenPowerSeries x : EReal) ≠ ⊥ := by
    exact ne_of_gt (positiveNatWeightedEvenPowerSeries x).2
  simpa [positiveNatWeightedEvenPowerSeriesReal] using
    (EReal.coe_toReal htop hbot)

@[simp] private theorem positiveNatWeightedEvenPowerSeriesReal_toEReal_fun :
    positiveNatWeightedEvenPowerSeriesReal.toEReal = positiveNatWeightedEvenPowerSeries := by
  funext x
  apply Subtype.ext
  exact positiveNatWeightedEvenPowerSeriesReal_toEReal x

private noncomputable def positiveNatWeightedEvenPowerSeriesMinimalNormSelection :
    Selection (∂ positiveNatWeightedEvenPowerSeriesReal.toEReal) :=
  fun x ↦ by
    refine ⟨
      minimalNormSubgradient positiveNatWeightedEvenPowerSeries
        positiveNatWeightedEvenPowerSeries_mem_gammaZero.2 x.1
        (positiveNatWeightedEvenPowerSeries_continuousPoint x.1),
      ?_⟩
    simpa [positiveNatWeightedEvenPowerSeriesReal_toEReal_fun] using
      (minimalNormSubgradient_mem_subdifferential_of_continuousAtOnEffectiveDomain
        positiveNatWeightedEvenPowerSeries positiveNatWeightedEvenPowerSeries_mem_gammaZero.2
        (positiveNatWeightedEvenPowerSeries_continuousPoint x.1))

private theorem positiveNatWeightedEvenPowerSeriesReal_mem_subdifferential_dom
    (x : L2pos) :
    x ∈ SetValuedOperator.dom (∂ positiveNatWeightedEvenPowerSeriesReal.toEReal) := by
  rw [SetValuedOperator.mem_dom_iff]
  refine ⟨
    minimalNormSubgradient positiveNatWeightedEvenPowerSeries
      positiveNatWeightedEvenPowerSeries_mem_gammaZero.2 x
      (positiveNatWeightedEvenPowerSeries_continuousPoint x),
    ?_⟩
  simpa [positiveNatWeightedEvenPowerSeriesReal_toEReal_fun] using
    (minimalNormSubgradient_mem_subdifferential_of_continuousAtOnEffectiveDomain
      positiveNatWeightedEvenPowerSeries positiveNatWeightedEvenPowerSeries_mem_gammaZero.2
      (positiveNatWeightedEvenPowerSeries_continuousPoint x))

private theorem positiveNatWeightedEvenPowerSeriesReal_continuous :
    Continuous positiveNatWeightedEvenPowerSeriesReal := by
  simpa [positiveNatWeightedEvenPowerSeriesReal] using positiveNatWeightedEvenPowerSeries_continuous

private theorem positiveNatWeightedEvenPowerSeriesReal_convexOn :
    _root_.ConvexOn ℝ Set.univ positiveNatWeightedEvenPowerSeriesReal := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a ha0 ha1 hab
  have hE :
      ((positiveNatWeightedEvenPowerSeriesReal (a • x + (1 - a) • y) : ℝ) : EReal) ≤
        ((a * positiveNatWeightedEvenPowerSeriesReal x +
            (1 - a) * positiveNatWeightedEvenPowerSeriesReal y : ℝ) : EReal) := by
    simpa [positiveNatWeightedEvenPowerSeriesReal_toEReal, smul_eq_mul] using
      positiveNatWeightedEvenPowerSeries_mem_gammaZero.2.2
        (by simpa [positiveNatWeightedEvenPowerSeries_effectiveDomain_eq_univ])
        (by simpa [positiveNatWeightedEvenPowerSeries_effectiveDomain_eq_univ])
        ha0.le (sub_nonneg.mpr ha1.le) (by linarith)
  exact_mod_cast hE

private theorem positiveNatWeightedEvenPowerSeriesReal_lowerLevelSet_zero_nonempty :
    (lowerLevelSet positiveNatWeightedEvenPowerSeriesReal.toEReal.asEReal 0).Nonempty := by
  refine ⟨0, ?_⟩
  rw [ERealFunction.mem_lowerLevelSet_iff]
  have hzero : positiveNatWeightedEvenPowerSeriesReal (0 : L2pos) = 0 := by
    exact (positiveNatWeightedEvenPowerSeriesReal_eq_zero_iff (0 : L2pos)).2 rfl
  simpa [Function.toEReal_apply, hzero]

private theorem positiveNatWeightedEvenPowerSeriesReal_selectedSubgradient_eq (x : L2pos) :
    continuousConvexSelectedSubgradient
        positiveNatWeightedEvenPowerSeriesReal
        positiveNatWeightedEvenPowerSeriesReal_continuous
        positiveNatWeightedEvenPowerSeriesReal_convexOn
        positiveNatWeightedEvenPowerSeriesMinimalNormSelection x =
      positiveNatWeightedEvenPowerSeriesMinimalNormSelection
        ⟨x, positiveNatWeightedEvenPowerSeriesReal_mem_subdifferential_dom x⟩ := by
  rw [continuousConvexSelectedSubgradient]
  congr 1
  exact Subtype.ext (by rfl)

/-- The `n`th standard unit vector of `ℓ²(ℕ+, ℝ)`. -/
def positive_nat_standard_unit_vector (n : ℕ+) : L2pos :=
  lp.single 2 n (1 : ℝ)

/-- The textbook family `x_n = e_1 + e_n` from Example 29.48, indexed by positive naturals. -/
def weighted_even_power_counterexample_points (n : ℕ+) : L2pos :=
  positive_nat_standard_unit_vector 1 + positive_nat_standard_unit_vector n

/-- The `n ≥ 2` tail of the textbook family from Example 29.48, reindexed by `ℕ` for convergence
statements. -/
def weighted_even_power_counterexample_sequence (n : ℕ) : L2pos :=
  weighted_even_power_counterexample_points ⟨n + 2, by omega⟩

/-- Helper for Example 29.48: a positive natural that is at least `2` cannot equal `1`. -/
private theorem positiveNat_ne_one_of_two_le {n : ℕ+} (hn : 2 ≤ n) :
    n ≠ 1 := by
  -- Compare the coercions to `ℕ`, where `omega` can read the lower bound.
  intro h
  have hn_nat : 2 ≤ (n : ℕ) := by
    exact_mod_cast hn
  have h1 : (n : ℕ) = 1 := congrArg Subtype.val h
  omega

/-- The subgradient projector associated with the Example 16.22 weighted even-power series and the
zero sublevel threshold. -/
noncomputable def weighted_even_power_subgradient_projector : L2pos → L2pos :=
  continuousConvexSubgradientProjector positiveNatWeightedEvenPowerSeriesReal 0
    positiveNatWeightedEvenPowerSeriesReal_continuous
    positiveNatWeightedEvenPowerSeriesReal_convexOn
    positiveNatWeightedEvenPowerSeriesReal_lowerLevelSet_zero_nonempty
    positiveNatWeightedEvenPowerSeriesMinimalNormSelection

/-- Helper for Example 29.48: the standard basis of `ℓ²(ℕ+, ℝ)` is orthonormal. -/
private theorem positiveNatStandardUnitVector_orthonormal :
    Orthonormal ℝ positive_nat_standard_unit_vector := by
  -- Reduce orthonormality to the coordinate formula for `lp.single`.
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [positive_nat_standard_unit_vector]
  · simp [positive_nat_standard_unit_vector, lp.inner_single_left, hij]

/-- Helper for Example 29.48: the reindexed tail `e_{n+2}` is still orthonormal. -/
private theorem positiveNatStandardUnitVectorTailOrthonormal :
    Orthonormal ℝ (fun n : ℕ ↦ positive_nat_standard_unit_vector ⟨n + 2, by omega⟩) := by
  -- Compose the orthonormal basis with the injective tail index map.
  refine positiveNatStandardUnitVector_orthonormal.comp (fun n ↦ ⟨n + 2, by omega⟩) ?_
  intro m n hmn
  exact Nat.add_right_cancel (congrArg Subtype.val hmn)

/-- Helper for Example 29.48: each weighted coordinate term is bounded above by the full series. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_ge_coordinate_term
    (x : L2pos) (n : ℕ+) :
    (n : ℝ) * (x n) ^ (2 * (n : ℕ)) ≤ positiveNatWeightedEvenPowerSeriesReal x := by
  have hnat : ¬ Finite ℕ+ := by
    intro hfinite
    exact hfinite.false
  have hcoord :
      ((((n : ℝ) * (x n) ^ (2 * (n : ℕ)) : ℝ) : EReal)) ≤
        (positiveNatWeightedEvenPowerSeries x : EReal) := by
    -- Compare the full family sum with the singleton partial sum supported at `n`.
    rw [positiveNatWeightedEvenPowerSeries_apply]
    rw [familySum_eq_iSup_nonemptyFinitePartialSums _ hnat]
    let J₀ : {s : Finset ℕ+ // s.Nonempty} := ⟨{n}, by simp⟩
    have hJ₀ :
        Finset.sum (J₀ : Finset ℕ+)
            (fun i ↦ (((i : ℝ) * (x i) ^ (2 * (i : ℕ)) : ℝ) : EReal)) ≤
          ⨆ J : {s : Finset ℕ+ // s.Nonempty},
            Finset.sum (J : Finset ℕ+)
              (fun i ↦ (((i : ℝ) * (x i) ^ (2 * (i : ℕ)) : ℝ) : EReal)) :=
      le_iSup
        (fun J : {s : Finset ℕ+ // s.Nonempty} ↦
          Finset.sum (J : Finset ℕ+)
            (fun i ↦ (((i : ℝ) * (x i) ^ (2 * (i : ℕ)) : ℝ) : EReal)))
        J₀
    simpa [J₀] using hJ₀
  -- Coercing back to `ℝ` recovers the claimed coordinate domination.
  rw [← positiveNatWeightedEvenPowerSeriesReal_toEReal x] at hcoord
  exact_mod_cast hcoord

/-- Helper for Example 29.48: the weighted even-power series vanishes only at the origin. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_eq_zero_iff
    (x : L2pos) :
    positiveNatWeightedEvenPowerSeriesReal x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    ext n
    have hcoord_nonneg : 0 ≤ (n : ℝ) * (x n) ^ (2 * (n : ℕ)) := by
      exact positiveNatWeightedEvenPowerCoordinate_nonneg n (x n)
    have hcoord_le_zero :
        (n : ℝ) * (x n) ^ (2 * (n : ℕ)) ≤ 0 := by
      simpa [hx] using positiveNatWeightedEvenPowerSeriesReal_ge_coordinate_term x n
    have hcoord_zero :
        (n : ℝ) * (x n) ^ (2 * (n : ℕ)) = 0 :=
      le_antisymm hcoord_le_zero hcoord_nonneg
    have hpow_zero : (x n) ^ (2 * (n : ℕ)) = 0 := by
      have hn_ne : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt n.2)
      exact (mul_eq_zero.mp hcoord_zero).resolve_left hn_ne
    have hsq_zero : (x n) ^ 2 = 0 := by
      simpa [pow_mul] using hpow_zero
    have hx_abs_sq : |x n| ^ 2 = 0 := by
      simpa [sq_abs] using hsq_zero
    have hx_abs : |x n| = 0 := by
      exact eq_zero_of_pow_eq_zero hx_abs_sq
    exact abs_eq_zero.mp hx_abs
  · intro hx
    subst hx
    simpa [positiveNatWeightedEvenPowerSeriesReal] using
      congrArg EReal.toReal positiveNatWeightedEvenPowerSeries_zero

/-- Helper for Example 29.48: every nonzero point of the weighted even-power series fails to be a
global minimizer. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_not_mem_argmin_of_ne_zero
    {x : L2pos} (hx : x ≠ 0) :
    x ∉ Argmin positiveNatWeightedEvenPowerSeries.asEReal := by
  intro hxmin
  rw [mem_argmin_iff, isMinOn_univ_iff] at hxmin
  have hfx_pos : 0 < positiveNatWeightedEvenPowerSeriesReal x := by
    have hnonneg : 0 ≤ positiveNatWeightedEvenPowerSeriesReal x := by
      exact
        (positiveNatWeightedEvenPowerCoordinate_nonneg 1 (x 1)).trans
          (positiveNatWeightedEvenPowerSeriesReal_ge_coordinate_term x 1)
    have hne : positiveNatWeightedEvenPowerSeriesReal x ≠ 0 := by
      intro hzero
      exact hx ((positiveNatWeightedEvenPowerSeriesReal_eq_zero_iff x).mp hzero)
    exact lt_of_le_of_ne hnonneg hne.symm
  have hmin := hxmin 0
  have hlt :
      (0 : EReal) < (positiveNatWeightedEvenPowerSeries x : EReal) := by
    rw [← positiveNatWeightedEvenPowerSeriesReal_toEReal x]
    exact_mod_cast hfx_pos
  have hnotle :
      ¬ (positiveNatWeightedEvenPowerSeries x : EReal) ≤
        (positiveNatWeightedEvenPowerSeries 0 : EReal) := by
    rw [positiveNatWeightedEvenPowerSeries_zero]
    exact not_le_of_gt hlt
  exact hnotle hmin

/-- Helper for Example 29.48: finite real sums commute with coercion to `EReal`. -/
private theorem finset_sum_coe_real_ereal {ι : Type*} (s : Finset ι) (r : ι → ℝ) :
    (((Finset.sum s r : ℝ)) : EReal) = Finset.sum s (fun i ↦ ((r i : ℝ) : EReal)) := by
  classical
  -- Induct on the finite set and use that `EReal` coercion preserves real addition.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    simp [Finset.sum_insert, ha, hs, EReal.coe_add]

/-- Helper for Example 29.48: a finitely supported point is evaluated by summing exactly its
nonzero weighted coordinates. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_eq_sum_of_support
    (x : L2pos) (s : Finset ℕ+) (hs : s.Nonempty)
    (hsupp : ∀ i : ℕ+, x i ≠ 0 → i ∈ s) :
    positiveNatWeightedEvenPowerSeriesReal x =
      Finset.sum s (fun i ↦ (i : ℝ) * (x i) ^ (2 * (i : ℕ))) := by
  classical
  let term : ℕ+ → EReal := fun i ↦ (((i : ℝ) * (x i) ^ (2 * (i : ℕ)) : ℝ) : EReal)
  have hnat : ¬ Finite ℕ+ := by
    intro hfinite
    exact hfinite.false
  have hzero_of_not_mem :
      ∀ i : ℕ+, i ∉ s → term i = 0 := by
    intro i hi
    have hxi : x i = 0 := by
      by_contra hxi
      exact hi (hsupp i hxi)
    simp [term, hxi]
  have hupper :
      (positiveNatWeightedEvenPowerSeries x : EReal) ≤
        Finset.sum s term := by
    -- Every finite partial sum is bounded by the support sum because the off-support terms vanish.
    rw [positiveNatWeightedEvenPowerSeries_apply]
    rw [familySum_eq_iSup_nonemptyFinitePartialSums _ hnat]
    refine iSup_le ?_
    intro J
    have hsubset : ((J : Finset ℕ+) ∩ s) ⊆ s := by
      intro i hi
      exact Finset.mem_of_mem_inter_right hi
    have hsum_eq :
        Finset.sum (J : Finset ℕ+) term = Finset.sum ((J : Finset ℕ+) ∩ s) term := by
      -- Restricting to the support discards only zero summands.
      symm
      refine Finset.sum_subset ?_ ?_
      · intro i hi
        exact Finset.mem_of_mem_inter_left hi
      · intro i hiJ hiJs
        exact hzero_of_not_mem i (by
          intro his
          exact hiJs (Finset.mem_inter.mpr ⟨hiJ, his⟩))
    have hle_inter :
        Finset.sum ((J : Finset ℕ+) ∩ s) term ≤ Finset.sum s term := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
      intro i hi hi_not
      exact by
        change (0 : EReal) ≤ (((i : ℝ) * (x i) ^ (2 * (i : ℕ)) : ℝ) : EReal)
        exact_mod_cast positiveNatWeightedEvenPowerCoordinate_nonneg i (x i)
    exact hsum_eq.le.trans hle_inter
  have hlower :
      Finset.sum s term ≤ (positiveNatWeightedEvenPowerSeries x : EReal) := by
    -- The support sum is one of the nonempty finite partial sums defining the family sum.
    rw [positiveNatWeightedEvenPowerSeries_apply]
    rw [familySum_eq_iSup_nonemptyFinitePartialSums _ hnat]
    exact le_iSup
      (fun J : {t : Finset ℕ+ // t.Nonempty} ↦ Finset.sum (J : Finset ℕ+) term)
      ⟨s, hs⟩
  have hEqEReal :
      (positiveNatWeightedEvenPowerSeries x : EReal) =
        ((Finset.sum s (fun i ↦ (i : ℝ) * (x i) ^ (2 * (i : ℕ))) : ℝ) : EReal) := by
    refine le_antisymm ?_ ?_
    · simpa [term, finset_sum_coe_real_ereal] using hupper
    · simpa [term, finset_sum_coe_real_ereal] using hlower
  -- Convert the `EReal` identity back to the real-valued representative.
  rw [← positiveNatWeightedEvenPowerSeriesReal_toEReal x] at hEqEReal
  exact EReal.coe_eq_coe_iff.mp hEqEReal

/-- Helper for Example 29.48: if `x` is supported on the single coordinate `a`, then the weighted
series has exactly one surviving term. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_eq_singleSupport
    {a : ℕ+} {x : L2pos}
    (hsupp : ∀ i : ℕ+, i ≠ a → x i = 0) :
    positiveNatWeightedEvenPowerSeriesReal x =
      (a : ℝ) * (x a) ^ (2 * (a : ℕ)) := by
  have hsupp_mem : ∀ i : ℕ+, x i ≠ 0 → i ∈ ({a} : Finset ℕ+) := by
    intro i hxi
    by_cases hia : i = a
    · simp [hia]
    · exact False.elim (hxi (hsupp i hia))
  -- Reduce the full series to the singleton support `{a}`.
  simpa using
    positiveNatWeightedEvenPowerSeriesReal_eq_sum_of_support x {a} (by simp) hsupp_mem

/-- Helper for Example 29.48: if `x` is supported on the two coordinates `a` and `b`, then the
weighted series is the sum of the two surviving weighted terms. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_eq_pairSupport
    {a b : ℕ+} (hab : a ≠ b) {x : L2pos}
    (hsupp : ∀ i : ℕ+, i ≠ a → i ≠ b → x i = 0) :
    positiveNatWeightedEvenPowerSeriesReal x =
      (a : ℝ) * (x a) ^ (2 * (a : ℕ)) + (b : ℝ) * (x b) ^ (2 * (b : ℕ)) := by
  have hsupp_mem : ∀ i : ℕ+, x i ≠ 0 → i ∈ ({a, b} : Finset ℕ+) := by
    intro i hxi
    by_cases hia : i = a
    · simp [hia]
    · by_cases hib : i = b
      · simp [hib]
      · exact False.elim (hxi (hsupp i hia hib))
  -- Reduce the family sum to the pair support `{a, b}`.
  simpa [hab, add_comm, add_left_comm, add_assoc] using
    positiveNatWeightedEvenPowerSeriesReal_eq_sum_of_support x {a, b} (by simp) hsupp_mem

/-- Helper for Example 29.48: if `x` is supported on the three coordinates `a`, `b`, and `c`,
then the weighted series is the sum of those three weighted terms. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_eq_tripleSupport
    {a b c : ℕ+} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {x : L2pos}
    (hsupp : ∀ i : ℕ+, i ≠ a → i ≠ b → i ≠ c → x i = 0) :
    positiveNatWeightedEvenPowerSeriesReal x =
      (a : ℝ) * (x a) ^ (2 * (a : ℕ)) +
        (b : ℝ) * (x b) ^ (2 * (b : ℕ)) +
          (c : ℝ) * (x c) ^ (2 * (c : ℕ)) := by
  have hsupp_mem : ∀ i : ℕ+, x i ≠ 0 → i ∈ ({a, b, c} : Finset ℕ+) := by
    intro i hxi
    by_cases hia : i = a
    · simp [hia]
    · by_cases hib : i = b
      · simp [hib]
      · by_cases hic : i = c
        · simp [hic]
        · exact False.elim (hxi (hsupp i hia hib hic))
  -- Reduce the family sum to the triple support `{a, b, c}`.
  simpa [hab, hac, hbc, add_assoc, add_left_comm, add_comm] using
    positiveNatWeightedEvenPowerSeriesReal_eq_sum_of_support x {a, b, c} (by simp) hsupp_mem

/-- Helper for Example 29.48: if `f(h)` dominates the affine form `a * h` and has derivative `d`
at `0`, then that affine slope must be `d`. -/
private theorem eq_derivAt_zero_of_mul_le
    {f : ℝ → ℝ} {a d : ℝ} (h0 : f 0 = 0) (hderiv : HasDerivAt f d 0)
    (hbound : ∀ h : ℝ, a * h ≤ f h) :
    a = d := by
  have hright :
      Tendsto (fun h : ℝ ↦ h⁻¹ * (f h - f 0)) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    -- The right-hand slopes converge to the derivative at `0`.
    simpa using hderiv.tendsto_slope_zero_right
  have hleft :
      Tendsto (fun h : ℝ ↦ h⁻¹ * (f h - f 0)) (𝓝[<] (0 : ℝ)) (𝓝 d) := by
    -- The left-hand slopes converge to the same derivative.
    simpa using hderiv.tendsto_slope_zero_left
  have hright_bound :
      ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), a ≤ h⁻¹ * (f h - f 0) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hdiv : a ≤ f h / h := (le_div_iff₀ hh).2 (hbound h)
    simpa [h0, div_eq_mul_inv, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hleft_bound :
      ∀ᶠ h : ℝ in 𝓝[<] (0 : ℝ), h⁻¹ * (f h - f 0) ≤ a := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hdiv : f h / h ≤ a := (div_le_iff_of_neg hh).2 (hbound h)
    simpa [h0, div_eq_mul_inv, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have ha_le_d : a ≤ d :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hright hright_bound
  have hd_le_a : d ≤ a :=
    le_of_tendsto_of_tendsto hleft tendsto_const_nhds hleft_bound
  exact le_antisymm ha_le_d hd_le_a

/-- Helper for Example 29.48: every nonempty finite partial sum of the weighted series is bounded
above by the full series. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_ge_finset_sum
    (x : L2pos) (s : Finset ℕ+) (hs : s.Nonempty) :
    Finset.sum s (fun i ↦ (i : ℝ) * (x i) ^ (2 * (i : ℕ))) ≤
      positiveNatWeightedEvenPowerSeriesReal x := by
  have hnat : ¬ Finite ℕ+ := by
    intro hfinite
    exact hfinite.false
  have hsum :
      (((Finset.sum s (fun i : ℕ+ ↦ ((i : ℝ) * (x i) ^ (2 * (i : ℕ)) : ℝ)) : ℝ) : EReal)) ≤
        (positiveNatWeightedEvenPowerSeries x : EReal) := by
    -- The chosen support sum is one of the nonempty finite partial sums defining the series.
    rw [positiveNatWeightedEvenPowerSeries_apply]
    rw [familySum_eq_iSup_nonemptyFinitePartialSums _ hnat]
    simpa [finset_sum_coe_real_ereal] using
      (le_iSup
        (fun J : {t : Finset ℕ+ // t.Nonempty} ↦
          Finset.sum (J : Finset ℕ+)
            (fun i ↦ (((i : ℝ) * (x i) ^ (2 * (i : ℕ)) : ℝ) : EReal)))
        ⟨s, hs⟩)
  -- Return to the real-valued representative of the series.
  rw [← positiveNatWeightedEvenPowerSeriesReal_toEReal x] at hsum
  exact_mod_cast hsum

/-- Helper for Example 29.48: the real representative of a nonnegative `toEReal` coordinate
function is the original coordinate function. -/
private theorem positiveNatWeightedEvenPowerCoordinate_toReal_eq
    (n : ℕ+) :
    (fun t : ℝ ↦ (((positiveNatWeightedEvenPowerCoordinate n).toEReal t : EReal).toReal)) =
      positiveNatWeightedEvenPowerCoordinate n := by
  funext t
  -- The coordinate function is nonnegative, so `toReal ∘ toEReal` is the identity on its values.
  simpa [positiveNatWeightedEvenPowerCoordinate_apply, Function.toEReal_apply] using
    (EReal.toReal_coe ((n : ℝ) * t ^ (2 * (n : ℕ))))

/-- Helper for Example 29.48: the `n`th weighted coordinate has derivative `2 n²` at `1`. -/
private theorem hasDerivAt_positiveNatWeightedEvenPowerCoordinate_one
    (n : ℕ+) :
    HasDerivAt (positiveNatWeightedEvenPowerCoordinate n) (2 * (n : ℝ) ^ 2) 1 := by
  -- Differentiate the monomial `t ↦ n * t^(2n)` and simplify the resulting coefficient at `1`.
  convert HasDerivAt.const_mul (n : ℝ) (hasDerivAt_pow (2 * (n : ℕ)) (1 : ℝ)) using 1
  norm_num [pow_two, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Example 29.48: the `n`th weighted coordinate has derivative `0` at `0`. -/
private theorem hasDerivAt_positiveNatWeightedEvenPowerCoordinate_zero
    (n : ℕ+) :
    HasDerivAt (positiveNatWeightedEvenPowerCoordinate n) 0 0 := by
  -- The monomial derivative vanishes at `0` because the remaining power is still positive.
  convert HasDerivAt.const_mul (n : ℝ) (hasDerivAt_pow (2 * (n : ℕ)) (0 : ℝ)) using 1
  have hpos : 0 < 2 * (n : ℕ) - 1 := by
    have hn : 1 ≤ (n : ℕ) := Nat.succ_le_of_lt n.2
    omega
  simp [hpos.ne']

/-- Helper for Example 29.48: away from the active coordinates `{1, n, i}`, the perturbed sparse
point `e₁ + eₙ + h eᵢ` vanishes coordinatewise. -/
private theorem weightedEvenPowerCounterexamplePoint_add_single_apply_zero_of_ne
    {n i j : ℕ+} {h : ℝ} (hj1 : j ≠ 1) (hjn : j ≠ n) (hji : j ≠ i) :
    ((weighted_even_power_counterexample_points n + lp.single 2 i h : L2pos) j) = 0 := by
  -- Evaluate the three sparse summands coordinatewise and discard the inactive indices.
  change
    (positive_nat_standard_unit_vector 1 j + positive_nat_standard_unit_vector n j) +
        (lp.single 2 i h : L2pos) j = 0
  simp [positive_nat_standard_unit_vector, hj1, hjn, hji]

/-- Helper for Example 29.48: away from the active coordinates `{1, i}`, the perturbed first basis
vector `e₁ + h eᵢ` vanishes coordinatewise. -/
private theorem weightedEvenPowerFirstBasis_add_single_apply_zero_of_ne
    {i j : ℕ+} {h : ℝ} (hj1 : j ≠ 1) (hji : j ≠ i) :
    ((positive_nat_standard_unit_vector 1 + lp.single 2 i h : L2pos) j) = 0 := by
  -- Evaluate the two sparse summands coordinatewise and discard the inactive indices.
  change positive_nat_standard_unit_vector 1 j + (lp.single 2 i h : L2pos) j = 0
  simp [positive_nat_standard_unit_vector, hj1, hji]

/-- Helper for Example 29.48: the sparse point `e₁ + eₙ` has weighted value `1 + n`. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint
    {n : ℕ+} (hn : 2 ≤ n) :
    positiveNatWeightedEvenPowerSeriesReal (weighted_even_power_counterexample_points n) =
      1 + n := by
  have h1n : 1 ≠ n := (positiveNat_ne_one_of_two_le hn).symm
  have hsupp :
      ∀ i : ℕ+, i ≠ 1 → i ≠ n → weighted_even_power_counterexample_points n i = 0 := by
    intro i hi1 hin
    -- Only the first and `n`th coordinates survive in `e₁ + eₙ`.
    change positive_nat_standard_unit_vector 1 i + positive_nat_standard_unit_vector n i = 0
    simp [positive_nat_standard_unit_vector, hi1, hin]
  have hcoord1 : weighted_even_power_counterexample_points n 1 = 1 := by
    change positive_nat_standard_unit_vector 1 1 + positive_nat_standard_unit_vector n 1 = 1
    simp [positive_nat_standard_unit_vector, h1n]
  have hcoordn : weighted_even_power_counterexample_points n n = 1 := by
    change positive_nat_standard_unit_vector 1 n + positive_nat_standard_unit_vector n n = 1
    simp [positive_nat_standard_unit_vector, h1n]
  -- Reduce the series to the pair support `{1, n}` and simplify the surviving coordinates.
  calc
    positiveNatWeightedEvenPowerSeriesReal (weighted_even_power_counterexample_points n) =
        (1 : ℝ) * (weighted_even_power_counterexample_points n 1) ^ (2 * (1 : ℕ)) +
          (n : ℝ) * (weighted_even_power_counterexample_points n n) ^ (2 * (n : ℕ)) := by
            simpa using
              positiveNatWeightedEvenPowerSeriesReal_eq_pairSupport h1n hsupp
    _ = (1 : ℝ) * (1 : ℝ) ^ (2 * (1 : ℕ)) + (n : ℝ) * (1 : ℝ) ^ (2 * (n : ℕ)) := by
          rw [hcoord1, hcoordn]
    _ = 1 + n := by
          simp

/-- Helper for Example 29.48: perturbing the first coordinate of `e₁ + eₙ` changes only the square
term at index `1`. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint_add_single_first
    {n : ℕ+} (hn : 2 ≤ n) (h : ℝ) :
    positiveNatWeightedEvenPowerSeriesReal
        (weighted_even_power_counterexample_points n + lp.single 2 1 h) =
      (1 + h) ^ 2 + n := by
  have h1n : 1 ≠ n := (positiveNat_ne_one_of_two_le hn).symm
  have hsupp :
      ∀ i : ℕ+, i ≠ 1 → i ≠ n →
        ((weighted_even_power_counterexample_points n + lp.single 2 1 h : L2pos) i) = 0 := by
    intro i hi1 hin
    -- The perturbation is still supported on `{1, n}`.
    simpa using
      (weightedEvenPowerCounterexamplePoint_add_single_apply_zero_of_ne
        (h := h) hi1 hin hi1)
  have hcoord1 :
      ((weighted_even_power_counterexample_points n + lp.single 2 1 h : L2pos) 1) = 1 + h := by
    change
      (positive_nat_standard_unit_vector 1 1 + positive_nat_standard_unit_vector n 1) +
          (lp.single 2 1 h : L2pos) 1 = 1 + h
    simp [positive_nat_standard_unit_vector, h1n]
  have hcoordn :
      ((weighted_even_power_counterexample_points n + lp.single 2 1 h : L2pos) n) = 1 := by
    change
      (positive_nat_standard_unit_vector 1 n + positive_nat_standard_unit_vector n n) +
          (lp.single 2 1 h : L2pos) n = 1
    simp [positive_nat_standard_unit_vector, h1n]
  -- Collapse the perturbed point to the two active coordinates.
  calc
    positiveNatWeightedEvenPowerSeriesReal
        (weighted_even_power_counterexample_points n + lp.single 2 1 h) =
        (1 : ℝ) *
            (((weighted_even_power_counterexample_points n + lp.single 2 1 h : L2pos) 1)) ^
              (2 * (1 : ℕ)) +
          (n : ℝ) *
            (((weighted_even_power_counterexample_points n + lp.single 2 1 h : L2pos) n)) ^
              (2 * (n : ℕ)) := by
            simpa using
              positiveNatWeightedEvenPowerSeriesReal_eq_pairSupport h1n hsupp
    _ = (1 : ℝ) * (1 + h) ^ (2 * (1 : ℕ)) + (n : ℝ) * (1 : ℝ) ^ (2 * (n : ℕ)) := by
          rw [hcoord1, hcoordn]
    _ = (1 + h) ^ 2 + n := by
          simp

/-- Helper for Example 29.48: perturbing the active `n`th coordinate of `e₁ + eₙ` changes only the
`n`th weighted even-power term. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint_add_single_active
    {n : ℕ+} (hn : 2 ≤ n) (h : ℝ) :
    positiveNatWeightedEvenPowerSeriesReal
        (weighted_even_power_counterexample_points n + lp.single 2 n h) =
      1 + (n : ℝ) * (1 + h) ^ (2 * (n : ℕ)) := by
  have h1n : 1 ≠ n := (positiveNat_ne_one_of_two_le hn).symm
  have hsupp :
      ∀ i : ℕ+, i ≠ 1 → i ≠ n →
        ((weighted_even_power_counterexample_points n + lp.single 2 n h : L2pos) i) = 0 := by
    intro i hi1 hin
    -- The perturbation remains supported on `{1, n}`.
    simpa using
      (weightedEvenPowerCounterexamplePoint_add_single_apply_zero_of_ne
        (h := h) hi1 hin hin)
  have hcoord1 :
      ((weighted_even_power_counterexample_points n + lp.single 2 n h : L2pos) 1) = 1 := by
    change
      (positive_nat_standard_unit_vector 1 1 + positive_nat_standard_unit_vector n 1) +
          (lp.single 2 n h : L2pos) 1 = 1
    simp [positive_nat_standard_unit_vector, h1n]
  have hcoordn :
      ((weighted_even_power_counterexample_points n + lp.single 2 n h : L2pos) n) = 1 + h := by
    change
      (positive_nat_standard_unit_vector 1 n + positive_nat_standard_unit_vector n n) +
          (lp.single 2 n h : L2pos) n = 1 + h
    simp [positive_nat_standard_unit_vector, h1n]
  -- Collapse the perturbed point to the pair support `{1, n}`.
  calc
    positiveNatWeightedEvenPowerSeriesReal
        (weighted_even_power_counterexample_points n + lp.single 2 n h) =
        (1 : ℝ) *
            (((weighted_even_power_counterexample_points n + lp.single 2 n h : L2pos) 1)) ^
              (2 * (1 : ℕ)) +
          (n : ℝ) *
            (((weighted_even_power_counterexample_points n + lp.single 2 n h : L2pos) n)) ^
              (2 * (n : ℕ)) := by
            simpa using
              positiveNatWeightedEvenPowerSeriesReal_eq_pairSupport h1n hsupp
    _ = (1 : ℝ) * (1 : ℝ) ^ (2 * (1 : ℕ)) + (n : ℝ) * (1 + h) ^ (2 * (n : ℕ)) := by
          rw [hcoord1, hcoordn]
    _ = 1 + (n : ℝ) * (1 + h) ^ (2 * (n : ℕ)) := by
          simp

/-- Helper for Example 29.48: perturbing any inactive coordinate of `e₁ + eₙ` adds only the
corresponding weighted even-power term. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint_add_single_other
    {n i : ℕ+} (hn : 2 ≤ n) (hi1 : i ≠ 1) (hin : i ≠ n) (h : ℝ) :
    positiveNatWeightedEvenPowerSeriesReal
        (weighted_even_power_counterexample_points n + lp.single 2 i h) =
      1 + n + (i : ℝ) * h ^ (2 * (i : ℕ)) := by
  have h1n : 1 ≠ n := (positiveNat_ne_one_of_two_le hn).symm
  have h1i : 1 ≠ i := hi1.symm
  have hni : n ≠ i := hin.symm
  have hsupp :
      ∀ j : ℕ+, j ≠ 1 → j ≠ n → j ≠ i →
        ((weighted_even_power_counterexample_points n + lp.single 2 i h : L2pos) j) = 0 := by
    intro j hj1 hjn hji
    -- Only the coordinates `{1, n, i}` remain after the inactive perturbation.
    simpa using
      (weightedEvenPowerCounterexamplePoint_add_single_apply_zero_of_ne
        (h := h) hj1 hjn hji)
  have hcoord1 :
      ((weighted_even_power_counterexample_points n + lp.single 2 i h : L2pos) 1) = 1 := by
    change
      (positive_nat_standard_unit_vector 1 1 + positive_nat_standard_unit_vector n 1) +
          (lp.single 2 i h : L2pos) 1 = 1
    simp [positive_nat_standard_unit_vector, h1n, hi1]
  have hcoordn :
      ((weighted_even_power_counterexample_points n + lp.single 2 i h : L2pos) n) = 1 := by
    change
      (positive_nat_standard_unit_vector 1 n + positive_nat_standard_unit_vector n n) +
          (lp.single 2 i h : L2pos) n = 1
    simp [positive_nat_standard_unit_vector, h1n, hin]
  have hcoordi :
      ((weighted_even_power_counterexample_points n + lp.single 2 i h : L2pos) i) = h := by
    change
      (positive_nat_standard_unit_vector 1 i + positive_nat_standard_unit_vector n i) +
          (lp.single 2 i h : L2pos) i = h
    simp [positive_nat_standard_unit_vector, hi1, hin]
  -- Collapse the perturbed point to the triple support `{1, n, i}`.
  calc
    positiveNatWeightedEvenPowerSeriesReal
        (weighted_even_power_counterexample_points n + lp.single 2 i h) =
        (1 : ℝ) *
            (((weighted_even_power_counterexample_points n + lp.single 2 i h : L2pos) 1)) ^
              (2 * (1 : ℕ)) +
          (n : ℝ) *
            (((weighted_even_power_counterexample_points n + lp.single 2 i h : L2pos) n)) ^
              (2 * (n : ℕ)) +
            (i : ℝ) *
              (((weighted_even_power_counterexample_points n + lp.single 2 i h : L2pos) i)) ^
                (2 * (i : ℕ)) := by
            simpa using
              positiveNatWeightedEvenPowerSeriesReal_eq_tripleSupport h1n h1i hni hsupp
    _ = (1 : ℝ) * (1 : ℝ) ^ (2 * (1 : ℕ)) + (n : ℝ) * (1 : ℝ) ^ (2 * (n : ℕ)) +
          (i : ℝ) * h ^ (2 * (i : ℕ)) := by
          rw [hcoord1, hcoordn, hcoordi]
    _ = 1 + n + (i : ℝ) * h ^ (2 * (i : ℕ)) := by
          simp

/-- Helper for Example 29.48: the first basis vector has weighted value `1`. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_firstBasis :
    positiveNatWeightedEvenPowerSeriesReal (positive_nat_standard_unit_vector 1) = 1 := by
  have hbasis := positiveNatWeightedEvenPowerSeries_apply_basisVector 1
  -- Cast the basis-vector evaluation from `EReal` back to the real representative.
  simpa [positiveNatWeightedEvenPowerSeriesReal, positive_nat_standard_unit_vector] using
    congrArg EReal.toReal hbasis

/-- Helper for Example 29.48: perturbing the first coordinate of `e₁` yields the scalar square
value `(1 + h)^2`. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_firstBasis_add_single_first
    (h : ℝ) :
    positiveNatWeightedEvenPowerSeriesReal
        (positive_nat_standard_unit_vector 1 + lp.single 2 1 h) =
      (1 + h) ^ 2 := by
  have hsupp :
      ∀ i : ℕ+, i ≠ 1 →
        ((positive_nat_standard_unit_vector 1 + lp.single 2 1 h : L2pos) i) = 0 := by
    intro i hi1
    -- The first-coordinate perturbation still leaves only coordinate `1` active.
    simpa using
      (weightedEvenPowerFirstBasis_add_single_apply_zero_of_ne (h := h) hi1 hi1)
  have hcoord1 : ((positive_nat_standard_unit_vector 1 + lp.single 2 1 h : L2pos) 1) = 1 + h := by
    change positive_nat_standard_unit_vector 1 1 + (lp.single 2 1 h : L2pos) 1 = 1 + h
    simp [positive_nat_standard_unit_vector]
  -- Collapse the perturbed basis vector to its unique active coordinate.
  calc
    positiveNatWeightedEvenPowerSeriesReal
        (positive_nat_standard_unit_vector 1 + lp.single 2 1 h) =
        (1 : ℝ) * (((positive_nat_standard_unit_vector 1 + lp.single 2 1 h : L2pos) 1)) ^
          (2 * (1 : ℕ)) := by
            simpa using positiveNatWeightedEvenPowerSeriesReal_eq_singleSupport hsupp
    _ = (1 : ℝ) * (1 + h) ^ (2 * (1 : ℕ)) := by
          rw [hcoord1]
    _ = (1 + h) ^ 2 := by
          simp

/-- Helper for Example 29.48: perturbing an inactive coordinate of `e₁` adds only that weighted
even-power term. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_firstBasis_add_single_other
    {i : ℕ+} (hi1 : i ≠ 1) (h : ℝ) :
    positiveNatWeightedEvenPowerSeriesReal
        (positive_nat_standard_unit_vector 1 + lp.single 2 i h) =
      1 + (i : ℝ) * h ^ (2 * (i : ℕ)) := by
  have h1i : 1 ≠ i := hi1.symm
  have hsupp :
      ∀ j : ℕ+, j ≠ 1 → j ≠ i →
        ((positive_nat_standard_unit_vector 1 + lp.single 2 i h : L2pos) j) = 0 := by
    intro j hj1 hji
    -- The inactive perturbation is supported on `{1, i}`.
    simpa using
      (weightedEvenPowerFirstBasis_add_single_apply_zero_of_ne (h := h) hj1 hji)
  have hcoord1 : ((positive_nat_standard_unit_vector 1 + lp.single 2 i h : L2pos) 1) = 1 := by
    change positive_nat_standard_unit_vector 1 1 + (lp.single 2 i h : L2pos) 1 = 1
    simp [positive_nat_standard_unit_vector, hi1]
  have hcoordi : ((positive_nat_standard_unit_vector 1 + lp.single 2 i h : L2pos) i) = h := by
    change positive_nat_standard_unit_vector 1 i + (lp.single 2 i h : L2pos) i = h
    simp [positive_nat_standard_unit_vector, hi1]
  -- Collapse the perturbed basis vector to the pair support `{1, i}`.
  calc
    positiveNatWeightedEvenPowerSeriesReal
        (positive_nat_standard_unit_vector 1 + lp.single 2 i h) =
        (1 : ℝ) * (((positive_nat_standard_unit_vector 1 + lp.single 2 i h : L2pos) 1)) ^
            (2 * (1 : ℕ)) +
          (i : ℝ) * (((positive_nat_standard_unit_vector 1 + lp.single 2 i h : L2pos) i)) ^
            (2 * (i : ℕ)) := by
            simpa using
              positiveNatWeightedEvenPowerSeriesReal_eq_pairSupport h1i hsupp
    _ = (1 : ℝ) * (1 : ℝ) ^ (2 * (1 : ℕ)) + (i : ℝ) * h ^ (2 * (i : ℕ)) := by
          rw [hcoord1, hcoordi]
    _ = 1 + (i : ℝ) * h ^ (2 * (i : ℕ)) := by
          simp

/-- Helper for Example 29.48: a subgradient controls the scalar defect created by perturbing one
coordinate. -/
private theorem positiveNatWeightedEvenPowerSeriesReal_singleCoordinateSubgradient_le
    {x u : L2pos} (hu : u ∈ (∂ positiveNatWeightedEvenPowerSeriesReal.toEReal) x)
    (i : ℕ+) (h : ℝ) :
    h * u i ≤
      positiveNatWeightedEvenPowerSeriesReal (x + lp.single 2 i h) -
        positiveNatWeightedEvenPowerSeriesReal x := by
  have hxeff : x ∈ effectiveDomain positiveNatWeightedEvenPowerSeriesReal.toEReal := by
    -- The real-valued representative has the same effective domain as the original series.
    rw [positiveNatWeightedEvenPowerSeriesReal_toEReal_fun,
      positiveNatWeightedEvenPowerSeries_effectiveDomain_eq_univ]
    simp
  have hyeff :
      x + lp.single 2 i h ∈ effectiveDomain positiveNatWeightedEvenPowerSeriesReal.toEReal := by
    -- The perturbed point also belongs to the full effective domain.
    rw [positiveNatWeightedEvenPowerSeriesReal_toEReal_fun,
      positiveNatWeightedEvenPowerSeries_effectiveDomain_eq_univ]
    simp
  have hsub := inner_le_sub_of_mem_subdifferential_real hxeff hyeff hu
  have hdisp : x + lp.single 2 i h - x = (lp.single 2 i h : L2pos) := by
    ext j
    simp [sub_eq_add_neg, add_left_comm, add_comm]
  have hinner : ⟪x + lp.single 2 i h - x, u⟫_ℝ = h * u i := by
    -- The displacement `x + h eᵢ - x` is exactly the single-coordinate vector `h eᵢ`.
    rw [hdisp, lp.inner_single_left]
    have hscalar : u i * h = h * u i := by ring
    simpa [RCLike.inner_apply] using hscalar
  -- Rewrite the ambient inequality through the single-coordinate inner-product formula.
  rw [hinner] at hsub
  simpa [positiveNatWeightedEvenPowerSeriesReal, Function.toEReal_apply] using hsub

/-- Helper for Example 29.48: the selected minimal-norm subgradient at `e₁` is `2 e₁`. -/
private theorem firstBasis_selectedSubgradient_eq :
    (positiveNatWeightedEvenPowerSeriesMinimalNormSelection
        ⟨positive_nat_standard_unit_vector 1,
          positiveNatWeightedEvenPowerSeriesReal_mem_subdifferential_dom
            (positive_nat_standard_unit_vector 1)⟩ : L2pos) =
      (2 : ℝ) • positive_nat_standard_unit_vector 1 := by
  let u : L2pos :=
    positiveNatWeightedEvenPowerSeriesMinimalNormSelection
      ⟨positive_nat_standard_unit_vector 1,
        positiveNatWeightedEvenPowerSeriesReal_mem_subdifferential_dom
          (positive_nat_standard_unit_vector 1)⟩
  have hu :
      u ∈ (∂ positiveNatWeightedEvenPowerSeriesReal.toEReal)
        (positive_nat_standard_unit_vector 1) := by
    -- The selected element lies in the subdifferential fiber by definition.
    simpa [u] using
      (selection_apply_mem positiveNatWeightedEvenPowerSeriesMinimalNormSelection
        ⟨positive_nat_standard_unit_vector 1,
          positiveNatWeightedEvenPowerSeriesReal_mem_subdifferential_dom
            (positive_nat_standard_unit_vector 1)⟩)
  have hu1 : u 1 = 2 := by
    let g : ℝ → ℝ := fun h ↦
      positiveNatWeightedEvenPowerSeriesReal
          (positive_nat_standard_unit_vector 1 + lp.single 2 1 h) -
        positiveNatWeightedEvenPowerSeriesReal (positive_nat_standard_unit_vector 1)
    have hg0 : g 0 = 0 := by
      -- The scalar defect vanishes at the base point.
      simp [g, positiveNatWeightedEvenPowerSeriesReal_firstBasis_add_single_first,
        positiveNatWeightedEvenPowerSeriesReal_firstBasis]
    have hgderiv : HasDerivAt g 2 0 := by
      -- The first-coordinate slice is exactly `(1 + h)^2 - 1`.
      have hpoly : g = fun h : ℝ ↦ (1 + h) ^ 2 - 1 := by
        funext h
        simp [g, positiveNatWeightedEvenPowerSeriesReal_firstBasis_add_single_first,
          positiveNatWeightedEvenPowerSeriesReal_firstBasis]
      rw [hpoly]
      simpa using ((((hasDerivAt_id 0).const_add 1).pow 2).sub_const (1 : ℝ))
    have hbound : ∀ h : ℝ, u 1 * h ≤ g h := by
      intro h
      -- The one-coordinate subgradient inequality gives the required scalar lower bound.
      simpa [g, mul_comm] using
        positiveNatWeightedEvenPowerSeriesReal_singleCoordinateSubgradient_le hu 1 h
    simpa [mul_comm] using eq_derivAt_zero_of_mul_le hg0 hgderiv hbound
  have huj_zero : ∀ {j : ℕ+}, j ≠ 1 → u j = 0 := by
    intro j hj1
    let g : ℝ → ℝ := fun h ↦
      positiveNatWeightedEvenPowerSeriesReal
          (positive_nat_standard_unit_vector 1 + lp.single 2 j h) -
        positiveNatWeightedEvenPowerSeriesReal (positive_nat_standard_unit_vector 1)
    have hg0 : g 0 = 0 := by
      -- The inactive scalar defect also vanishes at the base point.
      simp [g, positiveNatWeightedEvenPowerSeriesReal_firstBasis_add_single_other hj1,
        positiveNatWeightedEvenPowerSeriesReal_firstBasis]
    have hgderiv : HasDerivAt g 0 0 := by
      -- The inactive slice reduces to the coordinate monomial with derivative `0` at `0`.
      have hpoly : g = positiveNatWeightedEvenPowerCoordinate j := by
        funext h
        simp [g, positiveNatWeightedEvenPowerSeriesReal_firstBasis_add_single_other hj1,
          positiveNatWeightedEvenPowerSeriesReal_firstBasis,
          positiveNatWeightedEvenPowerCoordinate_apply]
      rw [hpoly]
      exact hasDerivAt_positiveNatWeightedEvenPowerCoordinate_zero j
    have hbound : ∀ h : ℝ, u j * h ≤ g h := by
      intro h
      -- Apply the one-coordinate subgradient inequality on the inactive coordinate `j`.
      simpa [g, mul_comm] using
        positiveNatWeightedEvenPowerSeriesReal_singleCoordinateSubgradient_le hu j h
    simpa [mul_comm] using eq_derivAt_zero_of_mul_le hg0 hgderiv hbound
  -- Extensionality reduces the vector identity to the active coordinate `1` and the inactive tail.
  ext j
  by_cases hj1 : j = 1
  · rw [hj1]
    change u 1 = (2 : ℝ) * positive_nat_standard_unit_vector 1 1
    rw [hu1]
    simp [positive_nat_standard_unit_vector]
  · change u j = ((2 : ℝ) • positive_nat_standard_unit_vector 1) j
    rw [huj_zero hj1]
    simp [positive_nat_standard_unit_vector, hj1]

/-- Helper for Example 29.48: the selected minimal-norm subgradient at `e₁ + eₙ` is the explicit
two-coordinate gradient from the source formula. -/
private theorem counterexamplePoint_selectedSubgradient_eq
    {n : ℕ+} (hn : 2 ≤ n) :
    (positiveNatWeightedEvenPowerSeriesMinimalNormSelection
        ⟨weighted_even_power_counterexample_points n,
          positiveNatWeightedEvenPowerSeriesReal_mem_subdifferential_dom
            (weighted_even_power_counterexample_points n)⟩ : L2pos) =
      (2 : ℝ) • positive_nat_standard_unit_vector 1 +
        ((2 * (n : ℝ) ^ 2 : ℝ) • positive_nat_standard_unit_vector n) := by
  let u : L2pos :=
    positiveNatWeightedEvenPowerSeriesMinimalNormSelection
      ⟨weighted_even_power_counterexample_points n,
        positiveNatWeightedEvenPowerSeriesReal_mem_subdifferential_dom
          (weighted_even_power_counterexample_points n)⟩
  have hu :
      u ∈ (∂ positiveNatWeightedEvenPowerSeriesReal.toEReal)
        (weighted_even_power_counterexample_points n) := by
    -- The selected element lies in the subdifferential fiber at `e₁ + eₙ`.
    simpa [u] using
      (selection_apply_mem positiveNatWeightedEvenPowerSeriesMinimalNormSelection
        ⟨weighted_even_power_counterexample_points n,
          positiveNatWeightedEvenPowerSeriesReal_mem_subdifferential_dom
            (weighted_even_power_counterexample_points n)⟩)
  have h1n : 1 ≠ n := (positiveNat_ne_one_of_two_le hn).symm
  have hu1 : u 1 = 2 := by
    let g : ℝ → ℝ := fun h ↦
      positiveNatWeightedEvenPowerSeriesReal
          (weighted_even_power_counterexample_points n + lp.single 2 1 h) -
        positiveNatWeightedEvenPowerSeriesReal (weighted_even_power_counterexample_points n)
    have hg0 : g 0 = 0 := by
      -- The first-coordinate defect vanishes at the base point.
      simp [g, positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint_add_single_first hn,
        positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint hn]
    have hgderiv : HasDerivAt g 2 0 := by
      -- The first-coordinate slice is still `(1 + h)^2 - 1`.
      have hpoly : g = fun h : ℝ ↦ (1 + h) ^ 2 - 1 := by
        funext h
        simp [g, positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint_add_single_first hn,
          positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint hn]
      rw [hpoly]
      simpa using ((((hasDerivAt_id 0).const_add 1).pow 2).sub_const (1 : ℝ))
    have hbound : ∀ h : ℝ, u 1 * h ≤ g h := by
      intro h
      -- The scalar subgradient inequality on coordinate `1` controls the first slice.
      simpa [g, mul_comm] using
        positiveNatWeightedEvenPowerSeriesReal_singleCoordinateSubgradient_le hu 1 h
    simpa [mul_comm] using eq_derivAt_zero_of_mul_le hg0 hgderiv hbound
  have hun : u n = 2 * (n : ℝ) ^ 2 := by
    let g : ℝ → ℝ := fun h ↦
      positiveNatWeightedEvenPowerSeriesReal
          (weighted_even_power_counterexample_points n + lp.single 2 n h) -
        positiveNatWeightedEvenPowerSeriesReal (weighted_even_power_counterexample_points n)
    have hg0 : g 0 = 0 := by
      -- The active `n`th-coordinate defect vanishes at the base point.
      simp [g, positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint_add_single_active hn,
        positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint hn]
    have hgderiv : HasDerivAt g (2 * (n : ℝ) ^ 2) 0 := by
      -- The active slice is the `n`th monomial translated by `1`.
      have hpoly :
          g = fun h : ℝ ↦ positiveNatWeightedEvenPowerCoordinate n (1 + h) - n := by
        funext h
        simp [g, positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint_add_single_active hn,
          positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint hn,
          positiveNatWeightedEvenPowerCoordinate_apply]
      rw [hpoly]
      have hone :
          HasDerivAt (positiveNatWeightedEvenPowerCoordinate n)
            (2 * (n : ℝ) ^ 2) ((1 : ℝ) + 0) := by
        simpa using hasDerivAt_positiveNatWeightedEvenPowerCoordinate_one n
      exact
        (hone.comp_const_add (1 : ℝ) (0 : ℝ)).sub_const (n : ℝ)
    have hbound : ∀ h : ℝ, u n * h ≤ g h := by
      intro h
      -- The scalar subgradient inequality on the active coordinate `n` gives the lower bound.
      simpa [g, mul_comm] using
        positiveNatWeightedEvenPowerSeriesReal_singleCoordinateSubgradient_le hu n h
    simpa [mul_comm] using eq_derivAt_zero_of_mul_le hg0 hgderiv hbound
  have huj_zero : ∀ {j : ℕ+}, j ≠ 1 → j ≠ n → u j = 0 := by
    intro j hj1 hjn
    let g : ℝ → ℝ := fun h ↦
      positiveNatWeightedEvenPowerSeriesReal
          (weighted_even_power_counterexample_points n + lp.single 2 j h) -
        positiveNatWeightedEvenPowerSeriesReal (weighted_even_power_counterexample_points n)
    have hg0 : g 0 = 0 := by
      -- The inactive scalar defect vanishes at the base point.
      simp [
        g,
        positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint_add_single_other hn hj1 hjn,
        positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint hn
      ]
    have hgderiv : HasDerivAt g 0 0 := by
      -- The inactive slice again reduces to the coordinate monomial at `0`.
      have hpoly : g = positiveNatWeightedEvenPowerCoordinate j := by
        funext h
        simp [
          g,
          positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint_add_single_other hn hj1 hjn,
          positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint hn,
          positiveNatWeightedEvenPowerCoordinate_apply
        ]
      rw [hpoly]
      exact hasDerivAt_positiveNatWeightedEvenPowerCoordinate_zero j
    have hbound : ∀ h : ℝ, u j * h ≤ g h := by
      intro h
      -- Apply the scalar subgradient inequality on the inactive coordinate `j`.
      simpa [g, mul_comm] using
        positiveNatWeightedEvenPowerSeriesReal_singleCoordinateSubgradient_le hu j h
    simpa [mul_comm] using eq_derivAt_zero_of_mul_le hg0 hgderiv hbound
  -- Compare the three coordinate regimes `{1}`, `{n}`, and the inactive complement.
  ext j
  by_cases hj1 : j = 1
  · rw [hj1]
    change u 1 =
      (2 : ℝ) * positive_nat_standard_unit_vector 1 1 +
        (2 * (n : ℝ) ^ 2 : ℝ) * positive_nat_standard_unit_vector n 1
    rw [hu1]
    simp [positive_nat_standard_unit_vector, h1n]
  · by_cases hjn : j = n
    · rw [hjn]
      change u n =
        (2 : ℝ) * positive_nat_standard_unit_vector 1 n +
          (2 * (n : ℝ) ^ 2 : ℝ) * positive_nat_standard_unit_vector n n
      rw [hun]
      simp [positive_nat_standard_unit_vector, h1n]
    · change u j =
        (2 : ℝ) * positive_nat_standard_unit_vector 1 j +
          (2 * (n : ℝ) ^ 2 : ℝ) * positive_nat_standard_unit_vector n j
      rw [huj_zero hj1 hjn]
      simp [positive_nat_standard_unit_vector, hj1, hjn]

/-- Helper for Example 29.48: the residual norm along the counterexample sequence is bounded by the
reciprocal comparison sequence `1 / (n + 2)`. -/
private theorem weightedEvenPowerCounterexampleResidualNorm_le_inv (m : ℕ) :
    ‖weighted_even_power_counterexample_sequence m -
        weighted_even_power_subgradient_projector
          (weighted_even_power_counterexample_sequence m)‖ ≤
      (1 : ℝ) / (m + 2 : ℝ) := by
  let n : ℕ+ := ⟨m + 2, by omega⟩
  let x : L2pos := weighted_even_power_counterexample_points n
  let u : L2pos :=
    positiveNatWeightedEvenPowerSeriesMinimalNormSelection
      ⟨x, positiveNatWeightedEvenPowerSeriesReal_mem_subdifferential_dom x⟩
  let α : ℝ := ((1 + n : ℝ) / (4 + 4 * (n : ℝ) ^ 4)) * 2
  let β : ℝ := ((1 + n : ℝ) / (4 + 4 * (n : ℝ) ^ 4)) * (2 * (n : ℝ) ^ 2)
  have hn : 2 ≤ n := by
    -- The reindexed counterexample uses the tail index `n = m + 2`.
    change 2 ≤ m + 2
    omega
  have h1n : 1 ≠ n := (positiveNat_ne_one_of_two_le hn).symm
  have hfx : positiveNatWeightedEvenPowerSeriesReal x = 1 + n := by
    simpa [x] using positiveNatWeightedEvenPowerSeriesReal_counterexamplePoint hn
  have hactive : 0 < positiveNatWeightedEvenPowerSeriesReal x := by
    rw [hfx]
    positivity
  have hu_eq :
      u = (2 : ℝ) • positive_nat_standard_unit_vector 1 +
        ((2 * (n : ℝ) ^ 2 : ℝ) • positive_nat_standard_unit_vector n) := by
    simpa [u, x] using counterexamplePoint_selectedSubgradient_eq hn
  have hbranch :
      weighted_even_power_subgradient_projector x =
        x + (((0 - positiveNatWeightedEvenPowerSeriesReal x) / (‖u‖ ^ 2)) • u) := by
    -- The counterexample point lies on the active projector branch.
    simpa [weighted_even_power_subgradient_projector, u, x,
      positiveNatWeightedEvenPowerSeriesReal_selectedSubgradient_eq] using
      (continuousConvexSubgradientProjector_apply_of_lt positiveNatWeightedEvenPowerSeriesReal 0
        positiveNatWeightedEvenPowerSeriesReal_continuous
        positiveNatWeightedEvenPowerSeriesReal_convexOn
        positiveNatWeightedEvenPowerSeriesReal_lowerLevelSet_zero_nonempty
        positiveNatWeightedEvenPowerSeriesMinimalNormSelection
        (x := x) hactive)
  have hnorm_sq : ‖u‖ ^ 2 = 4 + 4 * (n : ℝ) ^ 4 := by
    rw [hu_eq, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right,
      positiveNatStandardUnitVector_orthonormal.inner_eq_zero h1n, norm_smul, norm_smul,
      positiveNatStandardUnitVector_orthonormal.norm_eq_one 1,
      positiveNatStandardUnitVector_orthonormal.norm_eq_one n,
      Real.norm_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
      Real.norm_of_nonneg (by positivity : 0 ≤ (2 * (n : ℝ) ^ 2 : ℝ))]
    ring
  have hresidual :
      weighted_even_power_counterexample_sequence m -
          weighted_even_power_subgradient_projector
            (weighted_even_power_counterexample_sequence m) =
        α • positive_nat_standard_unit_vector 1 +
          β • positive_nat_standard_unit_vector n := by
    -- Rewrite the active projector formula and distribute the scalar over the explicit subgradient.
    calc
      weighted_even_power_counterexample_sequence m -
          weighted_even_power_subgradient_projector
            (weighted_even_power_counterexample_sequence m) =
          x - weighted_even_power_subgradient_projector x := by
            simp [weighted_even_power_counterexample_sequence, x, n]
      _ = -(((0 - positiveNatWeightedEvenPowerSeriesReal x) / (‖u‖ ^ 2)) • u) := by
            rw [hbranch]
            abel
      _ = α • positive_nat_standard_unit_vector 1 +
            β • positive_nat_standard_unit_vector n := by
            rw [hfx, hnorm_sq, hu_eq]
            rw [smul_add, smul_smul, smul_smul, neg_add]
            have hα :
                -(((0 - (1 + (n : ℝ))) / (4 + 4 * (n : ℝ) ^ 4)) * 2) = α := by
              simp [α]
              ring
            have hβ :
                -(((0 - (1 + (n : ℝ))) / (4 + 4 * (n : ℝ) ^ 4)) * (2 * (n : ℝ) ^ 2)) = β := by
              simp [β]
              ring
            have hα' :
                -((((-(n : ℝ)) + -1) / (4 + 4 * (n : ℝ) ^ 4)) * 2) = α := by
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hα
            have hβ' :
                -((((-(n : ℝ)) + -1) / (4 + 4 * (n : ℝ) ^ 4)) * (2 * (n : ℝ) ^ 2)) = β := by
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hβ
            have hαv :
                -((((0 - (1 + (n : ℝ))) / (4 + 4 * (n : ℝ) ^ 4)) * 2) •
                    positive_nat_standard_unit_vector 1) =
                  α • positive_nat_standard_unit_vector 1 := by
              simpa [neg_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                show
                  (-((((-(n : ℝ)) + -1) / (4 + 4 * (n : ℝ) ^ 4)) * 2)) •
                      positive_nat_standard_unit_vector 1 =
                    α • positive_nat_standard_unit_vector 1 by
                  rw [hα']
            have hβv :
                -((((0 - (1 + (n : ℝ))) / (4 + 4 * (n : ℝ) ^ 4)) * (2 * (n : ℝ) ^ 2)) •
                    positive_nat_standard_unit_vector n) =
                  β • positive_nat_standard_unit_vector n := by
              simpa [neg_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                show
                  (-((((-(n : ℝ)) + -1) / (4 + 4 * (n : ℝ) ^ 4)) * (2 * (n : ℝ) ^ 2))) •
                      positive_nat_standard_unit_vector n =
                    β • positive_nat_standard_unit_vector n by
                  rw [hβ']
            rw [hαv, hβv]
  have hα_nonneg : 0 ≤ α := by
    positivity
  have hβ_nonneg : 0 ≤ β := by
    positivity
  have hbound : α + β ≤ (1 : ℝ) / (n : ℝ) := by
    have hn_pos : 0 < (n : ℝ) := by positivity
    have hpoly : (n : ℝ) * (1 + n) * (1 + (n : ℝ) ^ 2) ≤ 2 * (1 + (n : ℝ) ^ 4) := by
      have hn_two : (2 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hn
      nlinarith
    have hsum :
        α + β =
          ((1 + n : ℝ) * (1 + (n : ℝ) ^ 2)) / (2 * (1 + (n : ℝ) ^ 4)) := by
      unfold α β
      field_simp
      ring
    rw [hsum]
    refine (le_div_iff₀ hn_pos).2 ?_
    have hden_pos : 0 < 2 * (1 + (n : ℝ) ^ 4) := by positivity
    calc
      ((1 + n : ℝ) * (1 + (n : ℝ) ^ 2)) / (2 * (1 + (n : ℝ) ^ 4)) * (n : ℝ)
          = ((1 + n : ℝ) * (1 + (n : ℝ) ^ 2) * (n : ℝ)) / (2 * (1 + (n : ℝ) ^ 4)) := by
              ring
      _ ≤ 1 := by
            refine (div_le_iff₀ hden_pos).2 ?_
            nlinarith [hpoly]
  calc
    ‖weighted_even_power_counterexample_sequence m -
        weighted_even_power_subgradient_projector
          (weighted_even_power_counterexample_sequence m)‖ =
        ‖α • positive_nat_standard_unit_vector 1 +
            β • positive_nat_standard_unit_vector n‖ := by
          rw [hresidual]
    _ ≤ ‖α • positive_nat_standard_unit_vector 1‖ +
          ‖β • positive_nat_standard_unit_vector n‖ := norm_add_le _ _
    _ = α + β := by
          rw [norm_smul, norm_smul,
            positiveNatStandardUnitVector_orthonormal.norm_eq_one 1,
            positiveNatStandardUnitVector_orthonormal.norm_eq_one n,
            Real.norm_of_nonneg hα_nonneg, Real.norm_of_nonneg hβ_nonneg]
          ring
    _ ≤ (1 : ℝ) / (n : ℝ) := hbound
    _ = (1 : ℝ) / (m + 2 : ℝ) := by
          simp [n]

/-- Preliminary for Example 29.48 (1): the reindexed textbook sequence `x_n = e_1 + e_{n+2}`
converges weakly to
`e_1` in `ℓ²(ℕ+, ℝ)`. -/
theorem weighted_even_power_counterexample_sequence_tendsto_weakly :
    Tendsto
      (fun n ↦ toWeakSpace ℝ L2pos (weighted_even_power_counterexample_sequence n))
      atTop
      (𝓝 (toWeakSpace ℝ L2pos (positive_nat_standard_unit_vector 1))) := by
  -- The tail basis sequence `e_{n+2}` is weakly null because it is orthonormal.
  have htail :
      Tendsto
        (fun n ↦ toWeakSpace ℝ L2pos (positive_nat_standard_unit_vector ⟨n + 2, by omega⟩))
        atTop
        (𝓝 (0 : WeakSpace ℝ L2pos)) :=
    orthonormal_sequence_tendsto_zero_weakly
      (fun n ↦ positive_nat_standard_unit_vector ⟨n + 2, by omega⟩)
      positiveNatStandardUnitVectorTailOrthonormal
  -- Adding the constant vector `e₁` transports the weak limit from `0` to `e₁`.
  have hconst :
      Tendsto
        (fun _ : ℕ ↦ toWeakSpace ℝ L2pos (positive_nat_standard_unit_vector 1))
        atTop
        (𝓝 (toWeakSpace ℝ L2pos (positive_nat_standard_unit_vector 1))) :=
    tendsto_const_nhds
  simpa [weighted_even_power_counterexample_sequence, weighted_even_power_counterexample_points,
    toWeakSpace] using hconst.add htail

/-- Example 29.48 (2): along the textbook counterexample sequence, the residual
`x_n - G x_n` of the weighted even-power subgradient projector tends strongly to `0`. -/
theorem weighted_even_power_subgradient_projector_residual_tendsto_zero :
    Tendsto
      (fun n ↦
        weighted_even_power_counterexample_sequence n -
          weighted_even_power_subgradient_projector
            (weighted_even_power_counterexample_sequence n))
      atTop
      (𝓝 (0 : L2pos)) := by
  -- Route correction: keep the downstream convergence argument and isolate the unresolved work in
  -- the explicit residual-norm estimate at the sparse counterexample points.
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have htail : Tendsto (fun n : ℕ ↦ (((n + 2 : ℕ) : ℝ)⁻¹ : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    simpa [Nat.cast_add, one_div] using (tendsto_inv_atTop_zero.comp hshift)
  refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ htail
  exact Eventually.of_forall fun n ↦ by
    simpa [one_div] using weightedEvenPowerCounterexampleResidualNorm_le_inv n

/-- Consequence of Example 29.48 (3): the projector images `G x_n` still converge weakly to `e_1`
along the
counterexample sequence. -/
theorem weighted_even_power_subgradient_projector_image_sequence_tendsto_weakly :
    Tendsto
      (fun n ↦
        toWeakSpace ℝ L2pos
          (weighted_even_power_subgradient_projector
            (weighted_even_power_counterexample_sequence n)))
      atTop
      (𝓝 (toWeakSpace ℝ L2pos (positive_nat_standard_unit_vector 1))) := by
  -- Send the strong residual convergence through the canonical map to `WeakSpace`.
  have hresWeak :
      Tendsto
        (fun n ↦
          toWeakSpace ℝ L2pos
            (weighted_even_power_counterexample_sequence n -
              weighted_even_power_subgradient_projector
                (weighted_even_power_counterexample_sequence n)))
        atTop
        (𝓝 (0 : WeakSpace ℝ L2pos)) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      (((toWeakSpaceCLM ℝ L2pos).continuous.tendsto (0 : L2pos)).comp
        weighted_even_power_subgradient_projector_residual_tendsto_zero)
  -- Rewrite `G xₙ` as `xₙ - (xₙ - G xₙ)` and subtract the weakly null residual.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, toWeakSpace] using
    weighted_even_power_counterexample_sequence_tendsto_weakly.sub hresWeak

/-- Consequence of Example 29.48 (4): the weighted even-power subgradient projector sends the first
standard unit
vector to half of itself. -/
theorem weighted_even_power_subgradient_projector_maps_first_basis_to_half :
    weighted_even_power_subgradient_projector (positive_nat_standard_unit_vector 1) =
      (1 / 2 : ℝ) • positive_nat_standard_unit_vector 1 := by
  -- Route correction: the only unresolved input is the selected subgradient at `e₁`; once that is
  -- fixed, the active projector branch is a short scalar calculation.
  have hactive :
      0 < positiveNatWeightedEvenPowerSeriesReal (positive_nat_standard_unit_vector 1) := by
    simp [positiveNatWeightedEvenPowerSeriesReal_firstBasis]
  let u : L2pos :=
    positiveNatWeightedEvenPowerSeriesMinimalNormSelection
      ⟨positive_nat_standard_unit_vector 1,
        positiveNatWeightedEvenPowerSeriesReal_mem_subdifferential_dom
          (positive_nat_standard_unit_vector 1)⟩
  have hu_eq : u = (2 : ℝ) • positive_nat_standard_unit_vector 1 := by
    simpa [u] using firstBasis_selectedSubgradient_eq
  have hbranch :
      weighted_even_power_subgradient_projector (positive_nat_standard_unit_vector 1) =
        positive_nat_standard_unit_vector 1 +
          (((0 - positiveNatWeightedEvenPowerSeriesReal (positive_nat_standard_unit_vector 1)) /
              (‖u‖ ^ 2)) • u) := by
    simpa [weighted_even_power_subgradient_projector, u,
      positiveNatWeightedEvenPowerSeriesReal_selectedSubgradient_eq] using
      (continuousConvexSubgradientProjector_apply_of_lt positiveNatWeightedEvenPowerSeriesReal 0
        positiveNatWeightedEvenPowerSeriesReal_continuous
        positiveNatWeightedEvenPowerSeriesReal_convexOn
        positiveNatWeightedEvenPowerSeriesReal_lowerLevelSet_zero_nonempty
        positiveNatWeightedEvenPowerSeriesMinimalNormSelection
        (x := positive_nat_standard_unit_vector 1) hactive)
  have hnorm_sq : ‖u‖ ^ 2 = 4 := by
    rw [hu_eq, norm_smul, positiveNatStandardUnitVector_orthonormal.norm_eq_one 1]
    norm_num
  calc
    weighted_even_power_subgradient_projector (positive_nat_standard_unit_vector 1) =
        positive_nat_standard_unit_vector 1 +
          (((0 - positiveNatWeightedEvenPowerSeriesReal (positive_nat_standard_unit_vector 1)) /
              (‖u‖ ^ 2)) • u) := hbranch
    _ =
        positive_nat_standard_unit_vector 1 +
          ((-(1 / 2 : ℝ)) • positive_nat_standard_unit_vector 1) := by
          rw [positiveNatWeightedEvenPowerSeriesReal_firstBasis, hnorm_sq, hu_eq]
          norm_num [smul_smul]
    _ = ((1 : ℝ) • positive_nat_standard_unit_vector 1 +
          (-(1 / 2 : ℝ)) • positive_nat_standard_unit_vector 1) := by
          rw [one_smul]
    _ = (((1 : ℝ) + (-(1 / 2 : ℝ))) • positive_nat_standard_unit_vector 1) := by
          rw [add_smul]
    _ = (1 / 2 : ℝ) • positive_nat_standard_unit_vector 1 := by
          norm_num

/-- Consequence of Example 29.48 (5): the fixed-point set of the weighted even-power subgradient
projector is the
singleton `{0}`. -/
theorem weighted_even_power_subgradient_projector_fixedPoints_eq_singleton_zero :
    Function.fixedPoints weighted_even_power_subgradient_projector = ({0} : Set L2pos) := by
  ext x
  constructor
  · intro hx
    rw [Function.mem_fixedPoints_iff] at hx
    by_cases hlevel : positiveNatWeightedEvenPowerSeriesReal x ≤ 0
    · -- On the nonpositive branch, the series must vanish because it is globally nonnegative.
      have hnonneg : 0 ≤ positiveNatWeightedEvenPowerSeriesReal x := by
        exact
          (positiveNatWeightedEvenPowerCoordinate_nonneg 1 (x 1)).trans
            (positiveNatWeightedEvenPowerSeriesReal_ge_coordinate_term x 1)
      have hzero : positiveNatWeightedEvenPowerSeriesReal x = 0 :=
        le_antisymm hlevel hnonneg
      rw [Set.mem_singleton_iff]
      exact (positiveNatWeightedEvenPowerSeriesReal_eq_zero_iff x).mp hzero
    · -- Route correction: on the active branch, fixed points would force the nonzero selected
      -- subgradient to vanish after scaling, contradicting Proposition 17.22.
      have hactive : 0 < positiveNatWeightedEvenPowerSeriesReal x := lt_of_not_ge hlevel
      let u : L2pos :=
        positiveNatWeightedEvenPowerSeriesMinimalNormSelection
          ⟨x, positiveNatWeightedEvenPowerSeriesReal_mem_subdifferential_dom x⟩
      have hu_eq :
          u =
            minimalNormSubgradient positiveNatWeightedEvenPowerSeries
              positiveNatWeightedEvenPowerSeries_mem_gammaZero.2 x
              (positiveNatWeightedEvenPowerSeries_continuousPoint x) := by
        simp [u, positiveNatWeightedEvenPowerSeriesMinimalNormSelection]
      have hx_ne_zero : x ≠ 0 := by
        intro hx_zero
        have hfx_zero : positiveNatWeightedEvenPowerSeriesReal x = 0 :=
          (positiveNatWeightedEvenPowerSeriesReal_eq_zero_iff x).2 hx_zero
        exact hactive.ne' hfx_zero
      have hu_ne : u ≠ 0 := by
        rw [hu_eq]
        exact
          minimalNormSubgradient_ne_zero_of_continuousAtOnEffectiveDomain_of_not_mem_argmin
            positiveNatWeightedEvenPowerSeries
            positiveNatWeightedEvenPowerSeries_mem_gammaZero.2
            (positiveNatWeightedEvenPowerSeries_continuousPoint x)
            (positiveNatWeightedEvenPowerSeriesReal_not_mem_argmin_of_ne_zero hx_ne_zero)
      have hbranch :
          weighted_even_power_subgradient_projector x =
            x + (((0 - positiveNatWeightedEvenPowerSeriesReal x) / (‖u‖ ^ 2)) • u) := by
        simpa [weighted_even_power_subgradient_projector, u,
          positiveNatWeightedEvenPowerSeriesReal_selectedSubgradient_eq] using
          (continuousConvexSubgradientProjector_apply_of_lt positiveNatWeightedEvenPowerSeriesReal 0
            positiveNatWeightedEvenPowerSeriesReal_continuous
            positiveNatWeightedEvenPowerSeriesReal_convexOn
            positiveNatWeightedEvenPowerSeriesReal_lowerLevelSet_zero_nonempty
            positiveNatWeightedEvenPowerSeriesMinimalNormSelection
            (x := x) hactive)
      have hsmul_zero :
          (((0 - positiveNatWeightedEvenPowerSeriesReal x) / (‖u‖ ^ 2)) • u) = 0 := by
        have hEq :
            x + (((0 - positiveNatWeightedEvenPowerSeriesReal x) / (‖u‖ ^ 2)) • u) = x := by
          exact hbranch.symm.trans hx
        have hEq' := congrArg (fun z : L2pos ↦ z - x) hEq
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hEq'
      have hcoeff_ne :
          ((0 - positiveNatWeightedEvenPowerSeriesReal x) / (‖u‖ ^ 2)) ≠ 0 := by
        have hnum_ne : 0 - positiveNatWeightedEvenPowerSeriesReal x ≠ 0 := by
          exact sub_ne_zero.mpr hactive.ne'.symm
        have hden_ne : ‖u‖ ^ 2 ≠ 0 := by
          exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu_ne)
        exact div_ne_zero hnum_ne hden_ne
      exact False.elim <| hu_ne <| (smul_eq_zero.mp hsmul_zero).resolve_left hcoeff_ne
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [Function.mem_fixedPoints_iff]
    have hzero : positiveNatWeightedEvenPowerSeriesReal (0 : L2pos) = 0 := by
      exact (positiveNatWeightedEvenPowerSeriesReal_eq_zero_iff (0 : L2pos)).2 rfl
    -- The zero vector lies in the lower level set, so Definition 29.40 stays on
    -- the identity branch.
    exact
      continuousConvexSubgradientProjector_apply_of_mem_lowerLevelSet
        positiveNatWeightedEvenPowerSeriesReal 0
        positiveNatWeightedEvenPowerSeriesReal_continuous
        positiveNatWeightedEvenPowerSeriesReal_convexOn
        positiveNatWeightedEvenPowerSeriesReal_lowerLevelSet_zero_nonempty
        positiveNatWeightedEvenPowerSeriesMinimalNormSelection
        (x := (0 : L2pos)) (by
          rw [ERealFunction.mem_lowerLevelSet_iff]
          have hzero_le : positiveNatWeightedEvenPowerSeriesReal (0 : L2pos) ≤ 0 := by
            simp [hzero]
          simpa [Function.toEReal_apply] using
            (show (((positiveNatWeightedEvenPowerSeriesReal (0 : L2pos) : ℝ) : EReal) ≤
                (0 : EReal)) from by
              exact_mod_cast hzero_le))

/-- Consequence of Example 29.48 (6): the weighted even-power subgradient projector is not weakly
continuous. -/
theorem weighted_even_power_subgradient_projector_not_weaklyContinuous :
    ¬ WeaklyContinuous
      (fun x : (Set.univ : Set L2pos) ↦ weighted_even_power_subgradient_projector x) := by
  intro hweak
  rw [weaklyContinuous_iff_forall_net_tendsto] at hweak
  -- Weak continuity transports the weak limit `xₙ ⇀ e₁` through the projector.
  have hproj_cont :
      Tendsto
        (fun n ↦
          toWeakSpace ℝ L2pos
            (weighted_even_power_subgradient_projector
              (weighted_even_power_counterexample_sequence n)))
        atTop
        (𝓝
          (toWeakSpace ℝ L2pos
            (weighted_even_power_subgradient_projector
              (positive_nat_standard_unit_vector 1)))) := by
    simpa using
      hweak
        (fun n ↦ ⟨weighted_even_power_counterexample_sequence n, Set.mem_univ _⟩)
        ⟨positive_nat_standard_unit_vector 1, Set.mem_univ _⟩
        weighted_even_power_counterexample_sequence_tendsto_weakly
  have hlimit_eq :
      toWeakSpace ℝ L2pos
          (weighted_even_power_subgradient_projector (positive_nat_standard_unit_vector 1)) =
        toWeakSpace ℝ L2pos (positive_nat_standard_unit_vector 1) :=
    tendsto_nhds_unique hproj_cont
      weighted_even_power_subgradient_projector_image_sequence_tendsto_weakly
  have hfixed_first :
      weighted_even_power_subgradient_projector (positive_nat_standard_unit_vector 1) =
        positive_nat_standard_unit_vector 1 :=
    (toWeakSpace ℝ L2pos).injective hlimit_eq
  have hhalf_eq :
      (1 / 2 : ℝ) • positive_nat_standard_unit_vector 1 =
        positive_nat_standard_unit_vector 1 := by
    calc
      (1 / 2 : ℝ) • positive_nat_standard_unit_vector 1 =
          weighted_even_power_subgradient_projector (positive_nat_standard_unit_vector 1) := by
            simpa using
              weighted_even_power_subgradient_projector_maps_first_basis_to_half.symm
      _ = positive_nat_standard_unit_vector 1 := hfixed_first
  -- Comparing the first coordinate yields the contradiction `1 / 2 = 1`.
  have hcoord := congrArg (fun z : L2pos ↦ z 1) hhalf_eq
  simp [positive_nat_standard_unit_vector, lp.single_apply] at hcoord

/-- Consequence of Example 29.48 (7): the weighted even-power subgradient projector is not
nonexpansive. -/
theorem weighted_even_power_subgradient_projector_not_nonexpansive :
    ¬ LipschitzWith 1 weighted_even_power_subgradient_projector := by
  intro hnonexp
  have hsub :
      LipschitzWith 1
        (fun x : (Set.univ : Set L2pos) ↦ weighted_even_power_subgradient_projector x) := by
    intro x y
    simpa using hnonexp x y
  have hfixed_first :
      weighted_even_power_subgradient_projector (positive_nat_standard_unit_vector 1) =
        positive_nat_standard_unit_vector 1 := by
    -- Corollary 4.28 turns weak convergence plus vanishing residuals into a fixed-point identity.
    simpa using
      map_eq_of_tendsto_weakly_of_residual_tendsto_zero_of_nonexpansive
        (D := (Set.univ : Set L2pos))
        (T := fun x : (Set.univ : Set L2pos) ↦ weighted_even_power_subgradient_projector x)
        (xₙ := fun n ↦ ⟨weighted_even_power_counterexample_sequence n, Set.mem_univ _⟩)
        (x := ⟨positive_nat_standard_unit_vector 1, Set.mem_univ _⟩)
        isClosed_univ convex_univ hsub
        weighted_even_power_counterexample_sequence_tendsto_weakly
        weighted_even_power_subgradient_projector_residual_tendsto_zero
  have hhalf_eq :
      (1 / 2 : ℝ) • positive_nat_standard_unit_vector 1 =
        positive_nat_standard_unit_vector 1 := by
    calc
      (1 / 2 : ℝ) • positive_nat_standard_unit_vector 1 =
          weighted_even_power_subgradient_projector (positive_nat_standard_unit_vector 1) := by
            simpa using
              weighted_even_power_subgradient_projector_maps_first_basis_to_half.symm
      _ = positive_nat_standard_unit_vector 1 := hfixed_first
  -- The first coordinate again forces the impossible equality `1 / 2 = 1`.
  have hcoord := congrArg (fun z : L2pos ↦ z 1) hhalf_eq
  simp [positive_nat_standard_unit_vector, lp.single_apply] at hcoord

end

end ERealFunction
