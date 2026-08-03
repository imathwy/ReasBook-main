module

public import Mathlib.Data.PNat.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Order.Lattice

public section

open Filter

/-- The real function with value `1 / n` at the rational point `g n` and zero away
from the rational points enumerated by `g`. -/
noncomputable def rationalSpikeFunction (g : ℕ+ ≃ ℚ) (x : ℝ) : ℝ :=
  ∑' n : ℕ+, if x = (g n : ℝ) then 1 / (n : ℝ) else 0

/-- At the rational point indexed by `n`, `rationalSpikeFunction g` has value `1 / n`. -/
theorem rationalSpikeFunction_apply (g : ℕ+ ≃ ℚ) (n : ℕ+) :
    rationalSpikeFunction g (g n : ℝ) = 1 / (n : ℝ) := by
  -- Only the summand indexed by `n` survives at the point `g n`.
  rw [rationalSpikeFunction, tsum_eq_single n]
  · simp
  · intro m hmn
    have hne : (g n : ℝ) ≠ (g m : ℝ) := by
      intro h
      apply hmn
      apply g.injective
      exact_mod_cast h.symm
    simp [hne]

/-- The function `rationalSpikeFunction g` vanishes at every irrational point. -/
theorem rationalSpikeFunction_eq_zero_of_irrational (g : ℕ+ ≃ ℚ) {x : ℝ}
    (hx : Irrational x) : rationalSpikeFunction g x = 0 := by
  -- No summand is supported at an irrational input.
  simp only [rationalSpikeFunction, hx.ne_rat, if_false, tsum_zero]

/-- Helper for Exercise 48.9: `Finset.range (N + 1)` is nonempty. -/
private lemma range_add_one_nonempty (N : ℕ) : (Finset.range (N + 1)).Nonempty := by
  simp

/-- The `N`-th continuous approximation to `rationalSpikeFunction g`, formed as the
maximum of triangular spikes at the first `N + 1` enumerated rational points. -/
noncomputable def rationalSpikeApproximation (g : ℕ+ ≃ ℚ) (N : ℕ) (x : ℝ) : ℝ :=
  (Finset.range (N + 1)).sup' (range_add_one_nonempty N) fun k ↦
    max 0 (1 / (k + 1 : ℝ) - (N + 1 : ℝ) * |x - (g k.succPNat : ℝ)|)

/-- Each `rationalSpikeApproximation g N` is continuous. -/
theorem continuous_rationalSpikeApproximation (g : ℕ+ ≃ ℚ) (N : ℕ) :
    Continuous (rationalSpikeApproximation g N) := by
  -- A finite maximum of triangular spikes is continuous.
  unfold rationalSpikeApproximation
  apply Continuous.finset_sup'_apply
  intro k hk
  fun_prop

/-- Helper for Exercise 48.9: a triangular spike evaluated away from its center
eventually vanishes as its slope tends to infinity. -/
private lemma triangularSpike_eventually_eq_zero {a x c : ℝ} (hxc : x ≠ c) :
    ∀ᶠ N : ℕ in atTop, max 0 (a - (N + 1 : ℝ) * |x - c|) = 0 := by
  have hd : 0 < |x - c| := abs_pos.mpr (sub_ne_zero.mpr hxc)
  obtain ⟨K, hK⟩ := exists_nat_gt (a / |x - c|)
  filter_upwards [eventually_ge_atTop K] with N hKN
  apply max_eq_left
  rw [sub_nonpos]
  have haK : a < (K : ℝ) * |x - c| := (div_lt_iff₀ hd).mp hK
  calc
    a ≤ (K : ℝ) * |x - c| := haK.le
    _ ≤ (N + 1 : ℝ) * |x - c| := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hKN.trans (Nat.le_succ N)
      · exact hd.le

/-- Helper for Exercise 48.9: a triangular spike is bounded above by its height. -/
private lemma triangularSpike_le_height {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max 0 (a - b * |d|) ≤ a := by
  apply max_le ha
  exact sub_le_self a (mul_nonneg hb (abs_nonneg d))

/-- Helper for Exercise 48.9: an enumerated point with an earlier natural index
is distinct from the point indexed by `n`. -/
private lemma enumeratedPoint_ne_of_lt_natPred (g : ℕ+ ≃ ℚ) (n : ℕ+) {k : ℕ}
    (hk : k < n.natPred) : (g n : ℝ) ≠ (g k.succPNat : ℝ) := by
  intro h
  have hrat : g n = g k.succPNat := by
    exact_mod_cast h
  have hindex : n = k.succPNat := g.injective hrat
  have hpred : n.natPred = k := by
    rw [hindex, Nat.natPred_succPNat]
  exact (Nat.ne_of_lt hk) hpred.symm

/-- The continuous approximations converge pointwise to `rationalSpikeFunction g`. -/
theorem tendsto_rationalSpikeApproximation (g : ℕ+ ≃ ℚ) (x : ℝ) :
    Tendsto (fun N ↦ rationalSpikeApproximation g N x) atTop
      (nhds (rationalSpikeFunction g x)) := by
  by_cases hx : Irrational x
  · rw [rationalSpikeFunction_eq_zero_of_irrational g hx, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
    have hvanish : ∀ᶠ N : ℕ in atTop, ∀ k ∈ Finset.range K,
        max 0 (1 / (k + 1 : ℝ) - (N + 1 : ℝ) * |x - (g k.succPNat : ℝ)|) = 0 :=
      (Finset.range K).eventually_all.mpr fun k hk ↦
        triangularSpike_eventually_eq_zero (hx.ne_rat (g k.succPNat))
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hvanish
    refine ⟨N₀, ?_⟩
    intro N hNN₀
    have hN := hN₀ N hNN₀
    have hnonneg : 0 ≤ rationalSpikeApproximation g N x := by
      unfold rationalSpikeApproximation
      have hzeroMem : 0 ∈ Finset.range (N + 1) :=
        Finset.mem_range.mpr (Nat.zero_lt_succ N)
      exact Finset.le_sup'_of_le
        (fun k : ℕ ↦ max 0 (1 / (k + 1 : ℝ) -
          (N + 1 : ℝ) * |x - (g k.succPNat : ℝ)|)) hzeroMem (le_max_left 0 _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    apply lt_of_le_of_lt _ hK
    unfold rationalSpikeApproximation
    apply Finset.sup'_le
    intro k hk
    by_cases hkK : k < K
    · rw [hN k (Finset.mem_range.mpr hkK)]
      positivity
    · calc
        max 0 (1 / (k + 1 : ℝ) - (N + 1 : ℝ) * |x - (g k.succPNat : ℝ)|) ≤
            1 / (k + 1 : ℝ) := by
          apply triangularSpike_le_height
          · positivity
          · positivity
        _ ≤ 1 / (K + 1 : ℝ) := by
          apply one_div_le_one_div_of_le
          · positivity
          · exact_mod_cast Nat.add_le_add_right (Nat.le_of_not_gt hkK) 1
  · obtain ⟨q, hxq⟩ := exists_rat_of_not_irrational hx
    let n : ℕ+ := g.symm q
    have hxn : x = (g n : ℝ) := by
      rw [hxq]
      simp [n]
    rw [hxn, rationalSpikeFunction_apply]
    have hvanish : ∀ᶠ N : ℕ in atTop, ∀ k ∈ Finset.range n.natPred,
        max 0 (1 / (k + 1 : ℝ) -
          (N + 1 : ℝ) * |(g n : ℝ) - (g k.succPNat : ℝ)|) = 0 :=
      (Finset.range n.natPred).eventually_all.mpr fun k hk ↦
        triangularSpike_eventually_eq_zero
          (enumeratedPoint_ne_of_lt_natPred g n (Finset.mem_range.mp hk))
    have hready : ∀ᶠ N : ℕ in atTop,
        (∀ k ∈ Finset.range n.natPred,
          max 0 (1 / (k + 1 : ℝ) -
            (N + 1 : ℝ) * |(g n : ℝ) - (g k.succPNat : ℝ)|) = 0) ∧
          n.natPred ≤ N := hvanish.and (eventually_ge_atTop n.natPred)
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hready
    apply tendsto_atTop_of_eventually_const (i₀ := N₀)
    intro N hNN₀
    obtain ⟨hN, hnN⟩ := hN₀ N hNN₀
    have hcast : (n.natPred : ℝ) + 1 = (n : ℝ) := by
      exact_mod_cast PNat.natPred_add_one n
    apply le_antisymm
    · unfold rationalSpikeApproximation
      apply Finset.sup'_le
      intro k hk
      by_cases hkn : k < n.natPred
      · rw [hN k (Finset.mem_range.mpr hkn)]
        positivity
      · calc
          max 0 (1 / (k + 1 : ℝ) -
              (N + 1 : ℝ) * |(g n : ℝ) - (g k.succPNat : ℝ)|) ≤
              1 / (k + 1 : ℝ) := by
            apply triangularSpike_le_height
            · positivity
            · positivity
          _ ≤ 1 / (n.natPred + 1 : ℝ) := by
            apply one_div_le_one_div_of_le
            · positivity
            · exact_mod_cast Nat.add_le_add_right (Nat.le_of_not_gt hkn) 1
          _ = 1 / (n : ℝ) := by rw [hcast]
    · unfold rationalSpikeApproximation
      have hnmem : n.natPred ∈ Finset.range (N + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hnN)
      apply le_trans _ (Finset.le_sup' _ hnmem)
      simp [PNat.succPNat_natPred, hcast]


end
