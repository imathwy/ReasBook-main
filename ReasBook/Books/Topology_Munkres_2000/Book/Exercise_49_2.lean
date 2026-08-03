import Topology_Munkres_2000.Book.Example_49_1.LargeSecants
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace UnitIntervalSecant

/-- An integer frequency large enough to make the triangular wave uniformly small. -/
noncomputable def sawtoothFrequency (n : ℕ) (ε : ℝ) : ℕ :=
  max n ⌈(n + 1 : ℝ) / (2 * ε)⌉₊

/-- Half the width of each affine edge in the small triangular wave. -/
noncomputable def sawtoothMesh (n : ℕ) (ε : ℝ) : ℝ :=
  1 / (4 * sawtoothFrequency n ε : ℝ)

/-- The lattice of minima for the small triangular wave. -/
def sawtoothLattice (n : ℕ) (ε : ℝ) : Set ℝ :=
  {y | ∃ k : ℤ, y = (4 * sawtoothMesh n ε) * k}

/-- The explicit small triangular wave used to produce an element of `Uₙ`. -/
noncomputable def smallSawtooth (n : ℕ) (ε : ℝ) : C(unitInterval, ℝ) where
  toFun x := (n + 1 : ℝ) * Metric.infDist (x : ℝ) (sawtoothLattice n ε)
  continuous_toFun := continuous_const.mul
    ((Metric.continuous_infDist_pt (sawtoothLattice n ε)).comp continuous_subtype_val)

/-- Evaluation of the explicit small triangular wave. -/
theorem smallSawtooth_apply (n : ℕ) (ε : ℝ) (x : unitInterval) :
    smallSawtooth n ε x =
      (n + 1 : ℝ) * Metric.infDist (x : ℝ) (sawtoothLattice n ε) := rfl


/-- Helper for Exercise 49.2: the frequency chosen for a positive amplitude
bound is a positive natural number. -/
theorem sawtoothFrequency_pos {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    0 < sawtoothFrequency n ε := by
  -- Positivity of the ceiling term passes to the defining maximum.
  have hquot : 0 < (n + 1 : ℝ) / (2 * ε) := by positivity
  exact lt_of_lt_of_le (Nat.ceil_pos.mpr hquot) (Nat.le_max_right _ _)

/-- The sawtooth mesh is positive when the requested amplitude bound is positive. -/
theorem sawtoothMesh_pos {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    0 < sawtoothMesh n ε := by
  -- Taking the reciprocal of four times that frequency gives a positive mesh.
  have hfrequency : 0 < sawtoothFrequency n ε := sawtoothFrequency_pos hε
  unfold sawtoothMesh
  positivity

/-- The sawtooth mesh is at most the scale permitted in `Uₙ`. -/
theorem sawtoothMesh_le_inv {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) :
    sawtoothMesh n ε ≤ 1 / (n : ℝ) := by
  -- The frequency dominates `n`, hence four times the frequency does as well.
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn)
  have hnfrequency : (n : ℝ) ≤ sawtoothFrequency n ε := by
    have hnfrequency_nat : n ≤ sawtoothFrequency n ε := by
      simpa only [sawtoothFrequency] using
        (Nat.le_max_left n ⌈(n + 1 : ℝ) / (2 * ε)⌉₊)
    exact_mod_cast hnfrequency_nat
  have hnfour : (n : ℝ) ≤ 4 * sawtoothFrequency n ε := by
    have hfrequency_nonneg : (0 : ℝ) ≤ sawtoothFrequency n ε := by positivity
    linarith
  -- Reciprocals reverse this positive denominator inequality.
  unfold sawtoothMesh
  exact one_div_le_one_div_of_le hnpos hnfour

/-- Helper for Exercise 49.2: distance to an integer lattice is the norm of the
corresponding point on the additive circle. -/
private lemma infDist_scaledIntegerLattice_eq_circleNorm (p x : ℝ) :
    Metric.infDist x {y : ℝ | ∃ k : ℤ, y = p * k} = ‖(x : AddCircle p)‖ := by
  -- Identify the displayed lattice with the carrier of `AddSubgroup.zmultiples p`.
  rw [QuotientAddGroup.norm_mk]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul]
    ring
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul]
    ring

/-- Helper for Exercise 49.2: four mesh widths form a period whose product
with the chosen frequency is one. -/
private lemma sawtoothPeriod_mul_frequency {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    (4 * sawtoothMesh n ε) * (sawtoothFrequency n ε : ℝ) = 1 := by
  -- Expanding the mesh leaves the frequency times its reciprocal.
  have hfrequency : 0 < sawtoothFrequency n ε := sawtoothFrequency_pos hε
  have hfrequency_ne : (sawtoothFrequency n ε : ℝ) ≠ 0 := by exact_mod_cast hfrequency.ne'
  unfold sawtoothMesh
  field_simp [hfrequency_ne]

/-- Helper for Exercise 49.2: distance to the sawtooth lattice is represented
by the norm on the additive circle of one sawtooth period. -/
private lemma infDist_sawtoothLattice_eq_circleNorm (n : ℕ) (ε x : ℝ) :
    Metric.infDist x (sawtoothLattice n ε) =
      ‖(x : AddCircle (4 * sawtoothMesh n ε))‖ := by
  -- Unfold only the lattice wrapper, then use the generic quotient-norm bridge.
  unfold sawtoothLattice
  exact infDist_scaledIntegerLattice_eq_circleNorm (4 * sawtoothMesh n ε) x

/-- Helper for Exercise 49.2: in either outward quarter of a period, shifting
forward by a quarter-period changes the additive-circle norm by that amount. -/
private lemma abs_circleNorm_add_quarter_div_eq_one (p x : ℝ) (hp : 0 < p)
    (hphase : p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < -(1 / 4 : ℝ) ∨
      (0 ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) ∧
        p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < 1 / 4)) :
    |(‖((x + p / 4 : ℝ) : AddCircle p)‖ - ‖(x : AddCircle p)‖) / (p / 4)| = 1 := by
  have hnormalize : p⁻¹ * (x + p / 4) = p⁻¹ * x + 1 / 4 := by
    field_simp [hp.ne']
  have hlower :
      -(1 / 2 : ℝ) ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) := by
    linarith [round_le_add_half (p⁻¹ * x)]
  have hupper :
      p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < 1 / 2 := by
    linarith [sub_half_lt_round (p⁻¹ * x)]
  have hround :
      round (p⁻¹ * (x + p / 4)) = round (p⁻¹ * x) := by
    rw [hnormalize, round_eq_iff]
    rcases hphase with hnegative | hpositive
    · constructor
      · linarith
      · linarith
    · constructor
      · linarith
      · linarith
  -- With the rounded lattice point fixed, the two possible phases are linear.
  rw [AddCircle.norm_eq' p hp, AddCircle.norm_eq' p hp, hround, hnormalize]
  rcases hphase with hnegative | hpositive
  · have hshiftNeg : p⁻¹ * x + 1 / 4 - (round (p⁻¹ * x) : ℝ) < 0 := by linarith
    have hbaseNeg : p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < 0 := by linarith
    rw [abs_of_neg hshiftNeg, abs_of_neg hbaseNeg]
    ring_nf
    simp [hp.ne']
  · have hshiftNonneg : 0 ≤ p⁻¹ * x + 1 / 4 - (round (p⁻¹ * x) : ℝ) := by linarith
    have hbaseNonneg : 0 ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) := by linarith
    rw [abs_of_nonneg hshiftNonneg, abs_of_nonneg hbaseNonneg]
    ring_nf
    simp [hp.ne']

/-- Helper for Exercise 49.2: in either inward quarter of a period, shifting
backward by a quarter-period changes the additive-circle norm by that amount. -/
private lemma abs_circleNorm_sub_quarter_div_eq_one (p x : ℝ) (hp : 0 < p)
    (hphase : (-(1 / 4 : ℝ) ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) ∧
        p⁻¹ * x - (round (p⁻¹ * x) : ℝ) ≤ 0) ∨
      1 / 4 ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ)) :
    |(‖((x - p / 4 : ℝ) : AddCircle p)‖ - ‖(x : AddCircle p)‖) / (-(p / 4))| = 1 := by
  have hnormalize : p⁻¹ * (x - p / 4) = p⁻¹ * x - 1 / 4 := by
    field_simp [hp.ne']
  have hlower :
      -(1 / 2 : ℝ) ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) := by
    linarith [round_le_add_half (p⁻¹ * x)]
  have hupper :
      p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < 1 / 2 := by
    linarith [sub_half_lt_round (p⁻¹ * x)]
  have hround :
      round (p⁻¹ * (x - p / 4)) = round (p⁻¹ * x) := by
    rw [hnormalize, round_eq_iff]
    rcases hphase with hnegative | hpositive
    · constructor
      · linarith
      · linarith
    · constructor
      · linarith
      · linarith
  -- Again the quotient norm is affine while the rounded lattice point is fixed.
  rw [AddCircle.norm_eq' p hp, AddCircle.norm_eq' p hp, hround, hnormalize]
  rcases hphase with hnegative | hpositive
  · have hshiftNonpos : p⁻¹ * x - 1 / 4 - (round (p⁻¹ * x) : ℝ) ≤ 0 := by linarith
    have hbaseNonpos : p⁻¹ * x - (round (p⁻¹ * x) : ℝ) ≤ 0 := by linarith
    rw [abs_of_nonpos hshiftNonpos, abs_of_nonpos hbaseNonpos]
    ring_nf
    simp [hp.ne']
  · have hshiftNonneg : 0 ≤ p⁻¹ * x - 1 / 4 - (round (p⁻¹ * x) : ℝ) := by linarith
    have hbaseNonneg : 0 ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) := by linarith
    rw [abs_of_nonneg hshiftNonneg, abs_of_nonneg hbaseNonneg]
    ring_nf
    simp [hp.ne']

/-- Helper for Exercise 49.2: a forward quarter-period selected by the triangular
phase remains in the unit interval when the period tiles that interval. -/
private lemma add_quarter_mem_unitInterval (p : ℝ) (m : ℕ) (hp : 0 < p)
    (htile : p * (m : ℝ) = 1) (x : unitInterval) (hxone : (x : ℝ) ≠ 1)
    (hphase : p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < -(1 / 4 : ℝ) ∨
      (0 ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) ∧
        p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < 1 / 4)) :
    (x : ℝ) + p / 4 ∈ Set.Icc (0 : ℝ) 1 := by
  -- Express inverse-period coordinates using the integral tiling frequency.
  have hinv : p⁻¹ = (m : ℝ) := by
    have hinv_mul : p⁻¹ * p = 1 := inv_mul_cancel₀ hp.ne'
    nlinarith
  have hinvpos : 0 < p⁻¹ := inv_pos.mpr hp
  have hquarter : p⁻¹ * (p / 4) = 1 / 4 := by
    field_simp [hp.ne']
  constructor
  · linarith [x.property.1]
  · by_contra hupper
    have hxlower : 1 - p / 4 < (x : ℝ) := by linarith
    have hzlower : (m : ℝ) - 1 / 4 < p⁻¹ * x := by
      have hscaled := mul_lt_mul_of_pos_left hxlower hinvpos
      rw [mul_sub, mul_one, hquarter] at hscaled
      rw [← hinv]
      exact hscaled
    have hzupper : p⁻¹ * x ≤ (m : ℝ) := by
      have hscaled := mul_le_mul_of_nonneg_left x.property.2 hinvpos.le
      simpa only [mul_one, hinv] using hscaled
    have hroundm : round (p⁻¹ * x) = (m : ℤ) := by
      rw [round_eq_iff]
      constructor
      · norm_num
        linarith
      · norm_num
        linarith
    rcases hphase with hnegative | hpositive
    · rw [hroundm] at hnegative
      norm_num at hnegative
      linarith
    · have hznonneg : (m : ℝ) ≤ p⁻¹ * x := by
        rw [hroundm] at hpositive
        norm_num at hpositive
        linarith
      have hxge : 1 ≤ (x : ℝ) := by
        rw [hinv] at hinvpos hznonneg
        nlinarith
      exact hxone (le_antisymm x.property.2 hxge)

/-- Helper for Exercise 49.2: a backward quarter-period selected by the
triangular phase remains in the unit interval. -/
private lemma sub_quarter_mem_unitInterval (p : ℝ) (hp : 0 < p) (x : unitInterval)
    (hphase : p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < 0 ∨
      1 / 4 ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ)) :
    (x : ℝ) - p / 4 ∈ Set.Icc (0 : ℝ) 1 := by
  -- If the backward endpoint crossed zero, its normalized phase would lie in `[0, 1/4)`.
  have hinvpos : 0 < p⁻¹ := inv_pos.mpr hp
  have hquarter : p⁻¹ * (p / 4) = 1 / 4 := by
    field_simp [hp.ne']
  constructor
  · by_contra hlower
    have hxupper : (x : ℝ) < p / 4 := by linarith
    have hzupper : p⁻¹ * x < 1 / 4 := by
      have hscaled := mul_lt_mul_of_pos_left hxupper hinvpos
      simpa only [hquarter] using hscaled
    have hzlower : 0 ≤ p⁻¹ * x := mul_nonneg hinvpos.le x.property.1
    have hroundzero : round (p⁻¹ * x) = 0 := by
      rw [round_eq_iff]
      constructor
      · norm_num
        linarith
      · norm_num
        linarith
    rcases hphase with hnegative | hpositive
    · rw [hroundzero] at hnegative
      norm_num at hnegative
      linarith
    · rw [hroundzero] at hpositive
      norm_num at hpositive
      linarith
  · linarith [x.property.2]

/-- Helper for Exercise 49.2: at every point of a tiled positive-period circle,
one available quarter-period secant changes the circle norm with unit slope. -/
private lemma exists_circleNorm_quarterSecant (p : ℝ) (m : ℕ) (hp : 0 < p)
    (htile : p * (m : ℝ) = 1) (x : unitInterval) :
    (∃ y : unitInterval, (y : ℝ) = x + p / 4 ∧
      |(‖((y : ℝ) : AddCircle p)‖ - ‖((x : ℝ) : AddCircle p)‖) / (p / 4)| = 1) ∨
    ∃ y : unitInterval, (y : ℝ) = x - p / 4 ∧
      |(‖((y : ℝ) : AddCircle p)‖ - ‖((x : ℝ) : AddCircle p)‖) / (-(p / 4))| = 1 := by
  -- Normalize the tiling data before splitting the four possible quarter-period phases.
  have hinv : p⁻¹ = (m : ℝ) := by
    have hinv_mul : p⁻¹ * p = 1 := inv_mul_cancel₀ hp.ne'
    nlinarith
  have hmposreal : 0 < (m : ℝ) := by
    rw [← hinv]
    exact inv_pos.mpr hp
  have hmone : (1 : ℝ) ≤ m := by
    have hmpos : 0 < m := by exact_mod_cast hmposreal
    exact_mod_cast hmpos
  have hpone : p ≤ 1 := by nlinarith
  by_cases hxone : (x : ℝ) = 1
  · have hresidual :
        p⁻¹ * x - (round (p⁻¹ * x) : ℝ) = 0 := by
      rw [hxone, hinv, mul_one]
      norm_num
    have hyMem : (x : ℝ) - p / 4 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith
    have hphase :
        (-(1 / 4 : ℝ) ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) ∧
          p⁻¹ * x - (round (p⁻¹ * x) : ℝ) ≤ 0) ∨
        1 / 4 ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) := by
      left
      constructor
      · linarith
      · linarith
    have hnorm := abs_circleNorm_sub_quarter_div_eq_one p (x : ℝ) hp hphase
    right
    refine ⟨⟨(x : ℝ) - p / 4, hyMem⟩, rfl, ?_⟩
    simpa only using hnorm
  · by_cases hnegative :
        p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < -(1 / 4 : ℝ)
    · have hphase :
          p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < -(1 / 4 : ℝ) ∨
          (0 ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) ∧
            p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < 1 / 4) := Or.inl hnegative
      have hyMem := add_quarter_mem_unitInterval p m hp htile x hxone hphase
      have hnorm := abs_circleNorm_add_quarter_div_eq_one p (x : ℝ) hp hphase
      left
      refine ⟨⟨(x : ℝ) + p / 4, hyMem⟩, rfl, ?_⟩
      simpa only using hnorm
    · by_cases hbelowzero :
          p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < 0
      · have hphase :
            (-(1 / 4 : ℝ) ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) ∧
              p⁻¹ * x - (round (p⁻¹ * x) : ℝ) ≤ 0) ∨
            1 / 4 ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) := by
          left
          exact ⟨not_lt.mp hnegative, hbelowzero.le⟩
        have hyMem := sub_quarter_mem_unitInterval p hp x (Or.inl hbelowzero)
        have hnorm := abs_circleNorm_sub_quarter_div_eq_one p (x : ℝ) hp hphase
        right
        refine ⟨⟨(x : ℝ) - p / 4, hyMem⟩, rfl, ?_⟩
        simpa only using hnorm
      · by_cases hbelowquarter :
            p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < 1 / 4
        · have hphase :
              p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < -(1 / 4 : ℝ) ∨
              (0 ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) ∧
                p⁻¹ * x - (round (p⁻¹ * x) : ℝ) < 1 / 4) := by
            right
            exact ⟨not_lt.mp hbelowzero, hbelowquarter⟩
          have hyMem := add_quarter_mem_unitInterval p m hp htile x hxone hphase
          have hnorm := abs_circleNorm_add_quarter_div_eq_one p (x : ℝ) hp hphase
          left
          refine ⟨⟨(x : ℝ) + p / 4, hyMem⟩, rfl, ?_⟩
          simpa only using hnorm
        · have hphase :
              (-(1 / 4 : ℝ) ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) ∧
                p⁻¹ * x - (round (p⁻¹ * x) : ℝ) ≤ 0) ∨
              1 / 4 ≤ p⁻¹ * x - (round (p⁻¹ * x) : ℝ) :=
            Or.inr (not_lt.mp hbelowquarter)
          have hyMem := sub_quarter_mem_unitInterval p hp x (Or.inr (not_lt.mp hbelowquarter))
          have hnorm := abs_circleNorm_sub_quarter_div_eq_one p (x : ℝ) hp hphase
          right
          refine ⟨⟨(x : ℝ) - p / 4, hyMem⟩, rfl, ?_⟩
          simpa only using hnorm

/-- The explicit sawtooth has pointwise absolute value at most `ε`. -/
theorem abs_smallSawtooth_le {n : ℕ} {ε : ℝ} (hε : 0 < ε) (x : ClosedUnitInterval) :
    |smallSawtooth n ε x| ≤ ε := by
  have hmesh : 0 < sawtoothMesh n ε := sawtoothMesh_pos hε
  have hperiod : 0 < 4 * sawtoothMesh n ε := by positivity
  have hfrequency : 0 < sawtoothFrequency n ε := sawtoothFrequency_pos hε
  have hfrequency_real : (0 : ℝ) < sawtoothFrequency n ε := by exact_mod_cast hfrequency
  have htile :
      (4 * sawtoothMesh n ε) * (sawtoothFrequency n ε : ℝ) = 1 :=
    sawtoothPeriod_mul_frequency hε
  have hperiod_formula :
      4 * sawtoothMesh n ε = 1 / (sawtoothFrequency n ε : ℝ) := by
    exact (eq_div_iff hfrequency_real.ne').mpr htile
  -- The quotient norm is at most half a period.
  have hinfDist :
      Metric.infDist (x : ℝ) (sawtoothLattice n ε) ≤
        (4 * sawtoothMesh n ε) / 2 := by
    rw [infDist_sawtoothLattice_eq_circleNorm]
    simpa only [abs_of_pos hperiod] using
      AddCircle.norm_le_half_period (4 * sawtoothMesh n ε) hperiod.ne'
  -- The ceiling in the frequency makes the resulting half-period height at most `ε`.
  have hfrequency_bound :
      (n + 1 : ℝ) / (2 * ε) ≤ (sawtoothFrequency n ε : ℝ) := by
    calc
      (n + 1 : ℝ) / (2 * ε) ≤
          (⌈(n + 1 : ℝ) / (2 * ε)⌉₊ : ℕ) := Nat.le_ceil _
      _ ≤ sawtoothFrequency n ε := by
        have hfrequencyNat :
            ⌈(n + 1 : ℝ) / (2 * ε)⌉₊ ≤ sawtoothFrequency n ε := by
          simpa only [sawtoothFrequency] using
            (Nat.le_max_right n ⌈(n + 1 : ℝ) / (2 * ε)⌉₊)
        exact_mod_cast hfrequencyNat
  have hheight :
      (n + 1 : ℝ) / (2 * sawtoothFrequency n ε) ≤ ε := by
    have hfrequencyDenom : (0 : ℝ) < 2 * sawtoothFrequency n ε := by positivity
    have hεDenom : (0 : ℝ) < 2 * ε := by positivity
    apply (div_le_iff₀ hfrequencyDenom).mpr
    have hscaled := (div_le_iff₀ hεDenom).mp hfrequency_bound
    nlinarith
  have hcoefficientNonneg : (0 : ℝ) ≤ n + 1 := by positivity
  have hwaveNonneg :
      0 ≤ (n + 1 : ℝ) * Metric.infDist (x : ℝ) (sawtoothLattice n ε) :=
    mul_nonneg hcoefficientNonneg Metric.infDist_nonneg
  rw [smallSawtooth_apply, abs_of_nonneg hwaveNonneg]
  calc
    (n + 1 : ℝ) * Metric.infDist (x : ℝ) (sawtoothLattice n ε) ≤
        (n + 1 : ℝ) * ((4 * sawtoothMesh n ε) / 2) := by
      exact mul_le_mul_of_nonneg_left hinfDist hcoefficientNonneg
    _ = (n + 1 : ℝ) / (2 * sawtoothFrequency n ε) := by
      rw [hperiod_formula]
      field_simp [hfrequency_real.ne']
    _ ≤ ε := hheight

/-- Helper for Exercise 49.2: at every point the explicit sawtooth has an
available secant of slope magnitude `n + 1` at the sawtooth mesh. -/
theorem smallSawtooth_largeSecant {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (x : unitInterval) :
    (n + 1 : ℝ) ≤ Δ (smallSawtooth n ε) (x, sawtoothMesh n ε) := by
  have hmesh : 0 < sawtoothMesh n ε := sawtoothMesh_pos hε
  have hperiod : 0 < 4 * sawtoothMesh n ε := by positivity
  have htile :
      (4 * sawtoothMesh n ε) * (sawtoothFrequency n ε : ℝ) = 1 :=
    sawtoothPeriod_mul_frequency hε
  have hquarter : (4 * sawtoothMesh n ε) / 4 = sawtoothMesh n ε := by ring
  have hcoefficientPos : (0 : ℝ) < n + 1 := by positivity
  have hcoefficientNonneg : (0 : ℝ) ≤ n + 1 := hcoefficientPos.le
  -- Choose the available quarter-period direction supplied by the circle geometry.
  rw [le_maxMagnitude_iff (smallSawtooth n ε) hcoefficientPos x (sawtoothMesh n ε)]
  rcases exists_circleNorm_quarterSecant (4 * sawtoothMesh n ε)
      (sawtoothFrequency n ε) hperiod htile x with hright | hleft
  · obtain ⟨y, hy, hnorm⟩ := hright
    have hnormInf := hnorm
    rw [← infDist_sawtoothLattice_eq_circleNorm n ε (y : ℝ),
      ← infDist_sawtoothLattice_eq_circleNorm n ε (x : ℝ), hquarter] at hnormInf
    have hslope :
        |(smallSawtooth n ε y - smallSawtooth n ε x) / sawtoothMesh n ε| =
          (n + 1 : ℝ) := by
      rw [smallSawtooth_apply, smallSawtooth_apply]
      calc
        |((n + 1 : ℝ) * Metric.infDist (y : ℝ) (sawtoothLattice n ε) -
            (n + 1 : ℝ) * Metric.infDist (x : ℝ) (sawtoothLattice n ε)) /
              sawtoothMesh n ε| =
            |(n + 1 : ℝ) *
              ((Metric.infDist (y : ℝ) (sawtoothLattice n ε) -
                Metric.infDist (x : ℝ) (sawtoothLattice n ε)) /
                  sawtoothMesh n ε)| := by
            congr 1
            field_simp [hmesh.ne']
        _ = |(n + 1 : ℝ)| *
              |(Metric.infDist (y : ℝ) (sawtoothLattice n ε) -
                Metric.infDist (x : ℝ) (sawtoothLattice n ε)) /
                  sawtoothMesh n ε| := abs_mul _ _
        _ = (n + 1 : ℝ) := by
          rw [abs_of_nonneg hcoefficientNonneg, hnormInf, mul_one]
    left
    refine ⟨y, ?_, ?_⟩
    · calc
        (y : ℝ) = (x : ℝ) + (4 * sawtoothMesh n ε) / 4 := hy
        _ = (x : ℝ) + sawtoothMesh n ε := by rw [hquarter]
    · exact hslope.ge
  · obtain ⟨y, hy, hnorm⟩ := hleft
    have hnormInf := hnorm
    rw [← infDist_sawtoothLattice_eq_circleNorm n ε (y : ℝ),
      ← infDist_sawtoothLattice_eq_circleNorm n ε (x : ℝ), hquarter] at hnormInf
    have hslope :
        |(smallSawtooth n ε y - smallSawtooth n ε x) / (-sawtoothMesh n ε)| =
          (n + 1 : ℝ) := by
      rw [smallSawtooth_apply, smallSawtooth_apply]
      calc
        |((n + 1 : ℝ) * Metric.infDist (y : ℝ) (sawtoothLattice n ε) -
            (n + 1 : ℝ) * Metric.infDist (x : ℝ) (sawtoothLattice n ε)) /
              (-sawtoothMesh n ε)| =
            |(n + 1 : ℝ) *
              ((Metric.infDist (y : ℝ) (sawtoothLattice n ε) -
                Metric.infDist (x : ℝ) (sawtoothLattice n ε)) /
                  (-sawtoothMesh n ε))| := by
            congr 1
            field_simp [hmesh.ne']
        _ = |(n + 1 : ℝ)| *
              |(Metric.infDist (y : ℝ) (sawtoothLattice n ε) -
                Metric.infDist (x : ℝ) (sawtoothLattice n ε)) /
                  (-sawtoothMesh n ε)| := abs_mul _ _
        _ = (n + 1 : ℝ) := by
          rw [abs_of_nonneg hcoefficientNonneg, hnormInf, mul_one]
    right
    refine ⟨y, ?_, ?_⟩
    · calc
        (y : ℝ) = (x : ℝ) - (4 * sawtoothMesh n ε) / 4 := hy
        _ = (x : ℝ) - sawtoothMesh n ε := by rw [hquarter]
    · exact hslope.ge

/-- The explicit small sawtooth belongs to the set `Uₙ`. -/
theorem smallSawtooth_mem_largeSecantSet {n : ℕ} {ε : ℝ} (hn : 2 ≤ n)
    (hε : 0 < ε) :
    smallSawtooth n ε ∈ U_{n} := by
  have hmesh : 0 < sawtoothMesh n ε := sawtoothMesh_pos hε
  have hmeshInv : sawtoothMesh n ε ≤ 1 / (n : ℝ) := sawtoothMesh_le_inv hn
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have htwoPos : (0 : ℝ) < 2 := by norm_num
  have hinvHalf : 1 / (n : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le htwoPos hnreal
  have hmeshHalf : sawtoothMesh n ε ≤ 1 / 2 := hmeshInv.trans hinvHalf
  -- The pointwise exact slopes give a uniform lower bound for the secant infimum.
  have hLower :
      (n + 1 : ℝ) ≤ Δ_{sawtoothMesh n ε} (smallSawtooth n ε) :=
    (le_infMagnitude_iff (smallSawtooth n ε) (sawtoothMesh n ε) hmesh hmeshHalf).mpr
      (smallSawtooth_largeSecant hε)
  rw [mem_largeSecantSet]
  refine ⟨sawtoothMesh n ε, hmesh, hmeshInv, ?_⟩
  have hnstep : (n : ℝ) < n + 1 := by norm_num
  exact hnstep.trans_le hLower

/-- Exercise 49.2: for `n ≥ 2` and `ε > 0`, there is a continuous function in
`Uₙ` whose absolute value is everywhere at most `ε`. -/
theorem smallSawtooth_exists {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε) :
    ∃ f : C(unitInterval, ℝ), f ∈ U_{n} ∧ ∀ x, |f x| ≤ ε := by
  -- The explicit sawtooth simultaneously supplies membership and the amplitude bound.
  exact ⟨smallSawtooth n ε, smallSawtooth_mem_largeSecantSet hn hε,
    abs_smallSawtooth_le hε⟩

end UnitIntervalSecant
