import Mathlib
import DifferentialForms_Cartan_1970.III.section11.«frozen_0010_Definition_III_5_extra_7»
import DifferentialForms_Cartan_1970.III.section11.«frozen_0011_Proposition_5_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Topology
open MeromorphicOn

namespace PeriodPair

/-- Cartan's coefficient `a₂`, normalized from mathlib's lattice invariant `g₂`. -/
abbrev cartan_a₂ (L : PeriodPair) : ℂ :=
  L.g₂ / 20

/-- The normalization identity relating Cartan's `a₂` to `g₂`. -/
theorem twenty_mul_cartan_a₂ (L : PeriodPair) :
    20 * L.cartan_a₂ = L.g₂ := by
  field_simp [cartan_a₂]

/-- Cartan's coefficient `a₄`, normalized from mathlib's lattice invariant `g₃`. -/
abbrev cartan_a₄ (L : PeriodPair) : ℂ :=
  L.g₃ / 28

/-- The normalization identity relating Cartan's `a₄` to `g₃`. -/
theorem twenty_eight_mul_cartan_a₄ (L : PeriodPair) :
    28 * L.cartan_a₄ = L.g₃ := by
  field_simp [cartan_a₄]

/-- The affine cubic equation attached to a period pair in Cartan's `a₂`/`a₄` normalization. -/
def on_cartan_cubic (L : PeriodPair) (x y : ℂ) : Prop :=
  y ^ 2 = 4 * x ^ 3 - 20 * L.cartan_a₂ * x - 28 * L.cartan_a₄

/-- Cartan's cubic equation rewritten in mathlib's `g₂`/`g₃` normalization. -/
theorem on_cartan_cubic_iff_g₂_g₃ (L : PeriodPair) (x y : ℂ) :
    L.on_cartan_cubic x y ↔ y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ := by
  constructor <;> intro h
  · simpa [on_cartan_cubic, L.twenty_mul_cartan_a₂, L.twenty_eight_mul_cartan_a₄, mul_assoc] using h
  · simpa [on_cartan_cubic, L.twenty_mul_cartan_a₂, L.twenty_eight_mul_cartan_a₄, mul_assoc] using h

/-- The canonical Weierstrass parametrization lands on Cartan's cubic away from the lattice. -/
theorem on_cartan_cubic_weierstrassP (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    L.on_cartan_cubic (℘[L] z) (℘'[L] z) := by
  rw [L.on_cartan_cubic_iff_g₂_g₃]
  simpa using L.derivWeierstrassP_sq z hz

/-- Helper for Proposition 5.2: if a non-lattice point represents a nontrivial `2`-torsion class
of `ℂ / L.lattice`, then the derivative of `℘` vanishes there. -/
lemma derivWeierstrassP_eq_zero_of_two_mul_mem_lattice (L : PeriodPair) {z : ℂ}
    (_hz : z ∉ L.lattice) (h2z : 2 * z ∈ L.lattice) : ℘'[L] z = 0 := by
  -- Use oddness and periodicity to identify the value at `z` with its own negative.
  let l : L.lattice := ⟨2 * z, h2z⟩
  have hself : ℘'[L] z = -℘'[L] z := by
    calc
      ℘'[L] z = ℘'[L] (-z + (l : ℂ)) := by
        change ℘'[L] z = ℘'[L] (-z + 2 * z)
        ring_nf
      _ = ℘'[L] (-z) := L.derivWeierstrassP_add_coe (-z) l
      _ = -℘'[L] z := L.derivWeierstrassP_neg z
  -- In characteristic zero, the only element equal to its own negative is `0`.
  have hsum : ℘'[L] z + ℘'[L] z = 0 := eq_neg_iff_add_eq_zero.mp hself
  have htwo : (2 : ℂ) * ℘'[L] z = 0 := by simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero

/-- Helper for Proposition 5.2: the diagonal half-period is not a lattice point. -/
lemma omega_sum_div_two_not_mem_lattice (L : PeriodPair) :
    (L.ω₁ + L.ω₂) / 2 ∉ L.lattice := by
  -- Rewrite the half-sum in the lattice basis and use the denominator test from mathlib.
  simpa [add_div, inv_mul_eq_div, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
    mul_assoc] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := (1 / 2 : ℚ)) (β := (1 / 2 : ℚ))).not.mpr
      (by norm_num)

/-- Helper for Proposition 5.2: a non-lattice `2`-torsion class is represented by one of the
three nontrivial half-periods. -/
lemma two_mul_mem_lattice_iff_half_period_class (L : PeriodPair) {z : ℂ}
    (hz : z ∉ L.lattice) :
    2 * z ∈ L.lattice ↔
      z - L.ω₁ / 2 ∈ L.lattice ∨
        z - L.ω₂ / 2 ∈ L.lattice ∨
          z - (L.ω₁ + L.ω₂) / 2 ∈ L.lattice := by
  constructor
  · intro h2z
    obtain ⟨m, n, hmn⟩ := L.mem_lattice.mp h2z
    have hz_repr : z = ((m : ℂ) / 2) * L.ω₁ + ((n : ℂ) / 2) * L.ω₂ := by
      -- Divide the lattice relation for `2 * z` by `2` to recover coordinates for `z`.
      have hmn' : (2 : ℂ) * z = (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ := by
        simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hmn.symm
      have hdiv := congrArg (fun w : ℂ => w / 2) hmn'
      simpa [div_eq_mul_inv, add_mul, mul_assoc, mul_left_comm, mul_comm] using hdiv
    rcases Int.even_or_odd m with hm | hm
    · rcases hm with ⟨a, rfl⟩
      rcases Int.even_or_odd n with hn | hn
      · rcases hn with ⟨b, rfl⟩
        -- If both lattice coordinates are even then `z` itself is a lattice point, contradiction.
        have hz_mem : z ∈ L.lattice := by
          have hz_even :
              z = a * L.ω₁ + b * L.ω₂ := by
            calc
              z = (((2 * a : ℤ) : ℂ) / 2) * L.ω₁ + (((2 * b : ℤ) : ℂ) / 2) * L.ω₂ := by
                simpa using hz_repr
              _ = a * L.ω₁ + b * L.ω₂ := by norm_num
          exact L.mem_lattice.mpr ⟨a, b, hz_even.symm⟩
        exact (hz hz_mem).elim
      · rcases hn with ⟨b, rfl⟩
        -- The parity pattern `(even, odd)` lands in the `ω₂ / 2` class.
        right
        left
        have hz_half :
            z - L.ω₂ / 2 = a * L.ω₁ + b * L.ω₂ := by
          calc
            z - L.ω₂ / 2 =
                ((((2 * a : ℤ) : ℂ) / 2) * L.ω₁ + (((2 * b + 1 : ℤ) : ℂ) / 2) * L.ω₂) -
                  L.ω₂ / 2 := by
                  simpa using congrArg (fun w : ℂ => w - L.ω₂ / 2) hz_repr
            _ = (((2 * a : ℤ) : ℂ) / 2) * L.ω₁ +
                  ((((2 * b + 1 : ℤ) : ℂ) / 2) - 1 / 2) * L.ω₂ := by
                  ring
            _ = a * L.ω₁ + b * L.ω₂ := by
              have hb : ((((2 * b + 1 : ℤ) : ℂ) / 2) - 1 / 2) = (b : ℂ) := by
                calc
                  ((((2 * b + 1 : ℤ) : ℂ) / 2) - 1 / 2) = -1 / 2 + (((2 * b + 1 : ℤ) : ℂ)) * (1 / 2) := by
                    ring
                  _ = -1 / 2 + (1 + 2 * (b : ℂ)) * (1 / 2) := by
                    simpa [add_comm, add_left_comm, add_assoc]
                  _ = (b : ℂ) := by
                    ring_nf
              rw [hb]
              norm_num
        exact L.mem_lattice.mpr ⟨a, b, hz_half.symm⟩
    · rcases hm with ⟨a, rfl⟩
      rcases Int.even_or_odd n with hn | hn
      · rcases hn with ⟨b, rfl⟩
        -- The parity pattern `(odd, even)` lands in the `ω₁ / 2` class.
        left
        have hz_half :
            z - L.ω₁ / 2 = a * L.ω₁ + b * L.ω₂ := by
          calc
            z - L.ω₁ / 2 =
                ((((2 * a + 1 : ℤ) : ℂ) / 2) * L.ω₁ + (((2 * b : ℤ) : ℂ) / 2) * L.ω₂) -
                  L.ω₁ / 2 := by
                  simpa using congrArg (fun w : ℂ => w - L.ω₁ / 2) hz_repr
            _ = ((((2 * a + 1 : ℤ) : ℂ) / 2) - 1 / 2) * L.ω₁ +
                  (((2 * b : ℤ) : ℂ) / 2) * L.ω₂ := by
                  ring
            _ = a * L.ω₁ + b * L.ω₂ := by
              have ha : ((((2 * a + 1 : ℤ) : ℂ) / 2) - 1 / 2) = (a : ℂ) := by
                calc
                  ((((2 * a + 1 : ℤ) : ℂ) / 2) - 1 / 2) = -1 / 2 + (((2 * a + 1 : ℤ) : ℂ)) * (1 / 2) := by
                    ring
                  _ = -1 / 2 + (1 + 2 * (a : ℂ)) * (1 / 2) := by
                    simpa [add_comm, add_left_comm, add_assoc]
                  _ = (a : ℂ) := by
                    ring_nf
              rw [ha]
              norm_num
        exact L.mem_lattice.mpr ⟨a, b, hz_half.symm⟩
      · rcases hn with ⟨b, rfl⟩
        -- The parity pattern `(odd, odd)` lands in the diagonal half-period class.
        right
        right
        have hz_half :
            z - (L.ω₁ + L.ω₂) / 2 = a * L.ω₁ + b * L.ω₂ := by
          calc
            z - (L.ω₁ + L.ω₂) / 2 =
                ((((2 * a + 1 : ℤ) : ℂ) / 2) * L.ω₁ + (((2 * b + 1 : ℤ) : ℂ) / 2) * L.ω₂) -
                  (L.ω₁ + L.ω₂) / 2 := by
                  simpa using congrArg (fun w : ℂ => w - (L.ω₁ + L.ω₂) / 2) hz_repr
            _ = ((((2 * a + 1 : ℤ) : ℂ) / 2) - 1 / 2) * L.ω₁ +
                  ((((2 * b + 1 : ℤ) : ℂ) / 2) - 1 / 2) * L.ω₂ := by
                  ring
            _ = a * L.ω₁ + b * L.ω₂ := by
              have ha : ((((2 * a + 1 : ℤ) : ℂ) / 2) - 1 / 2) = (a : ℂ) := by
                calc
                  ((((2 * a + 1 : ℤ) : ℂ) / 2) - 1 / 2) = -1 / 2 + (((2 * a + 1 : ℤ) : ℂ)) * (1 / 2) := by
                    ring
                  _ = -1 / 2 + (1 + 2 * (a : ℂ)) * (1 / 2) := by
                    simpa [add_comm, add_left_comm, add_assoc]
                  _ = (a : ℂ) := by
                    ring_nf
              have hb : ((((2 * b + 1 : ℤ) : ℂ) / 2) - 1 / 2) = (b : ℂ) := by
                calc
                  ((((2 * b + 1 : ℤ) : ℂ) / 2) - 1 / 2) = -1 / 2 + (((2 * b + 1 : ℤ) : ℂ)) * (1 / 2) := by
                    ring
                  _ = -1 / 2 + (1 + 2 * (b : ℂ)) * (1 / 2) := by
                    simpa [add_comm, add_left_comm, add_assoc]
                  _ = (b : ℂ) := by
                    ring_nf
              rw [ha, hb]
        exact L.mem_lattice.mpr ⟨a, b, hz_half.symm⟩
  · rintro (hω₁ | hω₂ | hω₁ω₂)
    · -- Doubling a translate of `ω₁ / 2` recovers `2 * z` up to the lattice period `ω₁`.
      have hdouble : (2 : ℤ) • (z - L.ω₁ / 2) ∈ L.lattice := zsmul_mem hω₁ 2
      have hsum : (2 : ℂ) * (z - L.ω₁ / 2) + L.ω₁ ∈ L.lattice := by
        simpa [zsmul_eq_mul, two_mul] using add_mem hdouble L.ω₁_mem_lattice
      have hrewrite : (2 : ℂ) * (z - L.ω₁ / 2) + L.ω₁ = 2 * z := by ring
      simpa [hrewrite] using hsum
    · -- Doubling a translate of `ω₂ / 2` recovers `2 * z` up to the lattice period `ω₂`.
      have hdouble : (2 : ℤ) • (z - L.ω₂ / 2) ∈ L.lattice := zsmul_mem hω₂ 2
      have hsum : (2 : ℂ) * (z - L.ω₂ / 2) + L.ω₂ ∈ L.lattice := by
        simpa [zsmul_eq_mul, two_mul] using add_mem hdouble L.ω₂_mem_lattice
      have hrewrite : (2 : ℂ) * (z - L.ω₂ / 2) + L.ω₂ = 2 * z := by ring
      simpa [hrewrite] using hsum
    · -- The same doubling argument works for the diagonal half-period.
      have hdouble : (2 : ℤ) • (z - (L.ω₁ + L.ω₂) / 2) ∈ L.lattice := zsmul_mem hω₁ω₂ 2
      have hsum :
          (2 : ℂ) * (z - (L.ω₁ + L.ω₂) / 2) + (L.ω₁ + L.ω₂) ∈ L.lattice := by
        simpa [zsmul_eq_mul, two_mul, add_assoc] using
          add_mem hdouble (add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice)
      have hrewrite : (2 : ℂ) * (z - (L.ω₁ + L.ω₂) / 2) + (L.ω₁ + L.ω₂) = 2 * z := by ring
      simpa [hrewrite] using hsum

/-- Helper for Proposition 5.2: a branch point of `℘` gives a root of Cartan's cubic. -/
lemma cartan_polynomial_eq_zero_of_derivWeierstrassP_eq_zero (L : PeriodPair) {z : ℂ}
    (hz : z ∉ L.lattice) (hderiv : ℘'[L] z = 0) :
    4 * (℘[L] z) ^ 3 - 20 * L.cartan_a₂ * ℘[L] z - 28 * L.cartan_a₄ = 0 := by
  -- The differential equation for `(℘, ℘')` lands on Cartan's cubic; set `℘'(z) = 0`.
  have hcubic : L.on_cartan_cubic (℘[L] z) (℘'[L] z) := L.on_cartan_cubic_weierstrassP hz
  simpa [on_cartan_cubic, hderiv] using hcubic.symm

/-- Helper for Proposition 5.2: the first half-period maps to a root of Cartan's cubic. -/
lemma cartan_polynomial_eq_zero_at_omega₁_div_two (L : PeriodPair) :
    4 * (℘[L] (L.ω₁ / 2)) ^ 3 - 20 * L.cartan_a₂ * ℘[L] (L.ω₁ / 2) - 28 * L.cartan_a₄ = 0 := by
  -- The first half-period is a nontrivial `2`-torsion point modulo the lattice.
  have h2z : 2 * (L.ω₁ / 2) ∈ L.lattice := by
    have htwice : 2 * (L.ω₁ / 2) = L.ω₁ := by ring
    rw [htwice]
    exact L.ω₁_mem_lattice
  have hderiv :
      ℘'[L] (L.ω₁ / 2) = 0 :=
    L.derivWeierstrassP_eq_zero_of_two_mul_mem_lattice L.ω₁_div_two_notMem_lattice h2z
  exact L.cartan_polynomial_eq_zero_of_derivWeierstrassP_eq_zero L.ω₁_div_two_notMem_lattice hderiv

/-- Helper for Proposition 5.2: the second half-period maps to a root of Cartan's cubic. -/
lemma cartan_polynomial_eq_zero_at_omega₂_div_two (L : PeriodPair) :
    4 * (℘[L] (L.ω₂ / 2)) ^ 3 - 20 * L.cartan_a₂ * ℘[L] (L.ω₂ / 2) - 28 * L.cartan_a₄ = 0 := by
  -- The second half-period is another nontrivial `2`-torsion point modulo the lattice.
  have h2z : 2 * (L.ω₂ / 2) ∈ L.lattice := by
    have htwice : 2 * (L.ω₂ / 2) = L.ω₂ := by ring
    rw [htwice]
    exact L.ω₂_mem_lattice
  have hderiv :
      ℘'[L] (L.ω₂ / 2) = 0 :=
    L.derivWeierstrassP_eq_zero_of_two_mul_mem_lattice L.ω₂_div_two_notMem_lattice h2z
  exact L.cartan_polynomial_eq_zero_of_derivWeierstrassP_eq_zero L.ω₂_div_two_notMem_lattice hderiv

/-- Helper for Proposition 5.2: the diagonal half-period maps to a root of Cartan's cubic. -/
lemma cartan_polynomial_eq_zero_at_omega_sum_div_two (L : PeriodPair) :
    4 * (℘[L] ((L.ω₁ + L.ω₂) / 2)) ^ 3 - 20 * L.cartan_a₂ * ℘[L] ((L.ω₁ + L.ω₂) / 2) -
      28 * L.cartan_a₄ = 0 := by
  -- The remaining nontrivial `2`-torsion class is represented by the diagonal half-period.
  have h2z : 2 * ((L.ω₁ + L.ω₂) / 2) ∈ L.lattice := by
    simpa [two_mul, add_assoc] using add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice
  have hderiv :
      ℘'[L] ((L.ω₁ + L.ω₂) / 2) = 0 :=
    L.derivWeierstrassP_eq_zero_of_two_mul_mem_lattice L.omega_sum_div_two_not_mem_lattice h2z
  exact
    L.cartan_polynomial_eq_zero_of_derivWeierstrassP_eq_zero L.omega_sum_div_two_not_mem_lattice
      hderiv

/-- Helper for Proposition 5.2: the three candidate cubic roots are the `℘`-values of the three
nontrivial half-period classes. -/
def cartan_half_period_root (L : PeriodPair) : Fin 3 → ℂ :=
  fun i ↦
    if _ : i = 0 then ℘[L] (L.ω₁ / 2)
    else if _ : i = 1 then ℘[L] (L.ω₂ / 2)
    else ℘[L] ((L.ω₁ + L.ω₂) / 2)

/-- Helper for Proposition 5.2: the `0`-th candidate root is the first half-period value. -/
@[simp] lemma cartan_half_period_root_zero (L : PeriodPair) :
    L.cartan_half_period_root 0 = ℘[L] (L.ω₁ / 2) := by
  simp [cartan_half_period_root]

/-- Helper for Proposition 5.2: the `1`-st candidate root is the second half-period value. -/
@[simp] lemma cartan_half_period_root_one (L : PeriodPair) :
    L.cartan_half_period_root 1 = ℘[L] (L.ω₂ / 2) := by
  simp [cartan_half_period_root]

/-- Helper for Proposition 5.2: the `2`-nd candidate root is the diagonal half-period value. -/
@[simp] lemma cartan_half_period_root_two (L : PeriodPair) :
    L.cartan_half_period_root 2 = ℘[L] ((L.ω₁ + L.ω₂) / 2) := by
  simp [cartan_half_period_root]

/-- Helper for Proposition 5.2: translating by the first half-period class does not change the
`℘`-value. -/
lemma weierstrassP_eq_omega₁_div_two_of_sub_mem_lattice (L : PeriodPair) {z : ℂ}
    (hz : z - L.ω₁ / 2 ∈ L.lattice) :
    ℘[L] z = ℘[L] (L.ω₁ / 2) := by
  -- Rewrite `z` as the chosen half-period plus a lattice element and use periodicity.
  let l : L.lattice := ⟨z - L.ω₁ / 2, hz⟩
  have hz' : z = L.ω₁ / 2 + l := by
    change z = L.ω₁ / 2 + (z - L.ω₁ / 2)
    ring
  rw [hz', L.weierstrassP_add_coe]

/-- Helper for Proposition 5.2: translating by the second half-period class does not change the
`℘`-value. -/
lemma weierstrassP_eq_omega₂_div_two_of_sub_mem_lattice (L : PeriodPair) {z : ℂ}
    (hz : z - L.ω₂ / 2 ∈ L.lattice) :
    ℘[L] z = ℘[L] (L.ω₂ / 2) := by
  -- Rewrite `z` as the chosen half-period plus a lattice element and use periodicity.
  let l : L.lattice := ⟨z - L.ω₂ / 2, hz⟩
  have hz' : z = L.ω₂ / 2 + l := by
    change z = L.ω₂ / 2 + (z - L.ω₂ / 2)
    ring
  rw [hz', L.weierstrassP_add_coe]

/-- Helper for Proposition 5.2: translating by the diagonal half-period class does not change the
`℘`-value. -/
lemma weierstrassP_eq_omega_sum_div_two_of_sub_mem_lattice (L : PeriodPair) {z : ℂ}
    (hz : z - (L.ω₁ + L.ω₂) / 2 ∈ L.lattice) :
    ℘[L] z = ℘[L] ((L.ω₁ + L.ω₂) / 2) := by
  -- Rewrite `z` as the chosen half-period plus a lattice element and use periodicity.
  let l : L.lattice := ⟨z - (L.ω₁ + L.ω₂) / 2, hz⟩
  have hz' : z = (L.ω₁ + L.ω₂) / 2 + l := by
    change z = (L.ω₁ + L.ω₂) / 2 + (z - (L.ω₁ + L.ω₂) / 2)
    ring
  rw [hz', L.weierstrassP_add_coe]

/-- Helper for Proposition 5.2: once equality of `℘`-values is classified by `±` modulo the
lattice, the three half-period values are automatically distinct. -/
lemma cartan_half_period_root_injective_of_weierstrassP_fiber (L : PeriodPair)
    (hfiber :
      ∀ {z z' : ℂ}, z ∉ L.lattice → z' ∉ L.lattice → ℘[L] z' = ℘[L] z →
        z' - z ∈ L.lattice ∨ z' + z ∈ L.lattice) :
    Function.Injective L.cartan_half_period_root := by
  -- Route correction: the only missing source step is the global degree-two fiber theorem for `℘`.
  -- Once that theorem is available, injectivity reduces to half-period lattice arithmetic.
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    rcases hfiber L.ω₁_div_two_notMem_lattice L.ω₂_div_two_notMem_lattice hij.symm with hdiff | hsum
    · have hω :
        L.ω₁ / 2 - L.ω₂ / 2 ∈ L.lattice := by
        simpa using neg_mem hdiff
      have hbad : (((1 / 2 : ℚ) * L.ω₁ + (-1 / 2 : ℚ) * L.ω₂ : ℂ)) = L.ω₁ / 2 - L.ω₂ / 2 := by
        ring
      have hden :=
        (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := (1 / 2 : ℚ)) (β := (-1 / 2 : ℚ))).mp
          (hbad.symm ▸ hω)
      norm_num at hden
    · exact L.omega_sum_div_two_not_mem_lattice (by simpa [add_div, add_comm, add_left_comm] using hsum)
  · exfalso
    rcases hfiber L.ω₁_div_two_notMem_lattice L.omega_sum_div_two_not_mem_lattice hij.symm with
        hdiff | hsum
    · have hω : L.ω₂ / 2 ∈ L.lattice := by
        simpa [sub_eq_add_neg, add_div, add_comm, add_left_comm, add_assoc] using hdiff
      exact L.ω₂_div_two_notMem_lattice hω
    · have hω : L.ω₂ / 2 ∈ L.lattice := by
        have hsub : ((L.ω₁ + L.ω₂) / 2 + L.ω₁ / 2) - L.ω₁ ∈ L.lattice := by
          exact sub_mem hsum L.ω₁_mem_lattice
        have hrewrite : ((L.ω₁ + L.ω₂) / 2 + L.ω₁ / 2) - L.ω₁ = L.ω₂ / 2 := by
          ring
        exact hrewrite ▸ hsub
      exact L.ω₂_div_two_notMem_lattice hω
  · exfalso
    rcases hfiber L.ω₂_div_two_notMem_lattice L.ω₁_div_two_notMem_lattice (by simpa using hij.symm)
        with hdiff | hsum
    · have hω :
        L.ω₁ / 2 - L.ω₂ / 2 ∈ L.lattice := by
        simpa using hdiff
      have hbad : (((1 / 2 : ℚ) * L.ω₁ + (-1 / 2 : ℚ) * L.ω₂ : ℂ)) = L.ω₁ / 2 - L.ω₂ / 2 := by
        ring
      have hden :=
        (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := (1 / 2 : ℚ)) (β := (-1 / 2 : ℚ))).mp
          (hbad.symm ▸ hω)
      norm_num at hden
    · exact L.omega_sum_div_two_not_mem_lattice (by simpa [add_div, add_comm, add_left_comm] using hsum)
  · rfl
  · exfalso
    rcases hfiber L.ω₂_div_two_notMem_lattice L.omega_sum_div_two_not_mem_lattice hij.symm with
        hdiff | hsum
    · have hω : L.ω₁ / 2 ∈ L.lattice := by
        simpa [sub_eq_add_neg, add_div, add_comm, add_left_comm, add_assoc] using hdiff
      exact L.ω₁_div_two_notMem_lattice hω
    · have hω : L.ω₁ / 2 ∈ L.lattice := by
        have hsub : ((L.ω₁ + L.ω₂) / 2 + L.ω₂ / 2) - L.ω₂ ∈ L.lattice := by
          exact sub_mem hsum L.ω₂_mem_lattice
        have hrewrite : ((L.ω₁ + L.ω₂) / 2 + L.ω₂ / 2) - L.ω₂ = L.ω₁ / 2 := by
          ring
        exact hrewrite ▸ hsub
      exact L.ω₁_div_two_notMem_lattice hω
  · exfalso
    rcases hfiber L.omega_sum_div_two_not_mem_lattice L.ω₁_div_two_notMem_lattice
        (by simpa using hij.symm) with hdiff | hsum
    · have hω : L.ω₂ / 2 ∈ L.lattice := by
        have hneg : -((L.ω₁ / 2) - (L.ω₁ + L.ω₂) / 2) ∈ L.lattice := neg_mem hdiff
        simpa [sub_eq_add_neg, add_div, add_comm, add_left_comm, add_assoc] using hneg
      exact L.ω₂_div_two_notMem_lattice hω
    · have hω : L.ω₂ / 2 ∈ L.lattice := by
        have hsum' : ((L.ω₁ + L.ω₂) / 2 + L.ω₁ / 2) ∈ L.lattice := by
          simpa [add_comm] using hsum
        have hsub : ((L.ω₁ + L.ω₂) / 2 + L.ω₁ / 2) - L.ω₁ ∈ L.lattice := by
          exact sub_mem hsum' L.ω₁_mem_lattice
        have hrewrite : ((L.ω₁ + L.ω₂) / 2 + L.ω₁ / 2) - L.ω₁ = L.ω₂ / 2 := by
          ring
        exact hrewrite ▸ hsub
      exact L.ω₂_div_two_notMem_lattice hω
  · exfalso
    rcases hfiber L.omega_sum_div_two_not_mem_lattice L.ω₂_div_two_notMem_lattice
        (by simpa using hij.symm) with hdiff | hsum
    · have hω : L.ω₁ / 2 ∈ L.lattice := by
        have hneg : -((L.ω₂ / 2) - (L.ω₁ + L.ω₂) / 2) ∈ L.lattice := neg_mem hdiff
        simpa [sub_eq_add_neg, add_div, add_comm, add_left_comm, add_assoc] using hneg
      exact L.ω₁_div_two_notMem_lattice hω
    · have hω : L.ω₁ / 2 ∈ L.lattice := by
        have hsum' : ((L.ω₁ + L.ω₂) / 2 + L.ω₂ / 2) ∈ L.lattice := by
          simpa [add_comm] using hsum
        have hsub : ((L.ω₁ + L.ω₂) / 2 + L.ω₂ / 2) - L.ω₂ ∈ L.lattice := by
          exact sub_mem hsum' L.ω₂_mem_lattice
        have hrewrite : ((L.ω₁ + L.ω₂) / 2 + L.ω₂ / 2) - L.ω₂ = L.ω₁ / 2 := by
          ring
        exact hrewrite ▸ hsub
      exact L.ω₁_div_two_notMem_lattice hω
  · rfl

/-- Helper for Proposition 5.2: once `℘` is known to be surjective modulo the lattice and its
branch points are known to be the nontrivial `2`-torsion classes, every cubic root is one of the
three half-period values. -/
lemma exists_cartan_half_period_root_of_cubic_eq_zero (L : PeriodPair)
    (hsurj : ∀ x : ℂ, ∃ z : {z : ℂ // z ∉ L.lattice}, ℘[L] z = x)
    (hbranch : ∀ {z : ℂ}, z ∉ L.lattice → ℘'[L] z = 0 → 2 * z ∈ L.lattice)
    {x : ℂ} (hx : 4 * x ^ 3 - 20 * L.cartan_a₂ * x - 28 * L.cartan_a₄ = 0) :
    ∃ i : Fin 3, x = L.cartan_half_period_root i := by
  -- Choose a point above `x`, force it to be a branch point, and then classify its half-period class.
  obtain ⟨z, hz⟩ := hsurj x
  have hx' : 4 * x ^ 3 - L.g₂ * x - L.g₃ = 0 := by
    simpa [L.twenty_mul_cartan_a₂, L.twenty_eight_mul_cartan_a₄, mul_assoc] using hx
  have hsq : ℘'[L] z ^ 2 = 0 := by
    rw [L.derivWeierstrassP_sq z z.2, hz, hx']
  have hderiv : ℘'[L] z = 0 := by
    exact sq_eq_zero_iff.mp hsq
  have hclass := (L.two_mul_mem_lattice_iff_half_period_class z.2).mp (hbranch z.2 hderiv)
  rcases hclass with hω₁ | hω₂ | hωsum
  · refine ⟨0, ?_⟩
    -- Periodicity identifies the chosen representative with the first half-period.
    simpa [L.cartan_half_period_root_zero] using
      (hz.symm.trans (L.weierstrassP_eq_omega₁_div_two_of_sub_mem_lattice hω₁))
  · refine ⟨1, ?_⟩
    -- Periodicity identifies the chosen representative with the second half-period.
    simpa [L.cartan_half_period_root_one] using
      (hz.symm.trans (L.weierstrassP_eq_omega₂_div_two_of_sub_mem_lattice hω₂))
  · refine ⟨2, ?_⟩
    -- Periodicity identifies the chosen representative with the diagonal half-period.
    simpa [L.cartan_half_period_root_two] using
      (hz.symm.trans (L.weierstrassP_eq_omega_sum_div_two_of_sub_mem_lattice hωsum))

/-- Helper for Proposition 5.2: once the source-faithful `℘`-fiber theorem and branch
classification are available, the pair `(℘, ℘')` uniformizes Cartan's cubic modulo the lattice. -/
lemma exists_weierstrass_pair_of_on_cartan_cubic (L : PeriodPair)
    (hsurj : ∀ x : ℂ, ∃ z : {z : ℂ // z ∉ L.lattice}, ℘[L] z = x)
    (hfiber :
      ∀ {z z' : ℂ}, z ∉ L.lattice → z' ∉ L.lattice → ℘[L] z' = ℘[L] z →
        z' - z ∈ L.lattice ∨ z' + z ∈ L.lattice)
    (hbranch : ∀ {z : ℂ}, z ∉ L.lattice → ℘'[L] z = 0 → 2 * z ∈ L.lattice)
    {x y : ℂ} (hxy : L.on_cartan_cubic x y) :
    ∃ z : {z : ℂ // z ∉ L.lattice},
      (℘[L] z, ℘'[L] z) = (x, y) ∧
      ∀ z' : {z : ℂ // z ∉ L.lattice},
        (℘[L] z', ℘'[L] z') = (x, y) ↔ (z' : ℂ) - z ∈ L.lattice := by
  -- First choose a point above the `x`-coordinate and then use the sign of `℘'` to match `y`.
  obtain ⟨z₀, hz₀x⟩ := hsurj x
  have hxy' : y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ := (L.on_cartan_cubic_iff_g₂_g₃ x y).mp hxy
  have hz₀sq : ℘'[L] z₀ ^ 2 = y ^ 2 := by
    rw [L.derivWeierstrassP_sq z₀ z₀.2, hz₀x, ← hxy']
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz₀sq with hz₀y | hz₀y
  · refine ⟨z₀, ?_, ?_⟩
    · -- This branch already has the prescribed derivative.
      exact by simpa [hz₀x, hz₀y]
    · intro z'
      constructor
      · intro hz'
        have hweier : ℘[L] z' = ℘[L] z₀ := by
          exact (congrArg Prod.fst hz').trans hz₀x.symm
        rcases hfiber z₀.2 z'.2 hweier with hdiff | hsum
        · exact hdiff
        · -- The second fiber branch can only occur when `℘'` vanishes, so it collapses to
          -- the same lattice class by the branch classification.
          have hderiv_eq : ℘'[L] z' = ℘'[L] z₀ := by
            exact (congrArg Prod.snd hz').trans hz₀y.symm
          have hsum_deriv : ℘'[L] z' = -℘'[L] z₀ := by
            let l : L.lattice := ⟨(z' : ℂ) + z₀, hsum⟩
            have hz' : (z' : ℂ) = -z₀ + l := by
              change (z' : ℂ) = -z₀ + ((z' : ℂ) + z₀)
              ring
            calc
              ℘'[L] z' = ℘'[L] (-z₀ + l) := by rw [hz']
              _ = ℘'[L] (-z₀) := L.derivWeierstrassP_add_coe (-z₀) l
              _ = -℘'[L] z₀ := L.derivWeierstrassP_neg z₀
          have hz₀deriv_zero : ℘'[L] z₀ = 0 := by
            have hself : ℘'[L] z₀ = -℘'[L] z₀ := hderiv_eq.symm.trans hsum_deriv
            have hsum_zero : ℘'[L] z₀ + ℘'[L] z₀ = 0 := eq_neg_iff_add_eq_zero.mp hself
            have htwo : (2 : ℂ) * ℘'[L] z₀ = 0 := by simpa [two_mul] using hsum_zero
            exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero
          have h2z₀ : 2 * (z₀ : ℂ) ∈ L.lattice := hbranch z₀.2 hz₀deriv_zero
          have hdiff : (z' : ℂ) - z₀ ∈ L.lattice := by
            have hsub : ((z' : ℂ) + z₀) - 2 * (z₀ : ℂ) ∈ L.lattice := sub_mem hsum h2z₀
            have hrewrite : ((z' : ℂ) + z₀) - 2 * (z₀ : ℂ) = (z' : ℂ) - z₀ := by
              ring
            exact hrewrite ▸ hsub
          exact hdiff
      · intro hdiff
        -- Translating by a lattice element preserves both coordinates.
        let l : L.lattice := ⟨(z' : ℂ) - z₀, hdiff⟩
        have hz' : (z' : ℂ) = z₀ + l := by
          change (z' : ℂ) = z₀ + ((z' : ℂ) - z₀)
          ring
        refine Prod.ext ?_ ?_
        · calc
            ℘[L] z' = ℘[L] (z₀ + l) := by rw [hz']
            _ = ℘[L] z₀ := L.weierstrassP_add_coe z₀ l
            _ = x := hz₀x
        · calc
            ℘'[L] z' = ℘'[L] (z₀ + l) := by rw [hz']
            _ = ℘'[L] z₀ := L.derivWeierstrassP_add_coe z₀ l
            _ = y := hz₀y
  · refine ⟨⟨-z₀, ?_⟩, ?_, ?_⟩
    · -- Negation preserves non-membership in the lattice.
      intro hzneg
      exact z₀.2 (by simpa using neg_mem hzneg)
    · -- Flip to the other sheet using evenness of `℘` and oddness of `℘'`.
      refine Prod.ext ?_ ?_
      · simp [hz₀x]
      · simpa [hz₀y] using L.derivWeierstrassP_neg z₀
    · intro z'
      constructor
      · intro hz'
        have hweier : ℘[L] z' = ℘[L] (-z₀) := by
          exact (congrArg Prod.fst hz').trans (by simp [hz₀x])
        rcases hfiber (by
            intro hzneg
            exact z₀.2 (by simpa using neg_mem hzneg)) z'.2 hweier with hdiff | hsum
        · exact hdiff
        · have hderiv_eq : ℘'[L] z' = ℘'[L] (-z₀) := by
            exact (congrArg Prod.snd hz').trans (by simp [hz₀y])
          have hsum_deriv : ℘'[L] z' = -℘'[L] (-z₀) := by
            let l : L.lattice := ⟨(z' : ℂ) + (-z₀), hsum⟩
            have hz' : (z' : ℂ) = -(-z₀) + l := by
              change (z' : ℂ) = -(-z₀) + ((z' : ℂ) + (-z₀))
              ring
            calc
              ℘'[L] z' = ℘'[L] (-(-z₀) + l) := by rw [hz']
              _ = ℘'[L] (-(-z₀)) := L.derivWeierstrassP_add_coe (-(-z₀)) l
              _ = -℘'[L] (-z₀) := L.derivWeierstrassP_neg (-z₀)
          have hz₀deriv_zero : ℘'[L] (-z₀) = 0 := by
            have hself : ℘'[L] (-z₀) = -℘'[L] (-z₀) := hderiv_eq.symm.trans hsum_deriv
            have hsum_zero : ℘'[L] (-z₀) + ℘'[L] (-z₀) = 0 := eq_neg_iff_add_eq_zero.mp hself
            have htwo : (2 : ℂ) * ℘'[L] (-z₀) = 0 := by simpa [two_mul] using hsum_zero
            exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero
          have h2z₀ : 2 * (-((z₀ : ℂ))) ∈ L.lattice := by
            exact hbranch (by
              intro hzneg
              exact z₀.2 (by simpa using neg_mem hzneg)) hz₀deriv_zero
          have hdiff : (z' : ℂ) - (-((z₀ : ℂ))) ∈ L.lattice := by
            have hsub : ((z' : ℂ) + (-((z₀ : ℂ)))) - 2 * (-((z₀ : ℂ))) ∈ L.lattice := sub_mem hsum h2z₀
            have hrewrite :
                ((z' : ℂ) + (-((z₀ : ℂ)))) - 2 * (-((z₀ : ℂ))) = (z' : ℂ) - (-((z₀ : ℂ))) := by
              ring
            exact hrewrite ▸ hsub
          exact hdiff
      · intro hdiff
        let l : L.lattice := ⟨(z' : ℂ) - (-((z₀ : ℂ))), hdiff⟩
        have hz' : (z' : ℂ) = -((z₀ : ℂ)) + l := by
          change (z' : ℂ) = -((z₀ : ℂ)) + ((z' : ℂ) - (-((z₀ : ℂ))))
          ring
        refine Prod.ext ?_ ?_
        · calc
            ℘[L] z' = ℘[L] (-((z₀ : ℂ)) + l) := by rw [hz']
            _ = ℘[L] (-((z₀ : ℂ))) := L.weierstrassP_add_coe (-((z₀ : ℂ))) l
            _ = x := by simpa [hz₀x] using L.weierstrassP_neg (z₀ : ℂ)
        · calc
            ℘'[L] z' = ℘'[L] (-((z₀ : ℂ)) + l) := by rw [hz']
            _ = ℘'[L] (-((z₀ : ℂ))) := L.derivWeierstrassP_add_coe (-((z₀ : ℂ))) l
            _ = y := by simpa [hz₀y] using L.derivWeierstrassP_neg (z₀ : ℂ)

/-- Helper for Proposition 5.2: subtracting a constant preserves the lattice periodicity of `℘`. -/
lemma hasPeriodLattice_weierstrassP_sub_const (L : PeriodPair) (x : ℂ) :
    HasPeriodLattice L (fun w ↦ ℘[L] w - x) := by
  intro ω hω z
  -- The constant term does not affect periodicity, so the period comes from `℘`.
  simpa [sub_eq_add_neg] using
    congrArg (fun u : ℂ ↦ u - x) (L.weierstrassP_add_coe z ⟨ω, hω⟩)

/-- Helper for Proposition 5.2: the translated function `w ↦ ℘[L] w - x` is meromorphic. -/
lemma meromorphic_weierstrassP_sub_const (L : PeriodPair) (x : ℂ) :
    Meromorphic (fun w ↦ ℘[L] w - x) := by
  -- `℘` is meromorphic, and subtracting a constant preserves meromorphicity.
  fun_prop

/-- Helper for Proposition 5.2: subtracting a constant does not change the pole order of `℘` at
a lattice point. -/
lemma meromorphicOrderAt_weierstrassP_sub_const_of_mem_lattice (L : PeriodPair) (x z : ℂ)
    (hz : z ∈ L.lattice) :
    meromorphicOrderAt (fun w ↦ ℘[L] w - x) z = -2 := by
  -- The constant summand has nonnegative order, so the pole of `℘` still dominates.
  have hconst_nonneg : 0 ≤ meromorphicOrderAt (fun _ ↦ (-x : ℂ)) z := by
    by_cases hx : x = 0
    · simp [meromorphicOrderAt_const, hx]
    · have hne : (-x : ℂ) ≠ 0 := by simpa using hx
      simp [meromorphicOrderAt_const, hne]
  have hlt :
      meromorphicOrderAt ℘[L] z < meromorphicOrderAt (fun _ ↦ (-x : ℂ)) z := by
    have horder : meromorphicOrderAt ℘[L] z = (-2 : WithTop ℤ) := by
      simpa using L.order_weierstrassP z hz
    have hlt_zero : (-2 : WithTop ℤ) < 0 := by
      exact WithTop.coe_lt_coe.mpr (by norm_num : (-2 : ℤ) < 0)
    exact horder ▸ lt_of_lt_of_le hlt_zero hconst_nonneg
  -- Reinterpret subtraction as addition of a constant and apply the order comparison lemma.
  calc
    meromorphicOrderAt (fun w ↦ ℘[L] w - x) z =
        meromorphicOrderAt (℘[L]) z := by
          simpa [sub_eq_add_neg] using
            (meromorphicOrderAt_add_eq_left_of_lt
              (f₁ := ℘[L]) (f₂ := fun _ ↦ (-x : ℂ)) (x := z)
              (MeromorphicAt.const (-x) z) hlt)
    _ = -2 := by simpa using L.order_weierstrassP z hz

/-- Helper for Proposition 5.2: on any set containing a lattice point, the divisor of
`w ↦ ℘[L] w - x` has value `-2` at that point. -/
lemma divisor_weierstrassP_sub_const_of_mem_lattice (L : PeriodPair) {P : Set ℂ} {x z : ℂ}
    (hzP : z ∈ P) (hz : z ∈ L.lattice) :
    divisor (fun w ↦ ℘[L] w - x) P z = -2 := by
  -- On the chosen domain, the divisor reads off the local meromorphic order.
  have horder :
      meromorphicOrderAt (fun w ↦ ℘[L] w - x) z = (-2 : WithTop ℤ) :=
    L.meromorphicOrderAt_weierstrassP_sub_const_of_mem_lattice x z hz
  have hne : meromorphicOrderAt (fun w ↦ ℘[L] w - x) z ≠ ⊤ := by
    rw [horder]
    simp
  rw [divisor_apply (L.meromorphic_weierstrassP_sub_const x).meromorphicOn hzP]
  simpa [horder] using (WithTop.untop₀_coe (-2 : ℤ))

/-- Helper for Proposition 5.2: away from the lattice, a nonzero value of `℘[L] z - x` forces
meromorphic order `0`. -/
lemma meromorphicOrderAt_weierstrassP_sub_const_eq_zero_of_not_mem_lattice
    (L : PeriodPair) {x z : ℂ} (hz : z ∉ L.lattice) (hvalue : ℘[L] z ≠ x) :
    meromorphicOrderAt (fun w ↦ ℘[L] w - x) z = (0 : WithTop ℤ) := by
  -- Off the lattice the translated Weierstrass function is analytic, so order `0` is equivalent
  -- to nonvanishing at the center.
  have hanalytic : AnalyticAt ℂ (fun w ↦ ℘[L] w - x) z := by
    exact (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
  have horder : analyticOrderAt (fun w ↦ ℘[L] w - x) z = 0 := by
    rw [hanalytic.analyticOrderAt_eq_zero]
    simpa [sub_eq_zero] using hvalue
  have hmero :
      meromorphicOrderAt (fun w ↦ ℘[L] w - x) z =
        (analyticOrderAt (fun w ↦ ℘[L] w - x) z).map (↑) :=
    hanalytic.meromorphicOrderAt_eq
  rw [hmero, horder]
  simp

/-- Helper for Proposition 5.2: if the boundary of a period parallelogram avoids both the lattice
and the fiber `℘ = x`, then the translated function `w ↦ ℘[L] w - x` has order `0` on that
boundary. -/
lemma boundary_order_zero_of_avoids_lattice_and_fiber (L : PeriodPair) {x z₀ : ℂ}
    (havoid :
      ∀ z ∈ frontier (L.periodParallelogram z₀), z ∉ L.lattice ∧ ℘[L] z ≠ x) :
    ∀ z ∈ frontier (L.periodParallelogram z₀),
      meromorphicOrderAt (fun w ↦ ℘[L] w - x) z = (0 : WithTop ℤ) := by
  intro z hz
  -- The geometric avoidance hypothesis is exactly the analytic nonvanishing input from the
  -- previous lemma.
  exact L.meromorphicOrderAt_weierstrassP_sub_const_eq_zero_of_not_mem_lattice
    (havoid z hz).1 (havoid z hz).2

/-- Helper for Proposition 5.2: every lattice class has a representative in any chosen period
parallelogram. -/
lemma exists_mem_periodParallelogram_sub_lattice (L : PeriodPair) (z z₀ : ℂ) :
    ∃ w : ℂ, w ∈ L.periodParallelogram z₀ ∧ w - z ∈ L.lattice := by
  let c : Fin 2 → ℝ := L.basis.equivFun (z - z₀)
  let w : ℂ := z₀ + Int.fract (c 0) • L.ω₁ + Int.fract (c 1) • L.ω₂
  refine ⟨w, ?_, ?_⟩
  · -- The fractional coordinates land in the closed unit interval, so they define a point of the
    -- chosen period parallelogram.
    refine ⟨Int.fract (c 0), Int.fract (c 1), Int.fract_nonneg _, ?_, Int.fract_nonneg _, ?_, rfl⟩
    · exact le_of_lt (Int.fract_lt_one _)
    · exact le_of_lt (Int.fract_lt_one _)
  · -- Decompose `z - z₀` in the lattice basis and peel off the integer parts of the coordinates.
    have hcoords : z - z₀ = c 0 * L.ω₁ + c 1 * L.ω₂ := by
      simpa [c, smul_eq_mul] using (L.basis.sum_equivFun (z - z₀)).symm
    have hz' : z = z₀ + (c 0 * L.ω₁ + c 1 * L.ω₂) := by
      calc
        z = z₀ + (z - z₀) := by ring
        _ = z₀ + (c 0 * L.ω₁ + c 1 * L.ω₂) := by rw [hcoords]
    have hwz :
        w - z = (((-⌊c 0⌋ : ℤ) : ℂ) * L.ω₁ + (((-⌊c 1⌋ : ℤ) : ℂ)) * L.ω₂) := by
      calc
        w - z =
            (Int.fract (c 0) - c 0) * L.ω₁ + (Int.fract (c 1) - c 1) * L.ω₂ := by
              rw [hz']
              simp [w]
              ring
        _ = (((-⌊c 0⌋ : ℤ) : ℂ) * L.ω₁ + (((-⌊c 1⌋ : ℤ) : ℂ)) * L.ω₂) := by
              have h0 :
                  ((↑(Int.fract (c 0)) : ℂ) - ↑(c 0)) = (((-↑⌊c 0⌋ : ℝ) : ℂ)) := by
                have h0real : (Int.fract (c 0) : ℝ) - c 0 = -↑⌊c 0⌋ := by
                  rw [Int.fract]
                  ring
                exact_mod_cast h0real
              have h0' : (((-↑⌊c 0⌋ : ℝ) : ℂ)) = (((-⌊c 0⌋ : ℤ) : ℂ)) := by
                simp
              have h1 :
                  ((↑(Int.fract (c 1)) : ℂ) - ↑(c 1)) = (((-↑⌊c 1⌋ : ℝ) : ℂ)) := by
                have h1real : (Int.fract (c 1) : ℝ) - c 1 = -↑⌊c 1⌋ := by
                  rw [Int.fract]
                  ring
                exact_mod_cast h1real
              have h1' : (((-↑⌊c 1⌋ : ℝ) : ℂ)) = (((-⌊c 1⌋ : ℤ) : ℂ)) := by
                simp
              rw [h0, h1, h0', h1']
    exact L.mem_lattice.mpr ⟨-⌊c 0⌋, -⌊c 1⌋, hwz.symm⟩

/-- Helper for Proposition 5.2: an off-lattice point can be represented inside any period
parallelogram without introducing a lattice point. -/
lemma exists_nonlattice_mem_periodParallelogram_sub_lattice (L : PeriodPair) {z z₀ : ℂ}
    (hz : z ∉ L.lattice) :
    ∃ w : ℂ, w ∈ L.periodParallelogram z₀ ∧ w ∉ L.lattice ∧ w - z ∈ L.lattice := by
  obtain ⟨w, hwP, hwz⟩ := L.exists_mem_periodParallelogram_sub_lattice z z₀
  refine ⟨w, hwP, ?_, hwz⟩
  intro hwL
  -- Subtract the lattice translation back to recover that the original point would be in the
  -- lattice as well, contradicting the hypothesis.
  have hzL : z ∈ L.lattice := by
    have : w - (w - z) ∈ L.lattice := sub_mem hwL hwz
    simpa using this
  exact hz hzL

/-- Helper for Proposition 5.2: every period parallelogram is compact. -/
lemma isCompact_periodParallelogram (L : PeriodPair) (z₀ : ℂ) :
    IsCompact (L.periodParallelogram z₀) := by
  let e : ℝ × ℝ → ℂ := fun t ↦ z₀ + t.1 • L.ω₁ + t.2 • L.ω₂
  have he : Continuous e := by
    -- The affine-coordinate parametrization is continuous in both real variables.
    continuity
  have himage :
      e '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) = L.periodParallelogram z₀ := by
    ext z
    constructor
    · rintro ⟨⟨t₁, t₂⟩, ht, rfl⟩
      rcases ht with ⟨ht₁, ht₂⟩
      exact ⟨t₁, t₂, ht₁.1, ht₁.2, ht₂.1, ht₂.2, rfl⟩
    · rintro ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
      exact ⟨⟨t₁, t₂⟩, ⟨⟨ht₁0, ht₁1⟩, ⟨ht₂0, ht₂1⟩⟩, rfl⟩
  -- Compactness comes from the closed unit square via this parametrization.
  rw [← himage]
  exact (isCompact_Icc.prod isCompact_Icc).image he

/-- Helper for Proposition 5.2: the basis-coordinate homeomorphism identifies a real pair
`(t₁, t₂)` with the linear combination `t₁ ω₁ + t₂ ω₂`. -/
lemma basis_pair_homeomorph_apply (L : PeriodPair) (p : ℝ × ℝ) :
    (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
      p.1 • L.ω₁ + p.2 • L.ω₂ := by
  -- Expand the inverse basis map through the standard `Fin 2` coordinates.
  calc
    (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
        L.basis.equivFunL.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p) := by
          rfl
    _ = ∑ i : Fin 2,
          L.basis.equivFun
            (L.basis.equivFunL.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p)) i •
            L.basis i := by
          simpa using
            (L.basis.sum_equivFun
              (L.basis.equivFunL.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p))).symm
    _ = ∑ i : Fin 2, ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p) i • L.basis i := by
          congr with i
          exact congrArg (fun a : ℝ ↦ a • L.basis i)
            (congrFun
              (L.basis.equivFunL.apply_symm_apply
                ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p)) i)
    _ = p.1 • L.ω₁ + p.2 • L.ω₂ := by
          simp [Fin.sum_univ_two]

/-- Helper for Proposition 5.2: the inverse coordinate map sends the first `Fin 2` coordinate to
the first basis coefficient. -/
lemma basis_equivFunL_symm_apply_zero (L : PeriodPair) (a b : ℝ) :
    L.basis.equivFun (L.basis.equivFunL.symm ![a, b]) 0 = a := by
  have h := congrFun (L.basis.equivFunL.apply_symm_apply ![a, b]) 0
  simpa using h

/-- Helper for Proposition 5.2: the inverse coordinate map sends the second `Fin 2` coordinate to
the second basis coefficient. -/
lemma basis_equivFunL_symm_apply_one (L : PeriodPair) (a b : ℝ) :
    L.basis.equivFun (L.basis.equivFunL.symm ![a, b]) 1 = b := by
  have h := congrFun (L.basis.equivFunL.apply_symm_apply ![a, b]) 1
  simpa using h

/-- Helper for Proposition 5.2: a frontier point of a period parallelogram has affine coordinates
in `[0, 1]^2`, and at least one coordinate lies on the boundary `{0, 1}`. -/
lemma frontier_periodParallelogram_coord_eq_zero_or_one (L : PeriodPair) {z z₀ : ℂ}
    (hz : z ∈ frontier (L.periodParallelogram z₀)) :
    ∃ t₁ t₂ : ℝ,
      0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧
      z = z₀ + t₁ • L.ω₁ + t₂ • L.ω₂ ∧
      (t₁ = 0 ∨ t₁ = 1 ∨ t₂ = 0 ∨ t₂ = 1) := by
  let e : ℝ × ℝ ≃ₜ ℂ :=
    (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm).toHomeomorph).trans
      (Homeomorph.addLeft z₀)
  let square : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  have himage : e '' square = L.periodParallelogram z₀ := by
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with ⟨hp₁, hp₂⟩
      refine ⟨p.1, p.2, hp₁.1, hp₁.2, hp₂.1, hp₂.2, ?_⟩
      -- Read the image point in the period basis coordinates.
      change
        z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
          z₀ + p.1 • L.ω₁ + p.2 • L.ω₂
      rw [L.basis_pair_homeomorph_apply]
      simp [add_assoc]
    · rintro ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
      refine ⟨(t₁, t₂), ⟨⟨ht₁0, ht₁1⟩, ⟨ht₂0, ht₂1⟩⟩, ?_⟩
      -- The converse direction is the same affine-coordinate expansion.
      change
        z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
          (t₁, t₂) : ℂ) =
          z₀ + t₁ • L.ω₁ + t₂ • L.ω₂
      rw [L.basis_pair_homeomorph_apply]
      simp [add_assoc]
  have hz' : z ∈ e '' frontier square := by
    rw [e.image_frontier, himage]
    exact hz
  rcases hz' with ⟨p, hpfrontier, rfl⟩
  have hpcoords :
      0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 ∧
        (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) := by
    -- Transport the frontier condition back to the unit square.
    change p ∈ frontier (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) at hpfrontier
    have hpfrontier' := hpfrontier
    rw [frontier_prod_eq] at hpfrontier'
    simp [Set.mem_union, Set.mem_prod, Set.mem_Icc] at hpfrontier'
    rcases hpfrontier' with h | h
    · rcases h with ⟨hp₁, hp₂⟩
      rcases hp₂ with hp₂ | hp₂
      · exact ⟨hp₁.1, hp₁.2, by simpa [hp₂], by simpa [hp₂],
          Or.inr (Or.inr (Or.inl hp₂))⟩
      · exact ⟨hp₁.1, hp₁.2, by simpa [hp₂], by simpa [hp₂],
          Or.inr (Or.inr (Or.inr hp₂))⟩
    · rcases h with ⟨hp₁, hp₂⟩
      rcases hp₁ with hp₁ | hp₁
      · exact ⟨by simpa [hp₁], by simpa [hp₁], hp₂.1, hp₂.2, Or.inl hp₁⟩
      · exact ⟨by simpa [hp₁], by simpa [hp₁], hp₂.1, hp₂.2, Or.inr (Or.inl hp₁)⟩
  refine ⟨p.1, p.2, hpcoords.1, hpcoords.2.1, hpcoords.2.2.1, hpcoords.2.2.2.1, ?_,
    hpcoords.2.2.2.2⟩
  -- Translate the recovered square coordinates back to the actual period parallelogram.
  change
    z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
      z₀ + p.1 • L.ω₁ + p.2 • L.ω₂
  rw [L.basis_pair_homeomorph_apply]
  simp [add_assoc]

/-- Helper for Proposition 5.2: lattice points have integral coordinates in the period basis. -/
lemma exists_int_basis_coords_of_mem_lattice (L : PeriodPair) {z : ℂ} (hz : z ∈ L.lattice) :
    ∃ m n : ℤ, L.basis.equivFun z 0 = m ∧ L.basis.equivFun z 1 = n := by
  obtain ⟨m, n, hmn⟩ := L.mem_lattice.mp hz
  have hmn' : z = (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
      ((m : ℝ), (n : ℝ)) : ℂ) := by
    rw [L.basis_pair_homeomorph_apply]
    simpa [smul_eq_mul] using hmn.symm
  refine ⟨m, n, ?_, ?_⟩
  · -- Read the first basis coordinate of the explicit lattice expansion.
    rw [hmn']
    simpa using L.basis_equivFunL_symm_apply_zero (m : ℝ) (n : ℝ)
  · -- Read the second basis coordinate of the explicit lattice expansion.
    rw [hmn']
    simpa using L.basis_equivFunL_symm_apply_one (m : ℝ) (n : ℝ)

/-- Helper for Proposition 5.2: a point of a period parallelogram has basis coordinates in
`[0, 1]^2` after subtracting the basepoint. -/
lemma basis_coords_sub_of_mem_periodParallelogram (L : PeriodPair) {z z₀ : ℂ}
    (hz : z ∈ L.periodParallelogram z₀) :
    ∃ u v : ℝ,
      0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧
      L.basis.equivFun (z - z₀) 0 = u ∧
      L.basis.equivFun (z - z₀) 1 = v := by
  rcases hz with ⟨u, v, hu0, hu1, hv0, hv1, hz⟩
  have hsub :
      z - z₀ = u • L.ω₁ + v • L.ω₂ := by
    -- Subtract the basepoint from the affine-coordinate description of `z`.
    calc
      z - z₀ = (z₀ + u • L.ω₁ + v • L.ω₂) - z₀ := by rw [hz]
      _ = u • L.ω₁ + v • L.ω₂ := by ring
  have hsub' :
      z - z₀ =
        (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
          (u, v) : ℂ) := by
    -- Repackage the affine combination through the basis-coordinate inverse map.
    rw [L.basis_pair_homeomorph_apply]
    exact hsub
  have hcoord0 : L.basis.equivFun (z - z₀) 0 = u := by
    -- Read the first basis coordinate from the inverse basis map.
    rw [hsub']
    simpa using L.basis_equivFunL_symm_apply_zero u v
  have hcoord1 : L.basis.equivFun (z - z₀) 1 = v := by
    -- Read the second basis coordinate from the inverse basis map.
    rw [hsub']
    simpa using L.basis_equivFunL_symm_apply_one u v
  exact ⟨u, v, hu0, hu1, hv0, hv1, hcoord0, hcoord1⟩

/-- Helper for Proposition 5.2: membership in the slanted translate determines the basis
coordinates of the represented point. -/
lemma basis_coords_of_mem_slanted_periodParallelogram (L : PeriodPair) {t : ℝ} {z : ℂ}
    (hz :
      z ∈ L.periodParallelogram (-(t : ℝ) • L.ω₁ - (t / 2 : ℝ) • L.ω₂)) :
    ∃ u v : ℝ,
      0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧
      L.basis.equivFun z 0 = u - t ∧
      L.basis.equivFun z 1 = v - t / 2 := by
  let z₀ : ℂ := -(t : ℝ) • L.ω₁ - (t / 2 : ℝ) • L.ω₂
  obtain ⟨u, v, hu0, hu1, hv0, hv1, hcoord_sub0, hcoord_sub1⟩ :=
    L.basis_coords_sub_of_mem_periodParallelogram (z₀ := z₀) hz
  have hz₀_eq :
      z₀ =
        (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
          (-t, -(t / 2)) : ℂ) := by
    -- The slanted basepoint is the inverse basis image of the pair `(-t, -t / 2)`.
    rw [L.basis_pair_homeomorph_apply]
    simp [z₀, sub_eq_add_neg, add_assoc]
  have hz₀_coord0 : L.basis.equivFun z₀ 0 = -t := by
    -- Read the first basis coordinate of the chosen basepoint.
    rw [hz₀_eq]
    simpa using L.basis_equivFunL_symm_apply_zero (-t) (-(t / 2))
  have hz₀_coord1 : L.basis.equivFun z₀ 1 = -(t / 2) := by
    -- Read the second basis coordinate of the chosen basepoint.
    rw [hz₀_eq]
    simpa using L.basis_equivFunL_symm_apply_one (-t) (-(t / 2))
  have hcoord0 : L.basis.equivFun z 0 = u - t := by
    -- Add back the basepoint to recover the first basis coordinate of `z`.
    calc
      L.basis.equivFun z 0 = L.basis.equivFun ((z - z₀) + z₀) 0 := by
        congr 1
        ring
      _ = L.basis.equivFun (z - z₀) 0 + L.basis.equivFun z₀ 0 := by simp
      _ = u + (-t) := by rw [hcoord_sub0, hz₀_coord0]
      _ = u - t := by ring
  have hcoord1 : L.basis.equivFun z 1 = v - t / 2 := by
    -- Add back the basepoint to recover the second basis coordinate of `z`.
    calc
      L.basis.equivFun z 1 = L.basis.equivFun ((z - z₀) + z₀) 1 := by
        congr 1
        ring
      _ = L.basis.equivFun (z - z₀) 1 + L.basis.equivFun z₀ 1 := by simp
      _ = v + (-(t / 2)) := by rw [hcoord_sub1, hz₀_coord1]
      _ = v - t / 2 := by ring
  exact ⟨u, v, hu0, hu1, hv0, hv1, hcoord0, hcoord1⟩

/-- Helper for Proposition 5.2: a frontier point of the slanted period parallelogram determines
the parameter `t` through one of its two basis coordinates. -/
lemma parameter_eq_of_mem_frontier_slanted_periodParallelogram (L : PeriodPair) {t : ℝ} {z : ℂ}
    (hz :
      z ∈ frontier (L.periodParallelogram (-(t : ℝ) • L.ω₁ - (t / 2 : ℝ) • L.ω₂))) :
    t = -(L.basis.equivFun z 0) ∨
      t = 1 - L.basis.equivFun z 0 ∨
      t = -2 * L.basis.equivFun z 1 ∨
      t = 2 * (1 - L.basis.equivFun z 1) := by
  obtain ⟨u, v, hu0, hu1, hv0, hv1, hz_eq, hedge⟩ :=
    L.frontier_periodParallelogram_coord_eq_zero_or_one hz
  have hcoord0 : L.basis.equivFun z 0 = u - t := by
    have hz_pair :
        z =
          (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
            (u - t, v - t / 2) : ℂ) := by
      -- Package the explicit frontier coordinates through the inverse basis map.
      rw [L.basis_pair_homeomorph_apply]
      calc
        z = -(t : ℝ) • L.ω₁ - (t / 2 : ℝ) • L.ω₂ + u • L.ω₁ + v • L.ω₂ := hz_eq
        _ = (-t • L.ω₁ + u • L.ω₁) + (-(t / 2 : ℝ) • L.ω₂ + v • L.ω₂) := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = (-t + u) • L.ω₁ + (-(t / 2 : ℝ) + v) • L.ω₂ := by
              rw [← add_smul, ← add_smul]
        _ = (u - t) • L.ω₁ + (v - t / 2) • L.ω₂ := by ring
    rw [hz_pair]
    simpa using L.basis_equivFunL_symm_apply_zero (u - t) (v - t / 2)
  have hcoord1 : L.basis.equivFun z 1 = v - t / 2 := by
    have hz_pair :
        z =
          (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
            (u - t, v - t / 2) : ℂ) := by
      -- The same packaged coordinate identity yields the second basis coordinate.
      rw [L.basis_pair_homeomorph_apply]
      calc
        z = -(t : ℝ) • L.ω₁ - (t / 2 : ℝ) • L.ω₂ + u • L.ω₁ + v • L.ω₂ := hz_eq
        _ = (-t • L.ω₁ + u • L.ω₁) + (-(t / 2 : ℝ) • L.ω₂ + v • L.ω₂) := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = (-t + u) • L.ω₁ + (-(t / 2 : ℝ) + v) • L.ω₂ := by
              rw [← add_smul, ← add_smul]
        _ = (u - t) • L.ω₁ + (v - t / 2) • L.ω₂ := by ring
    rw [hz_pair]
    simpa using L.basis_equivFunL_symm_apply_one (u - t) (v - t / 2)
  rcases hedge with rfl | rfl | rfl | rfl
  · -- On the `u = 0` edge, the first basis coordinate is exactly `-t`.
    left
    linarith [hcoord0]
  · -- On the `u = 1` edge, the first basis coordinate is `1 - t`.
    right
    left
    linarith [hcoord0]
  · -- On the `v = 0` edge, the second basis coordinate is `-t / 2`.
    right
    right
    left
    linarith [hcoord1]
  · -- On the `v = 1` edge, the second basis coordinate is `1 - t / 2`.
    right
    right
    right
    linarith [hcoord1]

/-- Helper for Proposition 5.2: away from the lattice, the divisor of `w ↦ ℘[L] w - x` is
nonnegative because the function is analytic there. -/
lemma divisor_weierstrassP_sub_const_nonneg_of_not_mem_lattice (L : PeriodPair)
    {P : Set ℂ} {x z : ℂ} (hzP : z ∈ P) (hz : z ∉ L.lattice) :
    0 ≤ divisor (fun w ↦ ℘[L] w - x) P z := by
  -- Off the lattice the translated Weierstrass function is analytic, so its order cannot be
  -- negative.
  have hanalytic : AnalyticAt ℂ (fun w ↦ ℘[L] w - x) z := by
    exact (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
  rw [divisor_apply (L.meromorphic_weierstrassP_sub_const x).meromorphicOn hzP]
  exact WithTop.untop₀_nonneg.2 hanalytic.meromorphicOrderAt_nonneg

/-- Helper for Proposition 5.2: the period lattice is the range of the integer coordinate map in
the period basis. -/
lemma lattice_eq_range_period_coordinates (L : PeriodPair) :
    (L.lattice : Set ℂ) =
      Set.range (fun mn : ℤ × ℤ ↦ (mn.1 : ℂ) * L.ω₁ + (mn.2 : ℂ) * L.ω₂) := by
  ext z
  constructor
  · intro hz
    rcases L.mem_lattice.mp hz with ⟨m, n, hmn⟩
    exact ⟨(m, n), by simpa using hmn⟩
  · rintro ⟨⟨m, n⟩, hmn⟩
    exact L.mem_lattice.mpr ⟨m, n, by simpa using hmn⟩

/-- Helper for Proposition 5.2: the complement of the period lattice is preconnected. -/
lemma isPreconnected_compl_lattice (L : PeriodPair) :
    IsPreconnected (L.latticeᶜ : Set ℂ) := by
  let f : ℤ × ℤ → ℂ := fun mn ↦ (mn.1 : ℂ) * L.ω₁ + (mn.2 : ℂ) * L.ω₂
  have hcount : (Set.range f).Countable := Set.countable_range f
  have hpath : IsPathConnected (((Set.range f)ᶜ : Set ℂ)) :=
    hcount.isPathConnected_compl_of_one_lt_rank (by
      simp only [Complex.rank_real_complex, Nat.one_lt_ofNat])
  simpa [f, L.lattice_eq_range_period_coordinates] using hpath.isConnected.isPreconnected

/-- Helper for Proposition 5.2: off the lattice, `w ↦ ℘[L] w - x` cannot vanish on a whole
neighborhood. -/
lemma analyticOrderAt_weierstrassP_sub_const_ne_top_of_not_mem_lattice (L : PeriodPair)
    {x z : ℂ} (hz : z ∉ L.lattice) :
    analyticOrderAt (fun w ↦ ℘[L] w - x) z ≠ ⊤ := by
  -- Route correction: the missing source-faithful bridge is to spread local vanishing across the
  -- connected complement of the lattice and then contradict the known pole at the origin.
  let f : ℂ → ℂ := fun w ↦ ℘[L] w - x
  have hf : AnalyticOnNhd ℂ f (L.latticeᶜ : Set ℂ) := by
    intro w hw
    exact (L.analyticOnNhd_weierstrassP w hw).sub analyticAt_const
  have hconnected : IsPreconnected (L.latticeᶜ : Set ℂ) := L.isPreconnected_compl_lattice
  intro htop
  have hzero_local : f =ᶠ[𝓝 z] 0 := by
    simpa [f] using analyticOrderAt_eq_top.mp htop
  have hzero_global : Set.EqOn f 0 (L.latticeᶜ : Set ℂ) :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconnected hz hzero_local
  have hnear_lattice :
      ((↑L.lattice \ ({(0 : ℂ)} : Set ℂ))ᶜ : Set ℂ) ∈ 𝓝[≠] (0 : ℂ) :=
    mem_nhdsWithin_of_mem_nhds (L.compl_lattice_diff_singleton_mem_nhds 0)
  have hzero_punctured : ∀ᶠ w in 𝓝[≠] (0 : ℂ), f w = 0 := by
    -- Near the origin, the punctured neighborhood avoids the whole lattice, so the global `EqOn`
    -- statement specializes to a punctured-neighborhood vanishing statement.
    filter_upwards [self_mem_nhdsWithin, hnear_lattice] with w hw0 hwnear
    have hw_not_lattice : w ∉ L.lattice := by
      intro hwL
      have hw_mem_diff : w ∈ (↑L.lattice \ ({(0 : ℂ)} : Set ℂ) : Set ℂ) := by
        refine ⟨hwL, ?_⟩
        simpa [Set.mem_compl_iff] using hw0
      exact hwnear hw_mem_diff
    have hw_zero : f w = 0 := hzero_global hw_not_lattice
    simpa [f] using hw_zero
  have horder_top : meromorphicOrderAt f (0 : ℂ) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    exact hzero_punctured
  have hzero_mem : (0 : ℂ) ∈ L.lattice := by
    simpa using (zero_mem L.lattice)
  have horder_zero :=
    L.meromorphicOrderAt_weierstrassP_sub_const_of_mem_lattice x 0 hzero_mem
  rw [horder_zero] at horder_top
  simp at horder_top

/-- Helper for Proposition 5.2: away from the lattice, positivity of the divisor of
`w ↦ ℘[L] w - x` is equivalent to the fiber condition `℘[L] z = x`. -/
lemma divisor_weierstrassP_sub_const_pos_iff_of_not_mem_lattice (L : PeriodPair)
    {P : Set ℂ} {x z : ℂ} (hzP : z ∈ P) (hz : z ∉ L.lattice) :
    0 < divisor (fun w ↦ ℘[L] w - x) P z ↔ ℘[L] z = x := by
  -- Route correction: after excluding the `analyticOrderAt = ⊤` branch off the lattice, divisor
  -- positivity is just the usual analytic statement that a zero has positive order.
  let f : ℂ → ℂ := fun w ↦ ℘[L] w - x
  have hanalytic : AnalyticAt ℂ f z := by
    exact (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
  have hnot_top : analyticOrderAt f z ≠ ⊤ :=
    L.analyticOrderAt_weierstrassP_sub_const_ne_top_of_not_mem_lattice hz
  constructor
  · intro hzdiv
    by_contra hzx
    have horder_zero : analyticOrderAt f z = 0 := by
      rw [hanalytic.analyticOrderAt_eq_zero]
      simpa [f, sub_eq_zero] using hzx
    have hdiv_zero : divisor f P z = 0 := by
      rw [divisor_apply (L.meromorphic_weierstrassP_sub_const x).meromorphicOn hzP,
        hanalytic.meromorphicOrderAt_eq, horder_zero]
      simp
    exact (ne_of_gt hzdiv) hdiv_zero
  · intro hzx
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnot_top
    have hfz : f z = 0 := by
      simp [f, hzx]
    have horder_ne_zero : analyticOrderAt f z ≠ 0 :=
      (hanalytic.analyticOrderAt_ne_zero).2 hfz
    have hn_ne_zero : n ≠ 0 := by
      intro hn0
      exact horder_ne_zero (by simpa [hn0] using hn.symm)
    have hdiv_eq : divisor f P z = (n : ℤ) := by
      rw [divisor_apply (L.meromorphic_weierstrassP_sub_const x).meromorphicOn hzP,
        hanalytic.meromorphicOrderAt_eq, ← hn]
      simp
    have hdiv_ne_zero : divisor f P z ≠ 0 := by
      rw [hdiv_eq]
      exact_mod_cast hn_ne_zero
    have hnonneg : 0 ≤ divisor f P z :=
      L.divisor_weierstrassP_sub_const_nonneg_of_not_mem_lattice hzP hz
    exact lt_of_le_of_ne hnonneg (Ne.symm hdiv_ne_zero)

/-- Helper for Proposition 5.2: if a period parallelogram contains no lattice point except `0`,
then the only pole representative for `w ↦ ℘[L] w - x` is `0`. -/
lemma pole_representatives_weierstrassP_sub_const_singleton (L : PeriodPair) {x z₀ : ℂ}
    (hzero : 0 ∈ L.periodParallelogram z₀)
    (hlattice :
      ∀ z ∈ L.periodParallelogram z₀, z ∈ L.lattice → z = 0) :
    IsPoleRepresentativeSet (fun w ↦ ℘[L] w - x) (L.periodParallelogram z₀) ({0} : Finset ℂ) := by
  intro z
  constructor
  · intro hz
    simp at hz
    subst hz
    constructor
    · exact hzero
    · rw [L.divisor_weierstrassP_sub_const_of_mem_lattice hzero (by simp)]
      norm_num
  · intro hz
    rcases hz with ⟨hzP, hzneg⟩
    by_cases hzL : z ∈ L.lattice
    · -- Any lattice pole inside the parallelogram is forced to be the distinguished origin.
      simpa [hlattice z hzP hzL] using hzP
    · -- Off the lattice the divisor is analytic, hence cannot be negative.
      have hnonneg :
          0 ≤ divisor (fun w ↦ ℘[L] w - x) (L.periodParallelogram z₀) z :=
        L.divisor_weierstrassP_sub_const_nonneg_of_not_mem_lattice hzP hzL
      exact False.elim (not_lt_of_ge hnonneg hzneg)

/-- Helper for Proposition 5.2: every period parallelogram admits a finite representative set for
the positive divisor of `w ↦ ℘[L] w - x`. -/
lemma exists_zero_representatives_weierstrassP_sub_const (L : PeriodPair) {x z₀ : ℂ}
    (_havoid :
      ∀ z ∈ frontier (L.periodParallelogram z₀), z ∉ L.lattice ∧ ℘[L] z ≠ x)
    (_hlattice :
      ∀ z ∈ L.periodParallelogram z₀, z ∈ L.lattice → z = 0) :
    ∃ roots : Finset ℂ,
      IsZeroRepresentativeSet (fun w ↦ ℘[L] w - x) (L.periodParallelogram z₀) roots := by
  let D := divisor (fun w ↦ ℘[L] w - x) (L.periodParallelogram z₀)
  let hfin : Set.Finite (D⁺).support := (D⁺).finiteSupport (L.isCompact_periodParallelogram z₀)
  refine ⟨hfin.toFinset, ?_⟩
  intro z
  constructor
  · intro hz
    have hzsupport : z ∈ (D⁺).support := by
      simpa [hfin] using hz
    have hzP : z ∈ L.periodParallelogram z₀ := (D⁺).supportWithinDomain hzsupport
    have hzpos : 0 < D z := by
      have hzneq : (D z)⁺ ≠ 0 := by
        simpa [D, Function.locallyFinsuppWithin.posPart_apply] using hzsupport
      have hznot : ¬ D z ≤ 0 := by
        intro hzle
        exact hzneq (posPart_eq_zero.2 hzle)
      exact lt_of_not_ge hznot
    exact ⟨hzP, hzpos⟩
  · rintro ⟨hzP, hzpos⟩
    have hzsupport : z ∈ (D⁺).support := by
      change (D z)⁺ ≠ 0
      exact ne_of_gt (by simpa [D, Function.locallyFinsuppWithin.posPart_apply] using posPart_pos hzpos)
    simpa [hfin] using hzsupport

/-- Helper for Proposition 5.2: each point of an off-lattice fiber inside a closed ball
contributes to the positive divisor support on that ball. -/
lemma fiber_closedBall_subset_positive_divisor_support (L : PeriodPair) {x z : ℂ} {n : ℕ}
    (hzball : z ∈ Metric.closedBall (0 : ℂ) n) (hz : z ∉ L.lattice) (hzx : ℘[L] z = x) :
    z ∈ ((divisor (fun w ↦ ℘[L] w - x) (Metric.closedBall (0 : ℂ) n))⁺).support := by
  -- Route correction: package the off-lattice fiber condition into divisor positivity on a compact
  -- closed ball so the source proof can use a countable union of finite supports.
  have hzpos :
      0 < divisor (fun w ↦ ℘[L] w - x) (Metric.closedBall (0 : ℂ) n) z :=
    (L.divisor_weierstrassP_sub_const_pos_iff_of_not_mem_lattice hzball hz).2 hzx
  -- Positive divisor multiplicity is exactly membership in the support of the positive part.
  change (divisor (fun w ↦ ℘[L] w - x) (Metric.closedBall (0 : ℂ) n) z)⁺ ≠ 0
  exact ne_of_gt (by simpa [Function.locallyFinsuppWithin.posPart_apply] using posPart_pos hzpos)

/-- Helper for Proposition 5.2: every off-lattice level set of `℘` is countable. -/
lemma weierstrassP_level_set_countable (L : PeriodPair) (x : ℂ) :
    Set.Countable {z : ℂ | z ∉ L.lattice ∧ ℘[L] z = x} := by
  let slice : ℕ → Set ℂ :=
    fun n ↦ {z : ℂ | z ∈ Metric.closedBall (0 : ℂ) n ∧ z ∉ L.lattice ∧ ℘[L] z = x}
  have hslice_countable : ∀ n : ℕ, Set.Countable (slice n) := by
    intro n
    let D := divisor (fun w ↦ ℘[L] w - x) (Metric.closedBall (0 : ℂ) n)
    have hfinite : Set.Finite (D⁺).support := (D⁺).finiteSupport (isCompact_closedBall (0 : ℂ) n)
    refine hfinite.countable.mono ?_
    intro z hz
    rcases hz with ⟨hzball, hznotL, hzx⟩
    -- Each closed-ball fiber slice embeds in the positive support of the corresponding divisor.
    simpa [D] using L.fiber_closedBall_subset_positive_divisor_support hzball hznotL hzx
  -- Cartan's source proof writes the full fiber as a countable union of these finite slices.
  refine (Set.countable_iUnion hslice_countable).mono ?_
  intro z hz
  rcases hz with ⟨hznotL, hzx⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
  refine Set.mem_iUnion.2 ⟨n, ?_⟩
  refine ⟨?_, hznotL, hzx⟩
  -- Choose a closed ball large enough to contain `z`.
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hn

/-- Helper for Proposition 5.2: the slanted boundary parameters excluded by the lattice and the
fiber `℘ = x` form a countable set. -/
lemma countable_slanted_bad_parameters (L : PeriodPair) (x : ℂ) :
    Set.Countable
      {t : ℝ | ∃ z : ℂ,
        (z ∈ L.lattice ∨ z ∉ L.lattice ∧ ℘[L] z = x) ∧
          (t = -(L.basis.equivFun z 0) ∨
            t = 1 - L.basis.equivFun z 0 ∨
            t = -2 * L.basis.equivFun z 1 ∨
            t = 2 * (1 - L.basis.equivFun z 1))} := by
  let S : Set ℂ := (L.lattice : Set ℂ) ∪ {z : ℂ | z ∉ L.lattice ∧ ℘[L] z = x}
  let A₁ : Set ℝ := (fun z : ℂ ↦ -(L.basis.equivFun z 0)) '' S
  let A₂ : Set ℝ := (fun z : ℂ ↦ 1 - L.basis.equivFun z 0) '' S
  let A₃ : Set ℝ := (fun z : ℂ ↦ -2 * L.basis.equivFun z 1) '' S
  let A₄ : Set ℝ := (fun z : ℂ ↦ 2 * (1 - L.basis.equivFun z 1)) '' S
  let A : Set ℝ := A₁ ∪ (A₂ ∪ (A₃ ∪ A₄))
  have hlattice : Set.Countable (L.lattice : Set ℂ) := by
    -- The period lattice is the image of `ℤ × ℤ` under the coordinate parametrization.
    simpa [L.lattice_eq_range_period_coordinates] using
      (Set.countable_range fun mn : ℤ × ℤ ↦
        (mn.1 : ℂ) * L.ω₁ + (mn.2 : ℂ) * L.ω₂)
  have hS : Set.Countable S := by
    -- The bad complex points are exactly lattice points together with the countable fiber.
    exact hlattice.union (L.weierstrassP_level_set_countable x)
  have hA₁ : Set.Countable A₁ := by
    -- Each coordinate expression is a countable image of the same bad complex set.
    exact hS.image (fun z : ℂ ↦ -(L.basis.equivFun z 0))
  have hA₂ : Set.Countable A₂ := by
    exact hS.image (fun z : ℂ ↦ 1 - L.basis.equivFun z 0)
  have hA₃ : Set.Countable A₃ := by
    exact hS.image (fun z : ℂ ↦ -2 * L.basis.equivFun z 1)
  have hA₄ : Set.Countable A₄ := by
    exact hS.image (fun z : ℂ ↦ 2 * (1 - L.basis.equivFun z 1))
  have hA : Set.Countable A := by
    exact hA₁.union (hA₂.union (hA₃.union hA₄))
  refine hA.mono ?_
  intro t ht
  rcases ht with ⟨z, hz, hparam⟩
  have hzS : z ∈ S := by
    rcases hz with hzL | hzx
    · exact Or.inl hzL
    · exact Or.inr hzx
  rcases hparam with rfl | rfl | rfl | rfl
  · exact by
      change -(L.basis.equivFun z 0) ∈ A
      exact Or.inl ⟨z, hzS, rfl⟩
  · exact by
      change 1 - L.basis.equivFun z 0 ∈ A
      exact Or.inr (Or.inl ⟨z, hzS, rfl⟩)
  · exact by
      change -2 * L.basis.equivFun z 1 ∈ A
      exact Or.inr (Or.inr (Or.inl ⟨z, hzS, rfl⟩))
  · exact by
      change 2 * (1 - L.basis.equivFun z 1) ∈ A
      exact Or.inr (Or.inr (Or.inr ⟨z, hzS, rfl⟩))

/-- Helper for Proposition 5.2: for any target value `x`, one can choose a slanted translate of
the period parallelogram whose boundary avoids both the lattice and the fiber `℘ = x`, while the
parallelogram contains no lattice point other than the origin. -/
lemma exists_boundary_generic_periodParallelogram (L : PeriodPair) (x : ℂ) :
    ∃ t : ℝ,
      0 < t ∧ t < 1 ∧
      let z₀ := -(t : ℝ) • L.ω₁ - (t / 2 : ℝ) • L.ω₂
      0 ∈ L.periodParallelogram z₀ ∧
        (∀ z ∈ frontier (L.periodParallelogram z₀), z ∉ L.lattice ∧ ℘[L] z ≠ x) ∧
        (∀ z ∈ L.periodParallelogram z₀, z ∈ L.lattice → z = 0) := by
  let badSet : Set ℝ :=
    {t : ℝ | ∃ z : ℂ,
      (z ∈ L.lattice ∨ z ∉ L.lattice ∧ ℘[L] z = x) ∧
        (t = -(L.basis.equivFun z 0) ∨
          t = 1 - L.basis.equivFun z 0 ∨
          t = -2 * L.basis.equivFun z 1 ∨
          t = 2 * (1 - L.basis.equivFun z 1))}
  have hbad : Set.Countable badSet := by
    simpa [badSet] using L.countable_slanted_bad_parameters x
  have hdense : Dense (badSetᶜ : Set ℝ) := by
    simpa using (Set.Countable.dense_compl (𝕜 := ℝ) hbad)
  have hunit_nonempty : (Set.Ioo (0 : ℝ) 1).Nonempty := by
    refine ⟨1 / 2, ?_⟩
    norm_num
  have hchoice : (Set.Ioo (0 : ℝ) 1 ∩ (badSetᶜ : Set ℝ)).Nonempty :=
    hdense.inter_open_nonempty (Set.Ioo (0 : ℝ) 1) isOpen_Ioo hunit_nonempty
  rcases hchoice with ⟨t, htunit, htbad⟩
  have htbad_not : t ∉ badSet := by
    simpa [Set.mem_compl_iff] using htbad
  have ht0 : 0 < t := htunit.1
  have ht1 : t < 1 := htunit.2
  refine ⟨t, ht0, ht1, ?_⟩
  dsimp
  constructor
  · -- The chosen slanted translate still contains the origin.
    refine ⟨t, t / 2, le_of_lt ht0, le_of_lt ht1, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · change 0 = -(t : ℝ) • L.ω₁ - (t / 2 : ℝ) • L.ω₂ + t • L.ω₁ + (t / 2 : ℝ) • L.ω₂
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (neg_add_cancel ((t : ℝ) • L.ω₁)).symm
  constructor
  · intro z hzfront
    have hparam := L.parameter_eq_of_mem_frontier_slanted_periodParallelogram hzfront
    have hznotL : z ∉ L.lattice := by
      -- A boundary lattice point would put `t` into the forbidden countable bad set.
      intro hzL
      exact htbad_not ⟨z, ⟨Or.inl hzL, hparam⟩⟩
    refine ⟨hznotL, ?_⟩
    intro hzx
    -- The same bad-parameter exclusion rules out boundary points on the fiber `℘ = x`.
    exact htbad_not ⟨z, ⟨Or.inr ⟨hznotL, hzx⟩, hparam⟩⟩
  · intro z hzP hzL
    obtain ⟨u, v, hu0, hu1, hv0, hv1, hcoord0, hcoord1⟩ :=
      L.basis_coords_of_mem_slanted_periodParallelogram hzP
    obtain ⟨m, n, hm, hn⟩ := L.exists_int_basis_coords_of_mem_lattice hzL
    have hm_eq : (m : ℝ) = u - t := by
      -- Compare the integer lattice coordinate with the slanted-coordinate expression.
      calc
        (m : ℝ) = L.basis.equivFun z 0 := by simpa using hm.symm
        _ = u - t := hcoord0
    have hn_eq : (n : ℝ) = v - t / 2 := by
      calc
        (n : ℝ) = L.basis.equivFun z 1 := by simpa using hn.symm
        _ = v - t / 2 := hcoord1
    have hm_low : (-1 : ℝ) < (m : ℝ) := by
      linarith [hu0, ht1, hm_eq]
    have hm_high : (m : ℝ) < 1 := by
      linarith [hu1, ht0, hm_eq]
    have hn_low : (-1 : ℝ) < (n : ℝ) := by
      linarith [hv0, ht1, hn_eq]
    have hn_high : (n : ℝ) < 1 := by
      linarith [hv1, ht0, hn_eq]
    have hm_low_int : (-1 : ℤ) < m := by
      exact_mod_cast hm_low
    have hm_high_int : m < 1 := by
      exact_mod_cast hm_high
    have hn_low_int : (-1 : ℤ) < n := by
      exact_mod_cast hn_low
    have hn_high_int : n < 1 := by
      exact_mod_cast hn_high
    have hm_zero : m = 0 := by
      omega
    have hn_zero : n = 0 := by
      omega
    have hzcoord0 : L.basis.equivFun z 0 = 0 := by
      simpa [hm_zero] using hm
    have hzcoord1 : L.basis.equivFun z 1 = 0 := by
      simpa [hn_zero] using hn
    -- Vanishing of both basis coordinates forces the lattice point itself to be the origin.
    apply L.basis.equivFun.injective
    ext i
    fin_cases i
    · simpa [hzcoord0]
    · simpa [hzcoord1]

/-- Helper for Proposition 5.2: on a boundary-generic period parallelogram, Proposition 5.1
packages the fiber representatives of `℘ = x` into total multiplicity `2`. -/
lemma exists_fiber_representatives_sum_divisor_eq_two (L : PeriodPair) {x z₀ : ℂ}
    (hzero : 0 ∈ L.periodParallelogram z₀)
    (havoid :
      ∀ z ∈ frontier (L.periodParallelogram z₀), z ∉ L.lattice ∧ ℘[L] z ≠ x)
    (hlattice :
      ∀ z ∈ L.periodParallelogram z₀, z ∈ L.lattice → z = 0) :
    ∃ roots : Finset ℂ,
      (∀ z : ℂ, z ∈ roots ↔ z ∈ L.periodParallelogram z₀ ∧ z ∉ L.lattice ∧ ℘[L] z = x) ∧
      roots.sum (fun z ↦ divisor (fun w ↦ ℘[L] w - x) (L.periodParallelogram z₀) z) = 2 := by
  classical
  obtain ⟨roots, hroots⟩ :=
    L.exists_zero_representatives_weierstrassP_sub_const havoid hlattice
  have hpoles :
      IsPoleRepresentativeSet (fun w ↦ ℘[L] w - x) (L.periodParallelogram z₀) ({0} : Finset ℂ) :=
    L.pole_representatives_weierstrassP_sub_const_singleton hzero hlattice
  have hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀),
        meromorphicOrderAt (fun w ↦ ℘[L] w - x) z = (0 : WithTop ℤ) :=
    L.boundary_order_zero_of_avoids_lattice_and_fiber havoid
  have hsum :=
    zero_multiplicity_sum_eq_pole_multiplicity_sum_in_period_parallelogram
      (L := L) (z₀ := z₀) (hf := L.meromorphic_weierstrassP_sub_const x)
      (hperiods := L.hasPeriodLattice_weierstrassP_sub_const x) hboundary roots ({0} : Finset ℂ)
      hroots hpoles
  refine ⟨roots, ?_, ?_⟩
  · intro z
    constructor
    · intro hz
      rcases (hroots.mem_iff z).1 hz with ⟨hzP, hzdiv⟩
      have hznotL : z ∉ L.lattice := by
        intro hzL
        have hdiv :
            divisor (fun w ↦ ℘[L] w - x) (L.periodParallelogram z₀) z = -2 :=
          L.divisor_weierstrassP_sub_const_of_mem_lattice hzP hzL
        have : ¬ 0 < divisor (fun w ↦ ℘[L] w - x) (L.periodParallelogram z₀) z := by
          simpa [hdiv]
        exact this hzdiv
      exact ⟨hzP, hznotL,
        (L.divisor_weierstrassP_sub_const_pos_iff_of_not_mem_lattice hzP hznotL).1 hzdiv⟩
    · rintro ⟨hzP, hznotL, hzx⟩
      exact (hroots.mem_iff z).2 ⟨hzP,
        (L.divisor_weierstrassP_sub_const_pos_iff_of_not_mem_lattice hzP hznotL).2 hzx⟩
  · -- Proposition 5.1 reduces the full root sum to the unique pole at the origin.
    simpa [L.divisor_weierstrassP_sub_const_of_mem_lattice hzero (by simp)] using hsum

/-- Helper for Proposition 5.2: a branch point of `℘` contributes multiplicity at least `2` to
the divisor of `w ↦ ℘[L] w - x`. -/
lemma divisor_weierstrassP_sub_const_ge_two_of_deriv_eq_zero (L : PeriodPair)
    {x z z₀ : ℂ} (hzP : z ∈ L.periodParallelogram z₀) (hz : z ∉ L.lattice)
    (hzx : ℘[L] z = x) (hderiv : ℘'[L] z = 0) :
    2 ≤ divisor (fun w ↦ ℘[L] w - x) (L.periodParallelogram z₀) z := by
  -- The zeroth and first iterated derivatives of `w ↦ ℘[L] w - x` vanish at a branch point, so
  -- the analytic order is at least `2`; the new non-top bridge converts that into divisor data.
  let f : ℂ → ℂ := fun w ↦ ℘[L] w - x
  have hanalytic : AnalyticAt ℂ f z := by
    exact (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
  have hnot_top : analyticOrderAt f z ≠ ⊤ :=
    L.analyticOrderAt_weierstrassP_sub_const_ne_top_of_not_mem_lattice hz
  have horder_ge : (2 : ℕ∞) ≤ analyticOrderAt f z := by
    change (2 : ℕ) ≤ analyticOrderAt f z
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanalytic]
    intro i hi
    interval_cases i
    · simpa [f, hzx]
    · simpa [f, iteratedDeriv_one] using hderiv
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnot_top
  have hn_ge : 2 ≤ n := by
    exact ENat.coe_le_coe.mp (by simpa [hn] using horder_ge)
  have hdiv_eq :
      divisor (fun w ↦ ℘[L] w - x) (L.periodParallelogram z₀) z = (n : ℤ) := by
    rw [divisor_apply (L.meromorphic_weierstrassP_sub_const x).meromorphicOn hzP,
      hanalytic.meromorphicOrderAt_eq, ← hn]
    simp
  rw [hdiv_eq]
  exact_mod_cast hn_ge

/-- Helper for Proposition 5.2: inside a boundary-generic period parallelogram, two non-lattice
points on the same `℘`-fiber differ by sign modulo the lattice. -/
lemma eq_or_neg_mod_lattice_of_same_weierstrassP_generic (L : PeriodPair)
    {x z₀ u v : ℂ}
    (hzero : 0 ∈ L.periodParallelogram z₀)
    (havoid :
      ∀ z ∈ frontier (L.periodParallelogram z₀), z ∉ L.lattice ∧ ℘[L] z ≠ x)
    (hlattice :
      ∀ z ∈ L.periodParallelogram z₀, z ∈ L.lattice → z = 0)
    (huP : u ∈ L.periodParallelogram z₀)
    (hvP : v ∈ L.periodParallelogram z₀)
    (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice)
    (hux : ℘[L] u = x)
    (hvx : ℘[L] v = x) :
    v - u ∈ L.lattice ∨ v + u ∈ L.lattice := by
  classical
  obtain ⟨roots, hroots, hsum⟩ :=
    L.exists_fiber_representatives_sum_divisor_eq_two hzero havoid hlattice
  let d : ℂ → ℤ := fun z ↦ divisor (fun w ↦ ℘[L] w - x) (L.periodParallelogram z₀) z
  have hsum_d : roots.sum d = 2 := by simpa [d] using hsum
  have hroot_pos : ∀ {z : ℂ}, z ∈ roots → 0 < d z := by
    intro z hz
    rcases (hroots z).1 hz with ⟨hzP, hzL, hzx⟩
    exact (L.divisor_weierstrassP_sub_const_pos_iff_of_not_mem_lattice hzP hzL).2 hzx
  have hu_root : u ∈ roots := (hroots u).2 ⟨huP, hu, hux⟩
  have hv_root : v ∈ roots := (hroots v).2 ⟨hvP, hv, hvx⟩
  obtain ⟨w, hwP, hw, hwshift⟩ :=
    L.exists_nonlattice_mem_periodParallelogram_sub_lattice (z := -u) (z₀ := z₀) (by
      simpa using hu)
  have hwu : w + u ∈ L.lattice := by simpa using hwshift
  have hwx : ℘[L] w = x := by
    -- Represent `w` as `-u` plus a lattice period and use evenness of `℘`.
    let l : L.lattice := ⟨w + u, hwu⟩
    have hw_eq : w = -u + l := by
      change w = -u + (w + u)
      ring
    calc
      ℘[L] w = ℘[L] (-u + l) := by rw [hw_eq]
      _ = ℘[L] (-u) := L.weierstrassP_add_coe (-u) l
      _ = ℘[L] u := L.weierstrassP_neg u
      _ = x := hux
  have hw_root : w ∈ roots := (hroots w).2 ⟨hwP, hw, hwx⟩
  have hu_ge_one : 1 ≤ d u := by
    have hpos := hroot_pos hu_root
    omega
  have hv_ge_one : 1 ≤ d v := by
    have hpos := hroot_pos hv_root
    omega
  have hw_ge_one : 1 ≤ d w := by
    have hpos := hroot_pos hw_root
    omega
  by_cases hwu_eq : w = u
  · -- If the negative-sheet representative coincides with `u`, then `u` is a branch point and
    -- already consumes the whole multiplicity-two fiber.
    have h2u : 2 * u ∈ L.lattice := by simpa [two_mul, hwu_eq] using hwu
    have hderiv_u : ℘'[L] u = 0 :=
      L.derivWeierstrassP_eq_zero_of_two_mul_mem_lattice hu h2u
    have hu_ge_two : 2 ≤ d u :=
      L.divisor_weierstrassP_sub_const_ge_two_of_deriv_eq_zero huP hu hux hderiv_u
    by_cases hvu : v = u
    · left
      simpa [hvu]
    · have hv_mem : v ∈ roots.erase u := by simpa [hvu] using hv_root
      have hv_le :
          d v ≤ (roots.erase u).sum d := by
        exact Finset.single_le_sum
          (fun z hz ↦ le_of_lt (hroot_pos (Finset.mem_of_mem_erase hz))) hv_mem
      have hsum_le : d u + d v ≤ roots.sum d := by
        rw [← roots.sum_erase_add d hu_root]
        linarith
      have hsum_le_two : d u + d v ≤ 2 := by
        linarith [hsum_d, hsum_le]
      omega
  · by_cases hvu : v = u
    · left
      simpa [hvu]
    · by_cases hvw : v = w
      · right
        simpa [hvw] using hwu
      · have hw_mem : w ∈ roots.erase u := by simpa [hwu_eq] using hw_root
        have hv_mem : v ∈ (roots.erase u).erase w := by
          simp [Finset.mem_erase, hvu, hvw, hv_root, hwu_eq]
        have hv_le :
            d v ≤ ((roots.erase u).erase w).sum d := by
          exact Finset.single_le_sum
            (fun z hz ↦
              le_of_lt (hroot_pos (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))))
            hv_mem
        have hsum_erase_w :
            d w + ((roots.erase u).erase w).sum d = (roots.erase u).sum d := by
          simpa [add_comm] using (roots.erase u).sum_erase_add d hw_mem
        have hsum_total : d u + d w + d v ≤ roots.sum d := by
          rw [← roots.sum_erase_add d hu_root, ← hsum_erase_w]
          linarith
        have hsum_total_two : d u + d w + d v ≤ 2 := by
          linarith [hsum_d, hsum_total]
        omega

/-- Helper for Proposition 5.2: inside a boundary-generic period parallelogram, a branch point of
`℘` is fixed by negation modulo the period lattice. -/
lemma two_mul_mem_lattice_of_deriv_eq_zero_generic (L : PeriodPair)
    {x z₀ u : ℂ}
    (hzero : 0 ∈ L.periodParallelogram z₀)
    (havoid :
      ∀ z ∈ frontier (L.periodParallelogram z₀), z ∉ L.lattice ∧ ℘[L] z ≠ x)
    (hlattice :
      ∀ z ∈ L.periodParallelogram z₀, z ∈ L.lattice → z = 0)
    (huP : u ∈ L.periodParallelogram z₀)
    (hu : u ∉ L.lattice)
    (hux : ℘[L] u = x)
    (hderiv : ℘'[L] u = 0) :
    2 * u ∈ L.lattice := by
  classical
  obtain ⟨roots, hroots, hsum⟩ :=
    L.exists_fiber_representatives_sum_divisor_eq_two hzero havoid hlattice
  let d : ℂ → ℤ := fun z ↦ divisor (fun w ↦ ℘[L] w - x) (L.periodParallelogram z₀) z
  have hsum_d : roots.sum d = 2 := by simpa [d] using hsum
  have hu_root : u ∈ roots := (hroots u).2 ⟨huP, hu, hux⟩
  obtain ⟨w, hwP, hw, hwshift⟩ :=
    L.exists_nonlattice_mem_periodParallelogram_sub_lattice (z := -u) (z₀ := z₀) (by
      simpa using hu)
  have hwu : w + u ∈ L.lattice := by simpa using hwshift
  have hwx : ℘[L] w = x := by
    -- Negation keeps the same `℘`-fiber, and lattice translation moves it back into the domain.
    let l : L.lattice := ⟨w + u, hwu⟩
    have hw_eq : w = -u + l := by
      change w = -u + (w + u)
      ring
    calc
      ℘[L] w = ℘[L] (-u + l) := by rw [hw_eq]
      _ = ℘[L] (-u) := L.weierstrassP_add_coe (-u) l
      _ = ℘[L] u := L.weierstrassP_neg u
      _ = x := hux
  have hw_root : w ∈ roots := (hroots w).2 ⟨hwP, hw, hwx⟩
  have hw_ge_one : 1 ≤ d w := by
    have hpos :
        0 < d w := by
          rcases (hroots w).1 hw_root with ⟨hwP', hwL, hwx'⟩
          exact (L.divisor_weierstrassP_sub_const_pos_iff_of_not_mem_lattice hwP' hwL).2 hwx'
    omega
  have hu_ge_two : 2 ≤ d u :=
    L.divisor_weierstrassP_sub_const_ge_two_of_deriv_eq_zero huP hu hux hderiv
  by_cases hwu_eq : w = u
  · simpa [two_mul, hwu_eq] using hwu
  · have hw_mem : w ∈ roots.erase u := by simpa [hwu_eq] using hw_root
    have hw_le :
        d w ≤ (roots.erase u).sum d := by
      exact Finset.single_le_sum
        (fun z hz ↦
          by
            rcases (hroots z).1 (Finset.mem_of_mem_erase hz) with ⟨hzP, hzL, hzx⟩
            exact le_of_lt
              ((L.divisor_weierstrassP_sub_const_pos_iff_of_not_mem_lattice hzP hzL).2 hzx))
        hw_mem
    have hsum_le : d u + d w ≤ roots.sum d := by
      rw [← roots.sum_erase_add d hu_root]
      linarith
    have hsum_le_two : d u + d w ≤ 2 := by
      linarith [hsum_d, hsum_le]
    omega

/-- Helper for Proposition 5.2: the single source-faithful analytic input packages surjectivity of
`℘` away from the lattice, the degree-two `±` fiber classification, and the collapse of a branch
fiber to a nontrivial `2`-torsion class. -/
theorem weierstrassP_fiber_mod_lattice (L : PeriodPair) :
    (∀ x : ℂ, ∃ z : {z : ℂ // z ∉ L.lattice}, ℘[L] z = x) ∧
      (∀ {z z' : ℂ}, z ∉ L.lattice → z' ∉ L.lattice → ℘[L] z' = ℘[L] z →
        z' - z ∈ L.lattice ∨ z' + z ∈ L.lattice) ∧
      (∀ {z : ℂ}, z ∉ L.lattice → ℘'[L] z = 0 → 2 * z ∈ L.lattice) := by
  constructor
  · intro x
    obtain ⟨t, ht0, ht1, hgeneric⟩ := L.exists_boundary_generic_periodParallelogram x
    let z₀ := -(t : ℝ) • L.ω₁ - (t / 2 : ℝ) • L.ω₂
    rcases hgeneric with ⟨hzero, havoid, hlattice⟩
    obtain ⟨roots, hroots, hsum⟩ :=
      L.exists_fiber_representatives_sum_divisor_eq_two hzero havoid hlattice
    have hroots_nonempty : roots.Nonempty := by
      by_contra hroots_empty
      rw [Finset.not_nonempty_iff_eq_empty] at hroots_empty
      simpa [hroots_empty] using hsum
    rcases hroots_nonempty with ⟨z, hz⟩
    refine ⟨⟨z, ?_⟩, ?_⟩
    · exact ((hroots z).1 hz).2.1
    · exact ((hroots z).1 hz).2.2
  · constructor
    · intro z z' hz hz' hsame
      let x : ℂ := ℘[L] z
      obtain ⟨t, ht0, ht1, hgeneric⟩ := L.exists_boundary_generic_periodParallelogram x
      let z₀ := -(t : ℝ) • L.ω₁ - (t / 2 : ℝ) • L.ω₂
      rcases hgeneric with ⟨hzero, havoid, hlattice⟩
      obtain ⟨u, huP, huN, huz⟩ :=
        L.exists_nonlattice_mem_periodParallelogram_sub_lattice (z := z) (z₀ := z₀) hz
      obtain ⟨v, hvP, hvN, hvz'⟩ :=
        L.exists_nonlattice_mem_periodParallelogram_sub_lattice (z := z') (z₀ := z₀) hz'
      have hux : ℘[L] u = x := by
        -- Translate the representative `u` back to `z` using periodicity of `℘`.
        let l : L.lattice := ⟨u - z, huz⟩
        have hu_eq : u = z + l := by
          change u = z + (u - z)
          ring
        calc
          ℘[L] u = ℘[L] (z + l) := by rw [hu_eq]
          _ = ℘[L] z := L.weierstrassP_add_coe z l
          _ = x := rfl
      have hvx : ℘[L] v = x := by
        -- The same translation argument moves `v` back to `z'`, then to `z`.
        let l : L.lattice := ⟨v - z', hvz'⟩
        have hv_eq : v = z' + l := by
          change v = z' + (v - z')
          ring
        calc
          ℘[L] v = ℘[L] (z' + l) := by rw [hv_eq]
          _ = ℘[L] z' := L.weierstrassP_add_coe z' l
          _ = ℘[L] z := hsame
          _ = x := rfl
      rcases
          L.eq_or_neg_mod_lattice_of_same_weierstrassP_generic
            hzero havoid hlattice huP hvP huN hvN hux hvx with huv | huv
      · left
        have hz'v : z' - v ∈ L.lattice := by simpa using neg_mem hvz'
        have htotal : (z' - v) + (v - u) + (u - z) ∈ L.lattice := by
          exact add_mem (add_mem hz'v huv) huz
        have hrewrite : (z' - v) + (v - u) + (u - z) = z' - z := by ring
        exact hrewrite ▸ htotal
      · right
        have hzu : z - u ∈ L.lattice := by simpa using neg_mem huz
        have hz'v : z' - v ∈ L.lattice := by simpa using neg_mem hvz'
        have htotal : (z' - v) + (v + u) + (z - u) ∈ L.lattice := by
          exact add_mem (add_mem hz'v huv) hzu
        have hrewrite : (z' - v) + (v + u) + (z - u) = z' + z := by ring
        exact hrewrite ▸ htotal
    · intro z hz hderiv
      let x : ℂ := ℘[L] z
      obtain ⟨t, ht0, ht1, hgeneric⟩ := L.exists_boundary_generic_periodParallelogram x
      let z₀ := -(t : ℝ) • L.ω₁ - (t / 2 : ℝ) • L.ω₂
      rcases hgeneric with ⟨hzero, havoid, hlattice⟩
      obtain ⟨u, huP, huN, huz⟩ :=
        L.exists_nonlattice_mem_periodParallelogram_sub_lattice (z := z) (z₀ := z₀) hz
      have hux : ℘[L] u = x := by
        -- Move the branch point representative back to the original point through a period.
        let l : L.lattice := ⟨u - z, huz⟩
        have hu_eq : u = z + l := by
          change u = z + (u - z)
          ring
        calc
          ℘[L] u = ℘[L] (z + l) := by rw [hu_eq]
          _ = ℘[L] z := L.weierstrassP_add_coe z l
          _ = x := rfl
      have huderiv : ℘'[L] u = 0 := by
        -- The derivative is periodic as well, so the branch condition transports to `u`.
        let l : L.lattice := ⟨u - z, huz⟩
        have hu_eq : u = z + l := by
          change u = z + (u - z)
          ring
        calc
          ℘'[L] u = ℘'[L] (z + l) := by rw [hu_eq]
          _ = ℘'[L] z := L.derivWeierstrassP_add_coe z l
          _ = 0 := hderiv
      have h2u : 2 * u ∈ L.lattice :=
        L.two_mul_mem_lattice_of_deriv_eq_zero_generic
          hzero havoid hlattice huP huN hux huderiv
      have h2shift : 2 * (u - z) ∈ L.lattice := by
        have hzsmul : (2 : ℤ) • (u - z) ∈ L.lattice := zsmul_mem huz 2
        simpa [zsmul_eq_mul, two_mul] using hzsmul
      have htotal : 2 * u - 2 * (u - z) ∈ L.lattice := sub_mem h2u h2shift
      have hrewrite : 2 * u - 2 * (u - z) = 2 * z := by ring
      exact hrewrite ▸ htotal

/-- Proposition 5.2 (1): the cubic equation `4 x^3 - 20 a₂ x - 28 a₄ = 0` attached to the
period lattice has three distinct complex roots. -/
theorem cartan_cubic_has_three_distinct_roots (L : PeriodPair) :
    ∃ e : Fin 3 → ℂ,
      Function.Injective e ∧
      ∀ x : ℂ, 4 * x ^ 3 - 20 * L.cartan_a₂ * x - 28 * L.cartan_a₄ = 0 ↔
        ∃ i : Fin 3, x = e i := by
  refine ⟨L.cartan_half_period_root, ?_, ?_⟩
  · -- The source proof identifies these three values with the three nonzero `2`-torsion classes.
    -- The packaged analytic theorem turns lattice-class distinctions into `℘`-value distinctions.
    rcases L.weierstrassP_fiber_mod_lattice with ⟨_, hfiber, _⟩
    exact L.cartan_half_period_root_injective_of_weierstrassP_fiber hfiber
  · intro x
    -- The verified prefix is that all three half-period values are roots of the cubic.
    have hroot0 :
        4 * (L.cartan_half_period_root 0) ^ 3 - 20 * L.cartan_a₂ * L.cartan_half_period_root 0 -
          28 * L.cartan_a₄ = 0 := by
      simpa using L.cartan_polynomial_eq_zero_at_omega₁_div_two
    have hroot1 :
        4 * (L.cartan_half_period_root 1) ^ 3 - 20 * L.cartan_a₂ * L.cartan_half_period_root 1 -
          28 * L.cartan_a₄ = 0 := by
      simpa using L.cartan_polynomial_eq_zero_at_omega₂_div_two
    have hroot2 :
        4 * (L.cartan_half_period_root 2) ^ 3 - 20 * L.cartan_a₂ * L.cartan_half_period_root 2 -
          28 * L.cartan_a₄ = 0 := by
      simpa using L.cartan_polynomial_eq_zero_at_omega_sum_div_two
    constructor
    · -- Route correction: the hard direction is still root classification, not root construction.
      -- The packaged analytic theorem supplies the required surjectivity and branch collapse.
      intro hx
      rcases L.weierstrassP_fiber_mod_lattice with ⟨hsurj, _, hbranch⟩
      simpa using L.exists_cartan_half_period_root_of_cubic_eq_zero hsurj hbranch hx
    · rintro ⟨i, rfl⟩
      -- Each listed half-period value already satisfies the cubic equation.
      fin_cases i
      · exact hroot0
      · exact hroot1
      · exact hroot2

/-- Proposition 5.2 (2): every affine point on Cartan's cubic is represented by a unique point of
`ℂ \ L.lattice` modulo the period lattice through the map `z ↦ (℘(z), ℘'(z))`. -/
theorem exists_weierstrass_p_representative_mod_lattice (L : PeriodPair) {x y : ℂ}
    (hxy : L.on_cartan_cubic x y) :
    ∃ z : {z : ℂ // z ∉ L.lattice},
      (℘[L] z, ℘'[L] z) = (x, y) ∧
      ∀ z' : {z : ℂ // z ∉ L.lattice},
        (℘[L] z', ℘'[L] z') = (x, y) ↔ (z' : ℂ) - z ∈ L.lattice := by
  -- Route correction: all algebraic bookkeeping is now isolated in
  -- `exists_weierstrass_pair_of_on_cartan_cubic`; only the source-faithful analytic core remains.
  rcases L.weierstrassP_fiber_mod_lattice with ⟨hsurj, hfiber, hbranch⟩
  exact L.exists_weierstrass_pair_of_on_cartan_cubic hsurj hfiber hbranch hxy

end PeriodPair
