import Mathlib
import StacksProject_2024.Chap10.Definition_10_84_1
import StacksProject_2024.Chap10.Definition_10_88_7
import StacksProject_2024.Chap10.Example_10_89_1
import StacksProject_2024.Chap10.Lemma_10_51_3
import StacksProject_2024.Chap10.Theorem_10_93_3
import StacksProject_2024.Chap10.Lemma_10_153_10
import StacksProject_2024.Chap10.Lemma_10_153_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: if `M` were Mittag-Leffler, then the countably generated module `M` would be a
-- direct sum of countably generated submodules in the trivial one-summand way. Theorem `10.93.3`
-- would then imply that `M` is projective, contradicting `hproj`.
/-- Helper for Chap10 Example 10 91 5: any flat countably generated non-projective `R`-module is not
Mittag-Leffler. This is the criterion used in the example to manufacture explicit
counterexamples. -/
@[stacks 059U]
theorem not_mittagLeffler_of_flat_of_countablyGenerated_of_not_projective
    [Flat R M] (hcg : CountablyGenerated R M) (hproj : ¬ Projective R M) :
    ¬ MittagLeffler R M := by
  intro hML
  -- The countable generation hypothesis gives the required one-summand internal direct-sum
  -- decomposition for Theorem 10.93.3.
  have hsum : IsDirectSumOfCountablyGenerated.{u, v, 0} R M := by
    rw [Module.isDirectSumOfCountablyGenerated_iff]
    refine ⟨PUnit.{1}, fun _ ↦ (⊤ : Submodule R M), ?_, ?_, ?_⟩
    · exact iSupIndep_subsingleton _
    · simp
    · intro _
      exact hcg
  -- The projectivity criterion then turns flatness, Mittag-Lefflerness, and this decomposition
  -- into projectivity, contradicting the hypothesis.
  apply hproj
  exact (projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated
    (R := R) (M := M)).2 ⟨inferInstance, hML, hsum⟩

-- Proof sketch: Proposition `10.89.5` identifies the Mittag-Leffler condition with injectivity of
-- all tensor-product-to-product maps, while Example `10.89.1` exhibits a specific family
-- `Q_n = ℤ / nℤ` for which the corresponding map for `ℚ` is not injective.
/-- The `ℤ`-module `ℚ` is not Mittag-Leffler. -/
theorem rat_not_mittagLeffler :
    ¬ MittagLeffler ℤ ℚ := by
  intro hML
  -- Proposition 10.89.5 converts Mittag-Lefflerness into injectivity of every tensor-to-product
  -- map; Example 10.89.1 supplies the failing family `ZMod n`.
  have hinj := (mittagLeffler_iff_tensorProduct_piRight_injective (R := ℤ) (M := ℚ)).mp hML
    ℕ+ (fun n ↦ ZMod n)
  exact rat_tensor_pnat_zmod_product_map_not_injective hinj

end

section

variable (k : Type u) [Field k]

/-- The quotient `k[[x]] / (x^n)` viewed as a `k[[x]]`-module. -/
abbrev powerSeriesQuotientByXPow (n : ℕ+) :=
  PowerSeries k ⧸ Ideal.span ({(PowerSeries.X : PowerSeries k) ^ (n : ℕ)} : Set (PowerSeries k))

/-- The product `∏_{n ≥ 1} k[[x]] / (x^n)` from the power-series example. -/
abbrev powerSeriesQuotientProduct :=
  (n : ℕ+) → powerSeriesQuotientByXPow k n

/-- The `x`-adic ideal of `k[[x]]`. -/
abbrev powerSeriesXIdeal : Ideal (PowerSeries k) :=
  Ideal.span ({(PowerSeries.X : PowerSeries k)} : Set (PowerSeries k))

/-- The direct sum `⨁_{n ≥ 1} k[[x]] / (x^n)` used before taking `x`-adic completion. -/
abbrev powerSeriesQuotientDirectSum :=
  Π₀ n : ℕ+, powerSeriesQuotientByXPow k n

/-- The `x`-adic completion of `⨁_{n ≥ 1} k[[x]] / (x^n)`. -/
abbrev powerSeriesQuotientDirectSumCompletion :=
  AdicCompletion (powerSeriesXIdeal k) (powerSeriesQuotientDirectSum k)

-- Route correction: the previous broad kernel-approximation route hid the concrete invariant.
-- The remaining power-series proofs are now routed through named annihilator exponents in the
-- quotients by powers of `X`.
/-- Helper for Chap10 Example 10 91 5: the submodule `X^l M` of a power-series module. -/
abbrev powerSeriesXPowSubmodule (M : Type v) [AddCommGroup M] [Module (PowerSeries k) M]
    (l : ℕ) : Submodule (PowerSeries k) M :=
  (Ideal.span ({(PowerSeries.X : PowerSeries k) ^ l} : Set (PowerSeries k))) •
    (⊤ : Submodule (PowerSeries k) M)

/-- Helper for Chap10 Example 10 91 5: an element has annihilator exactly `(X^e)` after
quotienting by `X^l`. -/
def HasAnnihilatorExponent (M : Type v) [AddCommGroup M] [Module (PowerSeries k) M]
    (x : M) (l e : ℕ) : Prop :=
  Ideal.torsionOf (PowerSeries k) (M ⧸ powerSeriesXPowSubmodule k M l)
      (Submodule.Quotient.mk x) =
    Ideal.span ({(PowerSeries.X : PowerSeries k) ^ e} : Set (PowerSeries k))

/-- Helper for Chap10 Example 10 91 5: a module has an element whose annihilator exponent is half
of the quotient exponent along powers of two. -/
def HasSparseHalfAnnihilator (M : Type v) [AddCommGroup M] [Module (PowerSeries k) M] :
    Prop :=
  ∃ x : M, ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
    HasAnnihilatorExponent k M x (2 ^ (m + 1)) (2 ^ m)

/-- Helper for Chap10 Example 10 91 5: the sparse product element supported at coordinates
`2^(m+1)` with value `X^(2^m)`. -/
def powerSeriesSparseProductElement : powerSeriesQuotientProduct k :=
  fun n =>
    @dite (powerSeriesQuotientByXPow k n) (∃ m : ℕ, (n : ℕ) = 2 ^ (m + 1))
      (Classical.propDecidable _)
      (fun h ↦ Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (2 ^ Nat.find h)))
      (fun _ ↦ 0)

/-- Helper for Chap10 Example 10 91 5: powers of two used as quotient indices are positive. -/
private lemma twoPowSucc_pos (m : ℕ) : 0 < 2 ^ (m + 1) := by
  -- This packages the positivity proof once so later subtype indices stay proof-free.
  positivity

/-- Helper for Chap10 Example 10 91 5: the positive natural number `2^(m+1)`. -/
private def twoPowSuccPNat (m : ℕ) : ℕ+ :=
  ⟨2 ^ (m + 1), twoPowSucc_pos m⟩

/-- Helper for Chap10 Example 10 91 5: in `k[[X]]/(X^n)`, every larger `X`-power acts
trivially. -/
private lemma powerSeriesQuotientByXPow_xPowSubmodule_eq_bot_of_le (n : ℕ+) {l : ℕ}
    (hnl : (n : ℕ) ≤ l) :
    powerSeriesXPowSubmodule k (powerSeriesQuotientByXPow k n) l = ⊥ := by
  -- Reduce membership in the `X^l`-multiple submodule to a single scalar multiple.
  apply le_antisymm
  · intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr z hz
      rw [Submodule.mem_bot]
      rcases Ideal.mem_span_singleton.mp hr with ⟨c, rfl⟩
      rw [mul_smul]
      -- Since `n ≤ l`, the scalar `X^l` belongs to the ideal `(X^n)` defining the quotient.
      suffices hkill : ∀ w : powerSeriesQuotientByXPow k n,
          ((PowerSeries.X : PowerSeries k) ^ l) • w = 0 by
        exact hkill (c • z)
      intro w
      rcases Ideal.Quotient.mk_surjective w with ⟨p, rfl⟩
      rw [Algebra.smul_def]
      simp only [Ideal.Quotient.algebraMap_eq]
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      refine Ideal.mul_mem_right _ _ ?_
      rw [Ideal.mem_span_singleton]
      refine ⟨(PowerSeries.X : PowerSeries k) ^ (l - (n : ℕ)), ?_⟩
      rw [← pow_add, Nat.add_sub_of_le hnl]
    · intro x y hx hy
      rw [Submodule.mem_bot] at hx hy ⊢
      simp [hx, hy]
  · intro y hy
    rw [Submodule.mem_bot] at hy
    rw [hy]
    exact Submodule.zero_mem _

/-- Helper for Chap10 Example 10 91 5: membership in an `X^l`-multiple submodule of the product
projects to membership in the corresponding coordinate submodule. -/
private lemma powerSeriesProduct_xPowSubmodule_coordinate {l : ℕ} {n : ℕ+}
    {y : powerSeriesQuotientProduct k}
    (hy : y ∈ powerSeriesXPowSubmodule k (powerSeriesQuotientProduct k) l) :
    y n ∈ powerSeriesXPowSubmodule k (powerSeriesQuotientByXPow k n) l := by
  -- The coordinate projection respects scalar multiples and sums in the generated submodule.
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr z hz
    exact Submodule.smul_mem_smul hr trivial
  · intro y z hy hz
    exact Submodule.add_mem _ hy hz

/-- Helper for Chap10 Example 10 91 5: the sparse element has value `X^(2^m)` in the
distinguished coordinate `2^(m+1)`. -/
private lemma powerSeriesSparseProductElement_apply_twoPowSucc (m : ℕ) :
    powerSeriesSparseProductElement k (twoPowSuccPNat m) =
      Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (2 ^ m)) := by
  -- Unfold the `dite`; uniqueness of powers of two identifies the chosen exponent.
  unfold powerSeriesSparseProductElement
  simp only [twoPowSuccPNat]
  split
  · congr 1
    apply congrArg (fun r : ℕ => (PowerSeries.X : PowerSeries k) ^ (2 ^ r))
    rw [Nat.find_eq_iff]
    constructor
    · rfl
    · intro y hylt hy
      have hpow : 2 ^ (y + 1) = 2 ^ (m + 1) := hy.symm
      have htwo_le : 2 ≤ (2 : ℕ) := by
        norm_num
      have hy_eq : y = m := Nat.succ.inj (Nat.pow_right_injective htwo_le hpow)
      omega
  · exfalso
    exact ‹¬∃ m_1, (twoPowSuccPNat m : ℕ) = 2 ^ (m_1 + 1)› ⟨m, rfl⟩

/-- Helper for Chap10 Example 10 91 5: divisibility by `X^(2^(m+1))` after multiplying by
`X^(2^m)` is the same as divisibility by `X^(2^m)`. -/
private lemma powerSeries_X_pow_mul_half_dvd_iff (a : PowerSeries k) (m : ℕ) :
    (PowerSeries.X ^ (2 ^ (m + 1)) ∣ a * PowerSeries.X ^ (2 ^ m)) ↔
      PowerSeries.X ^ (2 ^ m) ∣ a := by
  -- Compare coefficients below the relevant powers of `X`.
  rw [PowerSeries.X_pow_dvd_iff, PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h n hn
    have hlt : n + 2 ^ m < 2 ^ (m + 1) := by
      rw [pow_succ]
      omega
    specialize h (n + 2 ^ m) hlt
    simpa [PowerSeries.coeff_mul_X_pow] using h
  · intro h n hn
    by_cases hnle : 2 ^ m ≤ n
    · have hlt : n - 2 ^ m < 2 ^ m := by
        rw [pow_succ] at hn
        omega
      have hcoeff := h (n - 2 ^ m) hlt
      simpa [PowerSeries.coeff_mul_X_pow', hnle] using hcoeff
    · have hlt : n < 2 ^ m := lt_of_not_ge hnle
      simp [PowerSeries.coeff_mul_X_pow', hlt.not_ge]

/-- Helper for Chap10 Example 10 91 5: the distinguished coordinate has annihilator
`(X^(2^m))` in `k[[X]]/(X^(2^(m+1)))`. -/
private lemma powerSeriesQuotientByXPow_torsionOf_sparseCoordinate {n : ℕ+} {m : ℕ}
    (hn : (n : ℕ) = 2 ^ (m + 1)) :
    Ideal.torsionOf (PowerSeries k) (powerSeriesQuotientByXPow k n)
      (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (2 ^ m))) =
    Ideal.span ({(PowerSeries.X : PowerSeries k) ^ (2 ^ m)} : Set (PowerSeries k)) := by
  -- Rewrite torsion in the cyclic quotient as divisibility in the power-series ring.
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_span_singleton]
  rw [Algebra.smul_def]
  simp only [Ideal.Quotient.algebraMap_eq]
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  rw [Ideal.mem_span_singleton, hn]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (powerSeries_X_pow_mul_half_dvd_iff (k := k) a m)

/-- Helper for Chap10 Example 10 91 5: the annihilator of the sparse product element is bounded
above by the distinguished coordinate annihilator. -/
private lemma powerSeriesSparseProductElement_annihilator_le (m : ℕ) :
    Ideal.torsionOf (PowerSeries k)
      (powerSeriesQuotientProduct k ⧸
        powerSeriesXPowSubmodule k (powerSeriesQuotientProduct k) (2 ^ (m + 1)))
      (Submodule.Quotient.mk (powerSeriesSparseProductElement k)) ≤
    Ideal.span ({(PowerSeries.X : PowerSeries k) ^ (2 ^ m)} : Set (PowerSeries k)) := by
  intro a ha
  -- Project a global annihilator relation to the coordinate `2^(m+1)`.
  rw [Ideal.mem_torsionOf_iff] at ha
  rw [← Submodule.Quotient.mk_smul] at ha
  have hglobal : a • powerSeriesSparseProductElement k ∈
      powerSeriesXPowSubmodule k (powerSeriesQuotientProduct k) (2 ^ (m + 1)) :=
    (Submodule.Quotient.mk_eq_zero _).mp ha
  let n : ℕ+ := twoPowSuccPNat m
  have hcoord_mem : (a • powerSeriesSparseProductElement k) n ∈
      powerSeriesXPowSubmodule k (powerSeriesQuotientByXPow k n) (2 ^ (m + 1)) :=
    powerSeriesProduct_xPowSubmodule_coordinate (k := k) hglobal
  have hnle : (n : ℕ) ≤ 2 ^ (m + 1) := by
    rfl
  have hcoord_zero : (a • powerSeriesSparseProductElement k) n = 0 := by
    have hbot :
        powerSeriesXPowSubmodule k (powerSeriesQuotientByXPow k n) (2 ^ (m + 1)) = ⊥ :=
      powerSeriesQuotientByXPow_xPowSubmodule_eq_bot_of_le (k := k) n hnle
    rw [hbot, Submodule.mem_bot] at hcoord_mem
    exact hcoord_mem
  -- The coordinate computation converts the global relation into the cyclic quotient torsion
  -- calculation above.
  have hcoord_tors : a ∈ Ideal.torsionOf (PowerSeries k) (powerSeriesQuotientByXPow k n)
      (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (2 ^ m))) := by
    have hcoord_zero' : a • powerSeriesSparseProductElement k n = 0 := by
      change (a • powerSeriesSparseProductElement k) n = 0
      exact hcoord_zero
    rw [Ideal.mem_torsionOf_iff]
    rw [← powerSeriesSparseProductElement_apply_twoPowSucc (k := k) m]
    exact hcoord_zero'
  have hn_eq : (n : ℕ) = 2 ^ (m + 1) := by
    rfl
  have htors := powerSeriesQuotientByXPow_torsionOf_sparseCoordinate
    (k := k) (n := n) (m := m) hn_eq
  rwa [htors] at hcoord_tors

/-- Helper for Chap10 Example 10 91 5: `X^(2^m)` annihilates the sparse product element modulo
`X^(2^(m+1))`. -/
private lemma powerSeriesSparseProductElement_generator_mem_annihilator (m : ℕ) :
    ((PowerSeries.X : PowerSeries k) ^ (2 ^ m)) ∈
      Ideal.torsionOf (PowerSeries k)
        (powerSeriesQuotientProduct k ⧸
          powerSeriesXPowSubmodule k (powerSeriesQuotientProduct k) (2 ^ (m + 1)))
        (Submodule.Quotient.mk (powerSeriesSparseProductElement k)) := by
  rw [Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  -- Build the coordinatewise divisor witnessing that `X^(2^m) • ξ` is an `X^(2^(m+1))`-multiple.
  let z : powerSeriesQuotientProduct k := fun n =>
    @dite (powerSeriesQuotientByXPow k n)
      (∃ r : ℕ, (n : ℕ) = 2 ^ (r + 1) ∧ m ≤ r)
      (Classical.propDecidable _)
      (fun h ↦ Ideal.Quotient.mk _
        ((PowerSeries.X : PowerSeries k) ^ (2 ^ Nat.find h - 2 ^ m)))
      (fun _ ↦ 0)
  have hz : ((PowerSeries.X : PowerSeries k) ^ (2 ^ m)) • powerSeriesSparseProductElement k =
      ((PowerSeries.X : PowerSeries k) ^ (2 ^ (m + 1))) • z := by
    ext n
    unfold powerSeriesSparseProductElement z
    by_cases hs : ∃ r : ℕ, (n : ℕ) = 2 ^ (r + 1)
    · simp only [Pi.smul_apply, dif_pos hs]
      let r := Nat.find hs
      have hr : (n : ℕ) = 2 ^ (r + 1) := Nat.find_spec hs
      by_cases hmr : m ≤ r
      · have hge : ∃ r : ℕ, (n : ℕ) = 2 ^ (r + 1) ∧ m ≤ r := ⟨r, hr, hmr⟩
        simp only [dif_pos hge]
        have hfind : Nat.find hge = r := by
          rw [Nat.find_eq_iff]
          constructor
          · exact ⟨hr, hmr⟩
          · intro y hylt hy
            have hpow : 2 ^ (y + 1) = 2 ^ (r + 1) := by
              rw [← hy.1, hr]
            have htwo_le : 2 ≤ (2 : ℕ) := by
              norm_num
            have hy_eq : y = r := Nat.succ.inj (Nat.pow_right_injective htwo_le hpow)
            omega
        have hsfind : Nat.find hs = r := rfl
        have hpoweq : 2 ^ (m + 1) + (2 ^ r - 2 ^ m) = 2 ^ m + 2 ^ r := by
          have htwo_pos : 0 < (2 : ℕ) := by
            norm_num
          have hpow_le : 2 ^ m ≤ 2 ^ r := Nat.pow_le_pow_right htwo_pos hmr
          rw [pow_succ]
          omega
        rw [hsfind, hfind, Algebra.smul_def, Algebra.smul_def]
        simp only [Ideal.Quotient.algebraMap_eq]
        rw [← map_mul, ← map_mul]
        rw [← pow_add (PowerSeries.X : PowerSeries k) (2 ^ (m + 1)) (2 ^ r - 2 ^ m),
          hpoweq]
        rw [pow_add]
      · have hge_false : ¬ ∃ r : ℕ, (n : ℕ) = 2 ^ (r + 1) ∧ m ≤ r := by
          rintro ⟨s, hs_eq, hms⟩
          have hsr : s = r := by
            have htwo : 1 < (2 : ℕ) := by
              norm_num
            have hpow : 2 ^ (s + 1) = 2 ^ (r + 1) := by
              rw [← hs_eq, hr]
            have htwo_le : 2 ≤ (2 : ℕ) := by
              norm_num
            exact Nat.succ.inj (Nat.pow_right_injective htwo_le hpow)
          exact hmr (hsr ▸ hms)
        simp only [dif_neg hge_false, smul_zero]
        have hsfind : Nat.find hs = r := rfl
        rw [hsfind, Algebra.smul_def]
        simp only [Ideal.Quotient.algebraMap_eq]
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        rw [Ideal.mem_span_singleton]
        refine ⟨(PowerSeries.X : PowerSeries k) ^ (2 ^ m + 2 ^ r - (n : ℕ)), ?_⟩
        have hle : (n : ℕ) ≤ 2 ^ m + 2 ^ r := by
          have hlt : r < m := Nat.lt_of_not_ge hmr
          have htwo_pos : 0 < (2 : ℕ) := by
            norm_num
          have hpow_le : 2 ^ r ≤ 2 ^ m := Nat.pow_le_pow_right htwo_pos hlt.le
          rw [hr, pow_succ]
          omega
        calc
          (PowerSeries.X : PowerSeries k) ^ 2 ^ m * (PowerSeries.X : PowerSeries k) ^ 2 ^ r =
              (PowerSeries.X : PowerSeries k) ^ (2 ^ m + 2 ^ r) := by
            rw [pow_add]
          _ =
              (PowerSeries.X : PowerSeries k) ^ ((n : ℕ) + (2 ^ m + 2 ^ r - (n : ℕ))) := by
            rw [Nat.add_sub_of_le hle]
          _ = (PowerSeries.X : PowerSeries k) ^ (n : ℕ) *
              (PowerSeries.X : PowerSeries k) ^ (2 ^ m + 2 ^ r - (n : ℕ)) := by
            rw [pow_add]
    · have hge_false : ¬ ∃ r : ℕ, (n : ℕ) = 2 ^ (r + 1) ∧ m ≤ r := by
        rintro ⟨r, hr, _⟩
        exact hs ⟨r, hr⟩
      simp only [Pi.smul_apply, dif_neg hs, dif_neg hge_false, smul_zero]
  -- The explicit divisor turns the relation into membership in the generated submodule.
  rw [hz]
  exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) trivial

/-- Helper for Chap10 Example 10 91 5: the sparse product element has the expected annihilator
exponent at every power-of-two stage. -/
private lemma powerSeriesSparseProductElement_annihilatorExponent (m : ℕ) :
    HasAnnihilatorExponent k (powerSeriesQuotientProduct k)
      (powerSeriesSparseProductElement k) (2 ^ (m + 1)) (2 ^ m) := by
  -- Combine the distinguished-coordinate upper bound with the explicit lower annihilator
  -- generator.
  unfold HasAnnihilatorExponent
  apply le_antisymm
  · exact powerSeriesSparseProductElement_annihilator_le (k := k) m
  · refine Ideal.span_le.mpr ?_
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact powerSeriesSparseProductElement_generator_mem_annihilator (k := k) m

/-- Helper for Chap10 Example 10 91 5: the sparse product element has half-exponent
annihilators along the powers-of-two quotients. -/
lemma powerSeriesSparseProductElement_hasSparseHalfAnnihilator :
    HasSparseHalfAnnihilator k (powerSeriesQuotientProduct k) := by
  -- The product calculation above supplies the exact annihilator at every stage, so there is no
  -- initial threshold to discard.
  exact ⟨powerSeriesSparseProductElement k, 0, fun m _ ↦
    powerSeriesSparseProductElement_annihilatorExponent (k := k) m⟩

/-- Helper for Chap10 Example 10 91 5: membership in `(X^e)` forces lower coefficients to
vanish. -/
private lemma powerSeries_coeff_eq_zero_of_mem_span_X_pow {a : PowerSeries k} {e n : ℕ}
    (ha : a ∈ Ideal.span ({(PowerSeries.X : PowerSeries k) ^ e} : Set (PowerSeries k)))
    (hn : n < e) : PowerSeries.coeff n a = 0 := by
  rw [Ideal.mem_span_singleton] at ha
  exact (PowerSeries.X_pow_dvd_iff.mp ha) n hn

/-- Helper for Chap10 Example 10 91 5: a sparse half-annihilator element has zero annihilator
before quotienting. -/
private lemma sparseHalfAnnihilator_torsion_eq_bot
    {M : Type u} [AddCommGroup M] [Module (PowerSeries k) M]
    (x : M) (m0 : ℕ)
    (hx : ∀ m : ℕ, m0 ≤ m →
      HasAnnihilatorExponent k M x (2 ^ (m + 1)) (2 ^ m)) :
    Ideal.torsionOf (PowerSeries k) M x = ⊥ := by
  ext a
  constructor
  · intro ha
    rw [Ideal.mem_bot]
    ext n
    let m := n + m0 + 1
    have hm0 : m0 ≤ m := by omega
    have hnlt : n < 2 ^ m := by
      have hlt : n < 2 ^ n := Nat.lt_two_pow_self
      have hle : 2 ^ n ≤ 2 ^ m :=
        Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega)
      omega
    have hquot : a ∈ Ideal.torsionOf (PowerSeries k)
        (M ⧸ powerSeriesXPowSubmodule k M (2 ^ (m + 1)))
        (Submodule.Quotient.mk x) := by
      rw [Ideal.mem_torsionOf_iff] at ha ⊢
      simpa using congrArg
        (Submodule.Quotient.mk (p := powerSeriesXPowSubmodule k M (2 ^ (m + 1)))) ha
    have hx_m := hx m hm0
    unfold HasAnnihilatorExponent at hx_m
    have hspan : a ∈ Ideal.span ({(PowerSeries.X : PowerSeries k) ^ (2 ^ m)} :
        Set (PowerSeries k)) := by
      rwa [hx_m] at hquot
    exact powerSeries_coeff_eq_zero_of_mem_span_X_pow (k := k) hspan hnlt
  · intro ha
    rw [Ideal.mem_bot] at ha
    rw [ha]
    exact Ideal.zero_mem _

/-- Helper for Chap10 Example 10 91 5: a Mittag-Leffler module satisfies the finite-presentation
tensor-kernel comparison criterion. -/
private lemma mittagLeffler_kernel_condition
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (hML : MittagLeffler R M) :
    ∀ (P : ModuleCat.{u} R) [Module.FinitePresentation R P] (f : P →ₗ[R] M),
      ∃ (Q : ModuleCat.{u} R) (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q),
        ∀ N : ModuleCat.{u} R,
          LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  let pres : MittagLefflerPresentation R M := Classical.choice hML.exists_presentation
  letI : Preorder pres.index := pres.indexPreorder
  letI : Nonempty pres.index := pres.indexNonempty
  letI : IsDirectedOrder pres.index := pres.indexDirected
  let c : colimit pres.diagram ≅ ModuleCat.of R M := Classical.choice pres.colimitIso
  have hfp : ∀ i, Module.FinitePresentation R (pres.diagram.obj i) :=
    pres.presentation_isMittagLeffler.1
  have hhom : ∀ N : ModuleCat.{u} R,
      (colimitPresentationHomInverseSystem pres.diagram N).IsMittagLeffler :=
    pres.presentation_isMittagLeffler.2
  have htfae := directed_colimit_presentation_mittag_leffler_tfae
    (R := R) (I := pres.index) (M := M) pres.diagram hfp c
  exact (htfae.out 3 0 rfl rfl).mp hhom

/-- Helper for Chap10 Example 10 91 5: kernel equality after tensoring with a quotient of the
base ring identifies the corresponding annihilator ideals in the quotient modules. -/
private lemma torsion_eq_of_rTensor_kernel_eq
    {R : Type u} [CommRing R]
    {M Q : Type u} [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    (x : M) (g : R →ₗ[R] Q) (I : Ideal R)
    (hker : LinearMap.ker ((LinearMap.toSpanSingleton R M x).rTensor (R ⧸ I)) =
      LinearMap.ker (g.rTensor (R ⧸ I))) :
    Ideal.torsionOf R (M ⧸ I • (⊤ : Submodule R M)) (Submodule.Quotient.mk x) =
      Ideal.torsionOf R (Q ⧸ I • (⊤ : Submodule R Q)) (Submodule.Quotient.mk (g 1)) := by
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  let t : R ⊗[R] (R ⧸ I) := (1 : R) ⊗ₜ[R] (Ideal.Quotient.mk I a)
  have ht_left : ((LinearMap.toSpanSingleton R M x).rTensor (R ⧸ I)) t = 0 ↔
      a • Submodule.Quotient.mk (p := I • (⊤ : Submodule R M)) x = 0 := by
    constructor
    · intro ht
      have hq : TensorProduct.tensorQuotEquivQuotSMul (R := R) M I
          (((LinearMap.toSpanSingleton R M x).rTensor (R ⧸ I)) t) = 0 := by
        simp [ht]
      simpa [t, LinearMap.toSpanSingleton, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk,
        Submodule.Quotient.mk_smul] using hq
    · intro ht
      apply (TensorProduct.tensorQuotEquivQuotSMul (R := R) M I).injective
      simpa [t, LinearMap.toSpanSingleton, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk,
        Submodule.Quotient.mk_smul] using ht
  have ht_right : (g.rTensor (R ⧸ I)) t = 0 ↔
      a • Submodule.Quotient.mk (p := I • (⊤ : Submodule R Q)) (g 1) = 0 := by
    constructor
    · intro ht
      have hq : TensorProduct.tensorQuotEquivQuotSMul (R := R) Q I
          ((g.rTensor (R ⧸ I)) t) = 0 := by
        simp [ht]
      simpa [t, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk,
        Submodule.Quotient.mk_smul] using hq
    · intro ht
      apply (TensorProduct.tensorQuotEquivQuotSMul (R := R) Q I).injective
      simpa [t, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk,
        Submodule.Quotient.mk_smul] using ht
  have hmem : t ∈ LinearMap.ker ((LinearMap.toSpanSingleton R M x).rTensor (R ⧸ I)) ↔
      t ∈ LinearMap.ker (g.rTensor (R ⧸ I)) := by
    rw [hker]
  simpa [LinearMap.mem_ker, ht_left, ht_right] using hmem

/-- Helper for Chap10 Example 10 91 5: the kernel of a map out of the rank-one free module is
the annihilator of the image of `1`. -/
private lemma linearMap_ker_eq_torsion_one
    {R : Type u} [CommRing R] {Q : Type u} [AddCommGroup Q] [Module R Q] (g : R →ₗ[R] Q) :
    LinearMap.ker g = Ideal.torsionOf R Q (g 1) := by
  ext a
  rw [LinearMap.mem_ker, Ideal.mem_torsionOf_iff]
  have hg : g a = a • g 1 := by
    simpa using g.map_smul a (1 : R)
  rw [hg]

/-- Helper for Chap10 Example 10 91 5: tensoring the kernel comparison with the base ring recovers
the original kernels. -/
private lemma ker_eq_of_rTensor_self_kernel_eq
    {R : Type u} [CommRing R]
    {M Q : Type u} [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    {f : R →ₗ[R] M} {g : R →ₗ[R] Q}
    (hker : LinearMap.ker (f.rTensor R) = LinearMap.ker (g.rTensor R)) :
    LinearMap.ker f = LinearMap.ker g := by
  ext a
  constructor
  · intro ha
    have hfa : f a = 0 := by
      simpa [LinearMap.mem_ker] using ha
    have ht : (a ⊗ₜ[R] (1 : R)) ∈ LinearMap.ker (f.rTensor R) := by
      simp [LinearMap.mem_ker, hfa]
    have ht' : (a ⊗ₜ[R] (1 : R)) ∈ LinearMap.ker (g.rTensor R) := by
      rwa [hker] at ht
    have hzero := congrArg (TensorProduct.rid R Q) (by simpa [LinearMap.mem_ker] using ht')
    simpa [LinearMap.mem_ker] using hzero
  · intro ha
    have hga : g a = 0 := by
      simpa [LinearMap.mem_ker] using ha
    have ht : (a ⊗ₜ[R] (1 : R)) ∈ LinearMap.ker (g.rTensor R) := by
      simp [LinearMap.mem_ker, hga]
    have ht' : (a ⊗ₜ[R] (1 : R)) ∈ LinearMap.ker (f.rTensor R) := by
      rwa [← hker] at ht
    have hzero := congrArg (TensorProduct.rid R M) (by simpa [LinearMap.mem_ker] using ht')
    simpa [LinearMap.mem_ker] using hzero

/-- Helper for Chap10 Example 10 91 5: powers of the `X`-adic ideal act as the named
`X`-power submodules. -/
private lemma powerSeriesXIdeal_pow_smul_top (M : Type u)
    [AddCommGroup M] [Module (PowerSeries k) M] (l : ℕ) :
    (powerSeriesXIdeal k) ^ l • (⊤ : Submodule (PowerSeries k) M) =
      powerSeriesXPowSubmodule k M l := by
  simp [powerSeriesXIdeal, powerSeriesXPowSubmodule, Ideal.span_singleton_pow]

/-- Helper for Chap10 Example 10 91 5: the finite truncations of the sparse element in the
direct sum. -/
private def powerSeriesSparseDirectSumTrunc : ℕ → powerSeriesQuotientDirectSum k :=
  fun N =>
    Finset.sum (Finset.range N) fun r ↦
      DFinsupp.single (twoPowSuccPNat r)
        (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (2 ^ r)))

/-- Helper for Chap10 Example 10 91 5: a single direct-sum coordinate with a sufficiently high
power of `X` lies in the named `X`-power submodule. -/
private lemma powerSeriesSparseDirectSum_single_X_pow_mem (r L q : ℕ) (hLq : L ≤ q) :
    DFinsupp.single (twoPowSuccPNat r)
      (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ q)) ∈
      powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSum k) L := by
  have hfactor :
        (PowerSeries.X : PowerSeries k) ^ q =
        (PowerSeries.X : PowerSeries k) ^ L * (PowerSeries.X : PowerSeries k) ^ (q - L) := by
    rw [← pow_add, Nat.add_sub_of_le hLq]
  have hterm :
      DFinsupp.single (β := fun n : ℕ+ ↦ powerSeriesQuotientByXPow k n) (twoPowSuccPNat r)
        (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ q)) =
        ((PowerSeries.X : PowerSeries k) ^ L) •
          DFinsupp.single (β := fun n : ℕ+ ↦ powerSeriesQuotientByXPow k n) (twoPowSuccPNat r)
            ((Ideal.Quotient.mk _
              ((PowerSeries.X : PowerSeries k) ^ (q - L))) :
              powerSeriesQuotientByXPow k (twoPowSuccPNat r)) := by
    ext n
    by_cases hn : n = twoPowSuccPNat r
    · subst n
      rw [DFinsupp.single_eq_same, DFinsupp.smul_apply, DFinsupp.single_eq_same]
      rw [hfactor, Algebra.smul_def]
      simp only [Ideal.Quotient.algebraMap_eq]
      rw [map_mul]
    · rw [DFinsupp.single_eq_of_ne hn, DFinsupp.smul_apply, DFinsupp.single_eq_of_ne hn]
      simp
  rw [hterm]
  unfold powerSeriesXPowSubmodule
  exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) Submodule.mem_top

/-- Helper for Chap10 Example 10 91 5: the sparse direct-sum generator at coordinate
`2^(r+1)` lies in `X^N` whenever `N ≤ 2^r`. -/
private lemma powerSeriesSparseDirectSum_single_mem (r N : ℕ) (hN : N ≤ 2 ^ r) :
    DFinsupp.single (twoPowSuccPNat r)
      (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (2 ^ r))) ∈
      powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSum k) N :=
  powerSeriesSparseDirectSum_single_X_pow_mem (k := k) r N (2 ^ r) hN

/-- Helper for Chap10 Example 10 91 5: consecutive sparse direct-sum truncations agree modulo
the corresponding `X`-power submodule. -/
private lemma powerSeriesSparseDirectSumTrunc_smodEq_succ (N : ℕ) :
    powerSeriesSparseDirectSumTrunc k N ≡ powerSeriesSparseDirectSumTrunc k (N + 1)
      [SMOD ((powerSeriesXIdeal k) ^ N •
        (⊤ : Submodule (PowerSeries k) (powerSeriesQuotientDirectSum k)))] := by
  have hlast := powerSeriesSparseDirectSum_single_mem (k := k) N N
    (Nat.lt_two_pow_self (n := N)).le
  have hdiff :
      powerSeriesSparseDirectSumTrunc k N - powerSeriesSparseDirectSumTrunc k (N + 1) =
        -DFinsupp.single (twoPowSuccPNat N)
          (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (2 ^ N))) := by
    dsimp [powerSeriesSparseDirectSumTrunc]
    rw [Finset.sum_range_succ]
    abel
  rw [SModEq.sub_mem]
  rw [hdiff]
  rw [powerSeriesXIdeal_pow_smul_top]
  exact Submodule.neg_mem _ hlast

/-- Helper for Chap10 Example 10 91 5: the sparse truncations form an `X`-adic Cauchy sequence. -/
private def powerSeriesSparseDirectSumCauchySeq :
    AdicCompletion.AdicCauchySequence (powerSeriesXIdeal k)
      (powerSeriesQuotientDirectSum k) :=
  AdicCompletion.AdicCauchySequence.mk (powerSeriesXIdeal k)
    (powerSeriesQuotientDirectSum k)
    (powerSeriesSparseDirectSumTrunc k)
    (powerSeriesSparseDirectSumTrunc_smodEq_succ k)

/-- Helper for Chap10 Example 10 91 5: the completion element represented by the sparse
direct-sum truncations. -/
private def powerSeriesSparseCompletionElement :
    powerSeriesQuotientDirectSumCompletion k :=
  AdicCompletion.mk (powerSeriesXIdeal k) (powerSeriesQuotientDirectSum k)
    (powerSeriesSparseDirectSumCauchySeq k)

/-- Helper for Chap10 Example 10 91 5: the `X`-adic ideal of `k[[X]]` is finitely generated. -/
private lemma powerSeriesXIdeal_fg : (powerSeriesXIdeal k).FG := by
  simpa [powerSeriesXIdeal] using
    (Submodule.fg_span_singleton (R := PowerSeries k)
      (x := (PowerSeries.X : PowerSeries k)))

/-- Helper for Chap10 Example 10 91 5: quotienting the completion by `X^L` is the same as
taking the kernel quotient of the `L`th evaluation map. -/
private lemma powerSeriesCompletion_xPowSubmodule_eq_ker_eval (L : ℕ) :
    powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSumCompletion k) L =
      (AdicCompletion.eval (powerSeriesXIdeal k) (powerSeriesQuotientDirectSum k) L).ker := by
  rw [← powerSeriesXIdeal_pow_smul_top]
  exact AdicCompletion.pow_smul_top_eq_ker_eval (I := powerSeriesXIdeal k)
    (M := powerSeriesQuotientDirectSum k) (n := L) (powerSeriesXIdeal_fg k)

/-- Helper for Chap10 Example 10 91 5: the `L`th quotient of the completion is canonically the
`L`th quotient of the original direct sum. -/
private def powerSeriesCompletionQuotientEquiv (L : ℕ) :
    (powerSeriesQuotientDirectSumCompletion k ⧸
      powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSumCompletion k) L) ≃ₗ[PowerSeries k]
    (powerSeriesQuotientDirectSum k ⧸
      powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSum k) L) :=
  (Submodule.quotEquivOfEq _ _ (powerSeriesCompletion_xPowSubmodule_eq_ker_eval k L)).trans
    (((AdicCompletion.eval (powerSeriesXIdeal k) (powerSeriesQuotientDirectSum k) L).quotKerEquivOfSurjective
      (AdicCompletion.eval_surjective (powerSeriesXIdeal k) (powerSeriesQuotientDirectSum k) L)).trans
        (Submodule.quotEquivOfEq _ _ (powerSeriesXIdeal_pow_smul_top (k := k)
          (M := powerSeriesQuotientDirectSum k) L)))

/-- Helper for Chap10 Example 10 91 5: the sparse completion element evaluates to its `L`th
finite truncation in the `L`th quotient. -/
private lemma powerSeriesCompletionQuotientEquiv_apply (L : ℕ) :
    powerSeriesCompletionQuotientEquiv k L
      (Submodule.Quotient.mk (powerSeriesSparseCompletionElement k)) =
      Submodule.Quotient.mk
        (p := powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSum k) L)
        (powerSeriesSparseDirectSumTrunc k L) := by
  simp [powerSeriesCompletionQuotientEquiv, powerSeriesSparseCompletionElement,
    powerSeriesSparseDirectSumCauchySeq]

/-- Helper for Chap10 Example 10 91 5: a sparse direct-sum truncation has the expected value in
coordinate `2^(m+1)` once that coordinate has appeared. -/
private lemma powerSeriesSparseDirectSumTrunc_apply_twoPowSucc {N m : ℕ} (hmN : m < N) :
    powerSeriesSparseDirectSumTrunc k N (twoPowSuccPNat m) =
      Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (2 ^ m)) := by
  unfold powerSeriesSparseDirectSumTrunc
  rw [DFinsupp.finset_sum_apply]
  rw [Finset.sum_eq_single m]
  · simp
  · intro r hr hrm
    rw [DFinsupp.single_eq_of_ne]
    intro hnm
    have hpow : 2 ^ (m + 1) = 2 ^ (r + 1) := congrArg Subtype.val hnm
    have htwo_le : 2 ≤ (2 : ℕ) := by
      norm_num
    exact hrm (Nat.succ.inj (Nat.pow_right_injective htwo_le hpow)).symm
  · intro hmnot
    exact False.elim (hmnot (Finset.mem_range.mpr hmN))

/-- Helper for Chap10 Example 10 91 5: membership in an `X^l`-multiple submodule of the direct
sum projects to membership in the corresponding coordinate submodule. -/
private lemma powerSeriesDirectSum_xPowSubmodule_coordinate {l : ℕ} {n : ℕ+}
    {y : powerSeriesQuotientDirectSum k}
    (hy : y ∈ powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSum k) l) :
    y n ∈ powerSeriesXPowSubmodule k (powerSeriesQuotientByXPow k n) l := by
  -- Coordinate projection preserves scalar multiples and finite sums in the generated submodule.
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr z hz
    exact Submodule.smul_mem_smul hr trivial
  · intro y z hy hz
    exact Submodule.add_mem _ hy hz

/-- Helper for Chap10 Example 10 91 5: after multiplying by the half exponent, one sparse
direct-sum coordinate lies in the larger `X`-power submodule. -/
private lemma powerSeriesSparseDirectSum_scaled_single_mem (m r : ℕ) :
    ((PowerSeries.X : PowerSeries k) ^ (2 ^ m)) •
      DFinsupp.single (twoPowSuccPNat r)
        (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (2 ^ r))) ∈
      powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSum k) (2 ^ (m + 1)) := by
  by_cases hmr : m ≤ r
  · have hLq : 2 ^ (m + 1) ≤ 2 ^ m + 2 ^ r := by
      rw [pow_succ]
      have hpow_le : 2 ^ m ≤ 2 ^ r :=
        Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hmr
      omega
    have hmem := powerSeriesSparseDirectSum_single_X_pow_mem (k := k) r (2 ^ (m + 1))
      (2 ^ m + 2 ^ r) hLq
    have hterm :
        ((PowerSeries.X : PowerSeries k) ^ (2 ^ m)) •
          DFinsupp.single (β := fun n : ℕ+ ↦ powerSeriesQuotientByXPow k n) (twoPowSuccPNat r)
            ((Ideal.Quotient.mk _
              ((PowerSeries.X : PowerSeries k) ^ (2 ^ r))) :
              powerSeriesQuotientByXPow k (twoPowSuccPNat r)) =
          DFinsupp.single (β := fun n : ℕ+ ↦ powerSeriesQuotientByXPow k n) (twoPowSuccPNat r)
            ((Ideal.Quotient.mk _
              ((PowerSeries.X : PowerSeries k) ^ (2 ^ m + 2 ^ r))) :
              powerSeriesQuotientByXPow k (twoPowSuccPNat r)) := by
      ext n
      by_cases hn : n = twoPowSuccPNat r
      · subst n
        rw [DFinsupp.smul_apply, DFinsupp.single_eq_same, DFinsupp.single_eq_same]
        rw [Algebra.smul_def]
        simp only [Ideal.Quotient.algebraMap_eq]
        rw [← map_mul, ← pow_add]
      · rw [DFinsupp.smul_apply, DFinsupp.single_eq_of_ne hn, DFinsupp.single_eq_of_ne hn]
        simp
    rwa [hterm]
  · have hrlt : r < m := Nat.lt_of_not_ge hmr
    have hzero :
        ((PowerSeries.X : PowerSeries k) ^ (2 ^ m)) •
          Ideal.Quotient.mk
            (Ideal.span ({(PowerSeries.X : PowerSeries k) ^ (twoPowSuccPNat r : ℕ)} :
              Set (PowerSeries k)))
            ((PowerSeries.X : PowerSeries k) ^ (2 ^ r)) = 0 := by
      rw [Algebra.smul_def]
      simp only [Ideal.Quotient.algebraMap_eq]
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      refine ⟨(PowerSeries.X : PowerSeries k) ^
        (2 ^ m + 2 ^ r - (twoPowSuccPNat r : ℕ)), ?_⟩
      have hle : (twoPowSuccPNat r : ℕ) ≤ 2 ^ m + 2 ^ r := by
        have hpow_le : 2 ^ (r + 1) ≤ 2 ^ m :=
          Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hrlt
        simpa [twoPowSuccPNat] using le_add_right hpow_le
      calc
        (PowerSeries.X : PowerSeries k) ^ 2 ^ m * (PowerSeries.X : PowerSeries k) ^ 2 ^ r =
            (PowerSeries.X : PowerSeries k) ^ (2 ^ m + 2 ^ r) := by
          rw [pow_add]
        _ = (PowerSeries.X : PowerSeries k) ^
            ((twoPowSuccPNat r : ℕ) + (2 ^ m + 2 ^ r - (twoPowSuccPNat r : ℕ))) := by
          rw [Nat.add_sub_of_le hle]
        _ = (PowerSeries.X : PowerSeries k) ^ (twoPowSuccPNat r : ℕ) *
            (PowerSeries.X : PowerSeries k) ^
              (2 ^ m + 2 ^ r - (twoPowSuccPNat r : ℕ)) := by
          rw [pow_add]
    have hterm :
        ((PowerSeries.X : PowerSeries k) ^ (2 ^ m)) •
          DFinsupp.single (β := fun n : ℕ+ ↦ powerSeriesQuotientByXPow k n) (twoPowSuccPNat r)
            ((Ideal.Quotient.mk _
              ((PowerSeries.X : PowerSeries k) ^ (2 ^ r))) :
              powerSeriesQuotientByXPow k (twoPowSuccPNat r)) = 0 := by
      ext n
      by_cases hn : n = twoPowSuccPNat r
      · subst n
        rw [DFinsupp.smul_apply, DFinsupp.single_eq_same, hzero]
        rfl
      · rw [DFinsupp.smul_apply, DFinsupp.single_eq_of_ne hn]
        simp
    rw [hterm]
    exact Submodule.zero_mem _

/-- Helper for Chap10 Example 10 91 5: a finite sum of scaled sparse direct-sum coordinates lies
in the larger `X`-power submodule. -/
private lemma powerSeriesSparseDirectSum_scaled_sum_mem (m : ℕ) (s : Finset ℕ) :
    ((PowerSeries.X : PowerSeries k) ^ (2 ^ m)) •
      Finset.sum s (fun r ↦
        DFinsupp.single (twoPowSuccPNat r)
          (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (2 ^ r)))) ∈
      powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSum k) (2 ^ (m + 1)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro r s hrs ih
    rw [Finset.sum_insert hrs, smul_add]
    exact Submodule.add_mem _
      (powerSeriesSparseDirectSum_scaled_single_mem (k := k) m r) ih

/-- Helper for Chap10 Example 10 91 5: the annihilator of the sparse direct-sum truncation is
bounded by the distinguished coordinate annihilator. -/
private lemma powerSeriesSparseDirectSumTrunc_annihilator_le (m : ℕ) :
    Ideal.torsionOf (PowerSeries k)
      (powerSeriesQuotientDirectSum k ⧸
        powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSum k) (2 ^ (m + 1)))
      (Submodule.Quotient.mk (powerSeriesSparseDirectSumTrunc k (2 ^ (m + 1)))) ≤
    Ideal.span ({(PowerSeries.X : PowerSeries k) ^ (2 ^ m)} : Set (PowerSeries k)) := by
  intro a ha
  -- Project a global annihilator relation to the coordinate `2^(m+1)`.
  rw [Ideal.mem_torsionOf_iff] at ha
  rw [← Submodule.Quotient.mk_smul] at ha
  have hglobal : a • powerSeriesSparseDirectSumTrunc k (2 ^ (m + 1)) ∈
      powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSum k) (2 ^ (m + 1)) :=
    (Submodule.Quotient.mk_eq_zero _).mp ha
  let n : ℕ+ := twoPowSuccPNat m
  have hcoord_mem : (a • powerSeriesSparseDirectSumTrunc k (2 ^ (m + 1))) n ∈
      powerSeriesXPowSubmodule k (powerSeriesQuotientByXPow k n) (2 ^ (m + 1)) :=
    powerSeriesDirectSum_xPowSubmodule_coordinate (k := k) hglobal
  have hnle : (n : ℕ) ≤ 2 ^ (m + 1) := by
    rfl
  have hcoord_zero : (a • powerSeriesSparseDirectSumTrunc k (2 ^ (m + 1))) n = 0 := by
    have hbot :
        powerSeriesXPowSubmodule k (powerSeriesQuotientByXPow k n) (2 ^ (m + 1)) = ⊥ :=
      powerSeriesQuotientByXPow_xPowSubmodule_eq_bot_of_le (k := k) n hnle
    rw [hbot, Submodule.mem_bot] at hcoord_mem
    exact hcoord_mem
  have hmN : m < 2 ^ (m + 1) := by
    have hlt : m < 2 ^ m := Nat.lt_two_pow_self
    have hle : 2 ^ m ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (Nat.le_succ m)
    omega
  have hcoord_tors : a ∈ Ideal.torsionOf (PowerSeries k) (powerSeriesQuotientByXPow k n)
      (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (2 ^ m))) := by
    have hcoord_zero' :
        a • powerSeriesSparseDirectSumTrunc k (2 ^ (m + 1)) n = 0 := by
      change (a • powerSeriesSparseDirectSumTrunc k (2 ^ (m + 1))) n = 0
      exact hcoord_zero
    rw [Ideal.mem_torsionOf_iff]
    rwa [powerSeriesSparseDirectSumTrunc_apply_twoPowSucc (k := k) (N := 2 ^ (m + 1))
      (m := m) hmN] at hcoord_zero'
  have hn_eq : (n : ℕ) = 2 ^ (m + 1) := by
    rfl
  have htors := powerSeriesQuotientByXPow_torsionOf_sparseCoordinate
    (k := k) (n := n) (m := m) hn_eq
  rwa [htors] at hcoord_tors

/-- Helper for Chap10 Example 10 91 5: `X^(2^m)` annihilates the sparse direct-sum truncation
modulo `X^(2^(m+1))`. -/
private lemma powerSeriesSparseDirectSumTrunc_generator_mem_annihilator (m : ℕ) :
    ((PowerSeries.X : PowerSeries k) ^ (2 ^ m)) ∈
      Ideal.torsionOf (PowerSeries k)
        (powerSeriesQuotientDirectSum k ⧸
          powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSum k) (2 ^ (m + 1)))
        (Submodule.Quotient.mk (powerSeriesSparseDirectSumTrunc k (2 ^ (m + 1)))) := by
  rw [Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  dsimp [powerSeriesSparseDirectSumTrunc]
  -- Each finite-support coordinate term is individually an `X^(2^(m+1))`-multiple.
  exact powerSeriesSparseDirectSum_scaled_sum_mem (k := k) m (Finset.range (2 ^ (m + 1)))

/-- Helper for Chap10 Example 10 91 5: the sparse direct-sum truncation has the expected
annihilator exponent at a power-of-two stage. -/
private lemma powerSeriesSparseDirectSumTrunc_annihilatorExponent (m : ℕ) :
    HasAnnihilatorExponent k (powerSeriesQuotientDirectSum k)
      (powerSeriesSparseDirectSumTrunc k (2 ^ (m + 1))) (2 ^ (m + 1)) (2 ^ m) := by
  unfold HasAnnihilatorExponent
  apply le_antisymm
  · exact powerSeriesSparseDirectSumTrunc_annihilator_le (k := k) m
  · refine Ideal.span_le.mpr ?_
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact powerSeriesSparseDirectSumTrunc_generator_mem_annihilator (k := k) m

/-- Helper for Chap10 Example 10 91 5: a linear equivalence preserves annihilator ideals. -/
private lemma torsionOf_linearEquiv_eq
    {R : Type u} [CommRing R] {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (x : M) :
    Ideal.torsionOf R N (e x) = Ideal.torsionOf R M x := by
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  constructor
  · intro h
    exact e.injective (by simpa using h)
  · intro h
    have h' := congrArg e h
    simpa using h'

/-- Helper for Chap10 Example 10 91 5: the sparse completion element has the expected
annihilator exponent at a power-of-two stage. -/
private lemma powerSeriesSparseCompletionElement_annihilatorExponent (m : ℕ) :
    HasAnnihilatorExponent k (powerSeriesQuotientDirectSumCompletion k)
      (powerSeriesSparseCompletionElement k) (2 ^ (m + 1)) (2 ^ m) := by
  unfold HasAnnihilatorExponent
  calc
    Ideal.torsionOf (PowerSeries k)
        (powerSeriesQuotientDirectSumCompletion k ⧸
          powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSumCompletion k) (2 ^ (m + 1)))
        (Submodule.Quotient.mk (powerSeriesSparseCompletionElement k)) =
      Ideal.torsionOf (PowerSeries k)
        (powerSeriesQuotientDirectSum k ⧸
          powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSum k) (2 ^ (m + 1)))
        (powerSeriesCompletionQuotientEquiv k (2 ^ (m + 1))
          (Submodule.Quotient.mk (powerSeriesSparseCompletionElement k))) := by
      symm
      exact torsionOf_linearEquiv_eq (powerSeriesCompletionQuotientEquiv k (2 ^ (m + 1)))
        (Submodule.Quotient.mk (powerSeriesSparseCompletionElement k))
    _ = Ideal.torsionOf (PowerSeries k)
        (powerSeriesQuotientDirectSum k ⧸
          powerSeriesXPowSubmodule k (powerSeriesQuotientDirectSum k) (2 ^ (m + 1)))
        (Submodule.Quotient.mk (powerSeriesSparseDirectSumTrunc k (2 ^ (m + 1)))) := by
      rw [powerSeriesCompletionQuotientEquiv_apply]
    _ = Ideal.span ({(PowerSeries.X : PowerSeries k) ^ (2 ^ m)} : Set (PowerSeries k)) :=
      powerSeriesSparseDirectSumTrunc_annihilatorExponent (k := k) m

/-- Helper for Chap10 Example 10 91 5: the completed direct sum contains a sparse element with the
same half-exponent annihilator behavior as the product element. -/
lemma powerSeriesQuotientDirectSumCompletion_hasSparseHalfAnnihilator :
    HasSparseHalfAnnihilator k (powerSeriesQuotientDirectSumCompletion k) := by
  -- The Cauchy-sequence element has the same exact annihilator at every power-of-two quotient.
  exact ⟨powerSeriesSparseCompletionElement k, 0, fun m _ ↦
    powerSeriesSparseCompletionElement_annihilatorExponent (k := k) m⟩

/-- Helper for Chap10 Example 10 91 5: sparse half-exponent annihilator growth is incompatible
with the Mittag-Leffler finite-presentation kernel criterion. -/
lemma not_mittagLeffler_of_sparseHalfAnnihilatorExponents
    {M : Type u} [AddCommGroup M] [Module (PowerSeries k) M]
    (hM : HasSparseHalfAnnihilator k M) :
    ¬ MittagLeffler (PowerSeries k) M := by
  rintro hML
  rcases hM with ⟨x, m0, hx⟩
  let R := PowerSeries k
  let I : Ideal R := powerSeriesXIdeal k
  let f : R →ₗ[R] M := LinearMap.toSpanSingleton R M x
  have hcondition := mittagLeffler_kernel_condition (R := R) (M := M) hML
  obtain ⟨Q, hQfp, g, hker⟩ := hcondition (ModuleCat.of R R) f
  letI : Module.FinitePresentation R Q := hQfp
  have hQfinite : Module.Finite R Q := inferInstance
  have hxbot : Ideal.torsionOf R M x = ⊥ :=
    sparseHalfAnnihilator_torsion_eq_bot (k := k) x m0 hx
  have hker_R : LinearMap.ker f = LinearMap.ker g :=
    ker_eq_of_rTensor_self_kernel_eq (R := R) (M := M) (Q := Q) (hker (ModuleCat.of R R))
  have hqbot : Ideal.torsionOf R Q (g 1) = ⊥ := by
    have hfker : LinearMap.ker f = Ideal.torsionOf R M x := by
      rw [linearMap_ker_eq_torsion_one (R := R) f]
      simp [f, LinearMap.toSpanSingleton]
    rw [← linearMap_ker_eq_torsion_one (R := R) g, ← hker_R, hfker, hxbot]
  obtain ⟨c, hc⟩ := Ideal.exists_exact_preimage_pow_smul_eq (I := I) (f := g)
  let m := c + m0 + 1
  have hm0 : m0 ≤ m := by omega
  let L := 2 ^ (m + 1)
  let e := 2 ^ m
  have he_pos : c < e := by
    have hlt : c < 2 ^ c := Nat.lt_two_pow_self
    have hle : 2 ^ c ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega)
    omega
  have hLge : c ≤ L := by
    have he_le_L : e ≤ L := by
      dsimp [L, e]
      exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (Nat.le_succ m)
    omega
  have hstage := hx m hm0
  have htorsQ : Ideal.torsionOf R
      (Q ⧸ powerSeriesXPowSubmodule k Q L) (Submodule.Quotient.mk (g 1)) =
      Ideal.span ({(PowerSeries.X : R) ^ e} : Set R) := by
    have htorsM := hstage
    unfold HasAnnihilatorExponent at htorsM
    have hkerL :=
      hker (ModuleCat.of R (R ⧸ Ideal.span ({(PowerSeries.X : R) ^ L} : Set R)))
    have hIeq : I ^ L = Ideal.span ({(PowerSeries.X : R) ^ L} : Set R) := by
      simp [I, powerSeriesXIdeal, Ideal.span_singleton_pow]
    have htors_eq := torsion_eq_of_rTensor_kernel_eq (R := R) (M := M) (Q := Q)
      x g (Ideal.span ({(PowerSeries.X : R) ^ L} : Set R)) (by simpa [hIeq] using hkerL)
    have htors_eq' : Ideal.torsionOf R
        (M ⧸ powerSeriesXPowSubmodule k M L) (Submodule.Quotient.mk x) =
        Ideal.torsionOf R (Q ⧸ powerSeriesXPowSubmodule k Q L)
          (Submodule.Quotient.mk (g 1)) := by
      simpa [powerSeriesXPowSubmodule] using htors_eq
    exact htors_eq'.symm.trans (by simpa [L, e] using htorsM)
  have hgen_mem : (PowerSeries.X : R) ^ e ∈ Ideal.torsionOf R
      (Q ⧸ powerSeriesXPowSubmodule k Q L) (Submodule.Quotient.mk (g 1)) := by
    rw [htorsQ]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hpre : (PowerSeries.X : R) ^ e ∈
      Submodule.comap g (I ^ L • (⊤ : Submodule R Q)) := by
    rw [Ideal.mem_torsionOf_iff] at hgen_mem
    rw [← Submodule.Quotient.mk_smul] at hgen_mem
    have hgmap : g ((PowerSeries.X : R) ^ e) = ((PowerSeries.X : R) ^ e) • g 1 := by
      simpa using g.map_smul ((PowerSeries.X : R) ^ e) (1 : R)
    rw [← hgmap, Submodule.Quotient.mk_eq_zero] at hgen_mem
    rw [Submodule.mem_comap]
    rwa [powerSeriesXIdeal_pow_smul_top (k := k) Q L]
  have hpre_cut : (PowerSeries.X : R) ^ e ∈
      I ^ (L - c) • (⊤ : Submodule R R) := by
    have hcL := hc L hLge
    rw [hcL] at hpre
    have hgker_bot : LinearMap.ker g = ⊥ := by
      rw [linearMap_ker_eq_torsion_one (R := R) g, hqbot]
    rw [hgker_bot, bot_sup_eq] at hpre
    exact (Submodule.smul_mono (le_refl (I ^ (L - c) : Ideal R)) le_top) hpre
  have hspan_mem : (PowerSeries.X : R) ^ e ∈
      Ideal.span ({(PowerSeries.X : R) ^ (L - c)} : Set R) := by
    have hideal : (PowerSeries.X : R) ^ e ∈ I ^ (L - c) := by
      simpa using hpre_cut
    simpa [I, powerSeriesXIdeal, Ideal.span_singleton_pow] using hideal
  have hlt_exp : e < L - c := by
    have hsum : e + c < L := by
      have hL_eq : L = e + e := by
        dsimp [L, e]
        rw [pow_succ, mul_comm, two_mul]
      rw [hL_eq]
      omega
    exact Nat.lt_sub_of_add_lt hsum
  have hcoeff := powerSeries_coeff_eq_zero_of_mem_span_X_pow (k := k)
    (a := (PowerSeries.X : R) ^ e) (e := L - c) (n := e) hspan_mem hlt_exp
  have hone : PowerSeries.coeff e ((PowerSeries.X : R) ^ e) = 1 := by
    simp
  exact one_ne_zero (hone.symm.trans hcoeff)

-- Proof sketch: use the element `ξ` supported at powers of two from the textbook. Its
-- annihilator in `(∏ n, R/(x^n)) / x^l` behaves like `x^(l / 2)` along powers of two, which is
-- incompatible with the annihilator growth permitted by Proposition `10.88.6 (1)` for a
-- Mittag-Leffler module.
/-- The product `∏_{n ≥ 1} k[[x]] / (x^n)` is not Mittag-Leffler over `k[[x]]`. -/
theorem powerSeriesQuotientProduct_not_mittagLeffler :
    ¬ MittagLeffler (PowerSeries k) (powerSeriesQuotientProduct k) := by
  -- The named sparse-element calculation supplies the concrete invariant; the generic obstruction
  -- turns that invariant into failure of the Mittag-Leffler condition.
  exact not_mittagLeffler_of_sparseHalfAnnihilatorExponents k
    (powerSeriesSparseProductElement_hasSparseHalfAnnihilator k)

-- Proof sketch: the same annihilator calculation applies because the element `ξ` from the
-- textbook actually lies in the `x`-adic completion of the direct sum, so the previous
-- contradiction with Proposition `10.88.6 (1)` still goes through.
/-- The `x`-adic completion of `⨁_{n ≥ 1} k[[x]] / (x^n)` is not Mittag-Leffler over `k[[x]]`. -/
theorem powerSeriesQuotientDirectSumCompletion_not_mittagLeffler :
    ¬ MittagLeffler (PowerSeries k) (powerSeriesQuotientDirectSumCompletion k) := by
  -- The completion-stage comparison produces the same sparse invariant, so the same generic
  -- obstruction closes the target.
  exact not_mittagLeffler_of_sparseHalfAnnihilatorExponents k
    (powerSeriesQuotientDirectSumCompletion_hasSparseHalfAnnihilator k)

/-- Helper for Chap10 Example 10 91 5: the ideal cutting out the square-zero pair ring. -/
private abbrev squareZeroPairIdeal : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span
    ({(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2,
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1,
      (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ^ 2} : Set (MvPolynomial (Fin 2) k))

/-- The square-zero quotient ring `k[a, b] / (a^2, ab, b^2)` of the final example. -/
abbrev squareZeroPairRing :=
  MvPolynomial (Fin 2) k ⧸
    Ideal.span
      ({(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2,
        (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1,
        (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ^ 2} : Set (MvPolynomial (Fin 2) k))

/-- The class of `a` in `k[a, b] / (a^2, ab, b^2)`. -/
abbrev squareZeroPairRingA : squareZeroPairRing k :=
  Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The class of `b` in `k[a, b] / (a^2, ab, b^2)`. -/
abbrev squareZeroPairRingB : squareZeroPairRing k :=
  Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The finitely presented algebra `R[t] / (at - b)` over `R = k[a, b] / (a^2, ab, b^2)`. -/
abbrev squareZeroPairAlgebra :=
  Polynomial (squareZeroPairRing k) ⧸
    Ideal.span
      ({Polynomial.C (squareZeroPairRingA k) * Polynomial.X - Polynomial.C (squareZeroPairRingB k)} :
        Set (Polynomial (squareZeroPairRing k)))

local instance squareZeroPairRingCommRing : CommRing (squareZeroPairRing k) :=
  show CommRing (squareZeroPairRing k) from Ideal.Quotient.commRing _

local instance squareZeroPairAlgebraCommRing : CommRing (squareZeroPairAlgebra k) :=
  show CommRing (squareZeroPairAlgebra k) from Ideal.Quotient.commRing _

local instance squareZeroPairAlgebraAlgebra : Algebra (squareZeroPairRing k) (squareZeroPairAlgebra k) :=
  show Algebra (squareZeroPairRing k) (squareZeroPairAlgebra k) from Ideal.instAlgebraQuotient _ _

local instance squareZeroPairAlgebraModule : Module (squareZeroPairRing k) (squareZeroPairAlgebra k) :=
  Algebra.toModule

/-- Helper for Chap10 Example 10 91 5: the square-zero pair ring acts on itself by
multiplication. -/
local instance squareZeroPairRingModuleSelf : Module (squareZeroPairRing k) (squareZeroPairRing k) :=
  Semiring.toModule

/-- Helper for Chap10 Example 10 91 5: polynomials over the square-zero pair ring are modules
over their coefficient ring. -/
local instance squareZeroPairPolynomialModule :
    Module (squareZeroPairRing k) (Polynomial (squareZeroPairRing k)) :=
  Algebra.toModule

/-- Helper for Chap10 Example 10 91 5: the polynomial ring over the square-zero pair ring acts
on itself by multiplication. -/
local instance squareZeroPairPolynomialModuleSelf :
    Module (Polynomial (squareZeroPairRing k)) (Polynomial (squareZeroPairRing k)) :=
  Semiring.toModule

-- Proof sketch: the quotient `R[t] / (at - b)` is generated by the powers of `t`, so it is
-- countably generated as an `R`-module.
/-- The algebra `R[t] / (at - b)` is countably generated as an `R`-module. -/
theorem squareZeroPairAlgebra_countablyGenerated :
    CountablyGenerated (squareZeroPairRing k) (squareZeroPairAlgebra k) := by
  let I : Ideal (Polynomial (squareZeroPairRing k)) :=
    Ideal.span
      ({Polynomial.C (squareZeroPairRingA k) * Polynomial.X - Polynomial.C (squareZeroPairRingB k)} :
        Set (Polynomial (squareZeroPairRing k)))
  change CountablyGenerated (squareZeroPairRing k) (Polynomial (squareZeroPairRing k) ⧸ I)
  let s : Set (Polynomial (squareZeroPairRing k) ⧸ I) :=
    Set.range (fun n : ℕ =>
      Ideal.Quotient.mk I ((Polynomial.X : Polynomial (squareZeroPairRing k)) ^ n))
  rw [Module.countablyGenerated_iff]
  refine ⟨s, Set.countable_range _, ?_⟩
  -- It is enough to show that every polynomial representative maps into the span of the images
  -- of the monomials `X^n`.
  suffices hspan : ∀ p : Polynomial (squareZeroPairRing k),
      Ideal.Quotient.mk I p ∈ Submodule.span (squareZeroPairRing k) s by
    apply eq_top_iff.2
    intro y _
    rcases Ideal.Quotient.mk_surjective y with ⟨p, rfl⟩
    exact hspan p
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      -- The span is an additive subgroup, so the induction step for sums is immediate.
      simpa using (Submodule.span (squareZeroPairRing k) s).add_mem hp hq
  | monomial n a =>
      -- A monomial is a scalar multiple of `X^n`, whose quotient class is one of the chosen
      -- generators.
      have hx : Ideal.Quotient.mk I ((Polynomial.X : Polynomial (squareZeroPairRing k)) ^ n) ∈
          Submodule.span (squareZeroPairRing k) s := by
        exact Submodule.subset_span (Set.mem_range_self n)
      have hmem := (Submodule.span (squareZeroPairRing k) s).smul_mem a hx
      have hmul :
          (algebraMap (squareZeroPairRing k) (Polynomial (squareZeroPairRing k) ⧸ I)) a *
              Ideal.Quotient.mk I ((Polynomial.X : Polynomial (squareZeroPairRing k)) ^ n) =
            Ideal.Quotient.mk I ((Polynomial.monomial n) a) := by
        rw [← Ideal.Quotient.mk_algebraMap (R₁ := squareZeroPairRing k)
          (A := Polynomial (squareZeroPairRing k)) I a]
        rw [Polynomial.algebraMap_eq]
        rw [← map_mul]
        rw [Polynomial.C_mul_X_pow_eq_monomial]
      rwa [Algebra.smul_def, hmul] at hmem

-- Route correction: the final square-zero proof now separates the henselian-local input, the
-- source-facing direct-sum obstruction, and the short Lemma 10.153.13 contradiction.
/-- Helper for Chap10 Example 10 91 5: the square-zero ideal is contained in the kernel of the
constant-coefficient map. -/
private lemma squareZeroPairIdeal_le_constantCoeff_ker :
    squareZeroPairIdeal k ≤
      RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin 2) k →+* k) := by
  -- Each defining quadratic has zero constant coefficient, so the whole span maps to zero.
  apply Ideal.span_le.mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · simp [RingHom.mem_ker]
  · simp [RingHom.mem_ker]
  · simp [RingHom.mem_ker]

/-- Helper for Chap10 Example 10 91 5: the square-zero ideal is proper. -/
private lemma squareZeroPairIdeal_ne_top : squareZeroPairIdeal k ≠ ⊤ := by
  -- If the ideal were the whole ring, `1` would have zero constant coefficient.
  intro htop
  have hone : (1 : MvPolynomial (Fin 2) k) ∈ squareZeroPairIdeal k := by
    simpa [htop]
  have hker := squareZeroPairIdeal_le_constantCoeff_ker (k := k) hone
  simpa [RingHom.mem_ker] using hker

/-- Helper for Chap10 Example 10 91 5: the square-zero pair quotient is nontrivial. -/
private lemma squareZeroPairRing_nontrivial : Nontrivial (squareZeroPairRing k) := by
  -- Properness of the defining ideal is exactly nontriviality of the quotient.
  exact Ideal.Quotient.nontrivial_iff.mpr (squareZeroPairIdeal_ne_top (k := k))

/-- Helper for Chap10 Example 10 91 5: the square of the variable ideal maps into the
square-zero defining ideal. -/
private lemma squareZeroPairIdeal_idealOfVars_sq_le :
    MvPolynomial.idealOfVars (Fin 2) k ^ 2 ≤ squareZeroPairIdeal k := by
  -- The variable ideal is generated by `X 0` and `X 1`; its square is generated by the four
  -- pairwise products, three of which are the defining generators and the fourth is equal by
  -- commutativity.
  rw [show MvPolynomial.idealOfVars (Fin 2) k =
    Ideal.span ({(MvPolynomial.X 0 : MvPolynomial (Fin 2) k), MvPolynomial.X 1} :
      Set (MvPolynomial (Fin 2) k)) by
      rw [MvPolynomial.idealOfVars]
      congr
      ext p
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (hp | hp)
        · exact ⟨0, hp.symm⟩
        · exact ⟨1, hp.symm⟩]
  rw [pow_two, Ideal.span_pair_mul_span_pair]
  apply Ideal.span_le.mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact Ideal.subset_span (by simp [pow_two])
  · exact Ideal.subset_span (by simp)
  · simpa [mul_comm] using
      (Ideal.subset_span (by
        simp : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1 ∈
          ({(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2,
            (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1,
            (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ^ 2} :
              Set (MvPolynomial (Fin 2) k))))
  · exact Ideal.subset_span (by simp [pow_two])

/-- Helper for Chap10 Example 10 91 5: a class with zero constant coefficient is square-zero. -/
private lemma squareZeroPairRing_isNilpotent_mk_of_constantCoeff_eq_zero
    {p : MvPolynomial (Fin 2) k} (hp : MvPolynomial.constantCoeff p = 0) :
    IsNilpotent (Ideal.Quotient.mk (squareZeroPairIdeal k) p : squareZeroPairRing k) := by
  -- Zero constant coefficient puts `p` in the variable ideal; after squaring, the previous helper
  -- puts `p^2` in the defining ideal, so the quotient class is nilpotent.
  refine ⟨2, ?_⟩
  rw [pow_two, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hp_var : p ∈ MvPolynomial.idealOfVars (Fin 2) k := by
    rw [← pow_one (MvPolynomial.idealOfVars (Fin 2) k),
      MvPolynomial.mem_pow_idealOfVars_iff' 1]
    intro d hd
    have hd0 : d = 0 := by
      exact (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst d
    simpa [MvPolynomial.constantCoeff_eq] using hp
  have hp_var_pow : p ∈ MvPolynomial.idealOfVars (Fin 2) k ^ 1 := by
    simpa using hp_var
  exact squareZeroPairIdeal_idealOfVars_sq_le (k := k)
    (Ideal.mul_mem_mul hp_var_pow hp_var)

/-- Helper for Chap10 Example 10 91 5: the square-zero pair quotient is local. -/
private lemma squareZeroPairRing_isLocalRing : IsLocalRing (squareZeroPairRing k) := by
  letI : Nontrivial (squareZeroPairRing k) := squareZeroPairRing_nontrivial k
  -- An element is a unit when its constant coefficient is nonzero; otherwise it is nilpotent, so
  -- `1 - x` is a unit.
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self ?_
  intro x
  rcases Ideal.Quotient.mk_surjective x with ⟨p, rfl⟩
  by_cases hp0 : MvPolynomial.constantCoeff p = 0
  · right
    exact (squareZeroPairRing_isNilpotent_mk_of_constantCoeff_eq_zero (k := k) hp0).isUnit_one_sub
  · left
    have hunitC : IsUnit (algebraMap k (squareZeroPairRing k) (MvPolynomial.constantCoeff p)) := by
      exact RingHom.isUnit_map _ (isUnit_iff_ne_zero.mpr hp0)
    have hnil : IsNilpotent
        (Ideal.Quotient.mk (squareZeroPairIdeal k)
          (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) : squareZeroPairRing k) := by
      apply squareZeroPairRing_isNilpotent_mk_of_constantCoeff_eq_zero (k := k)
      simp
    have hdecomp : Ideal.Quotient.mk (squareZeroPairIdeal k) p =
        algebraMap k (squareZeroPairRing k) (MvPolynomial.constantCoeff p) +
          Ideal.Quotient.mk (squareZeroPairIdeal k)
            (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) := by
      rw [← Ideal.Quotient.mk_algebraMap (R₁ := k) (A := MvPolynomial (Fin 2) k)
        (squareZeroPairIdeal k) (MvPolynomial.constantCoeff p)]
      rw [← map_add]
      congr 1
      rw [MvPolynomial.algebraMap_eq]
      abel
    rw [hdecomp]
    exact hnil.isUnit_add_left_of_commute hunitC (Commute.all _ _)

/-- Helper for Chap10 Example 10 91 5: the square-zero pair quotient is finite over `k`. -/
private lemma squareZeroPairRing_moduleFinite : Module.Finite k (squareZeroPairRing k) := by
  let s : Set (squareZeroPairRing k) :=
    {Ideal.Quotient.mk (squareZeroPairIdeal k) (1 : MvPolynomial (Fin 2) k),
      Ideal.Quotient.mk (squareZeroPairIdeal k) (MvPolynomial.X 0),
      Ideal.Quotient.mk (squareZeroPairIdeal k) (MvPolynomial.X 1)}
  let S : Submodule k (squareZeroPairRing k) := Submodule.span k s
  -- Each monomial class is either constant, one of the two linear generators, or zero because it
  -- has degree at least two.
  have hmono :
      ∀ d c, Ideal.Quotient.mk (squareZeroPairIdeal k) (MvPolynomial.monomial d c) ∈ S := by
    intro d c
    by_cases hd0 : d.degree = 0
    · have hd : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd0
      subst d
      have h1mem : Ideal.Quotient.mk (squareZeroPairIdeal k) (1 : MvPolynomial (Fin 2) k) ∈
          S := by
        exact Submodule.subset_span (by simp [s])
      have hmem := S.smul_mem c h1mem
      simpa [S, Algebra.smul_def, Ideal.Quotient.mk_algebraMap] using hmem
    · by_cases hd1 : d.degree = 1
      · have hd_range : d ∈ Set.range (fun i : Fin 2 => Finsupp.single i 1) := by
          rw [Finsupp.range_single_one]
          exact hd1
        rcases hd_range with ⟨i, rfl⟩
        fin_cases i
        · have hxmem : Ideal.Quotient.mk (squareZeroPairIdeal k) (MvPolynomial.X 0) ∈ S := by
            exact Submodule.subset_span (by simp [s])
          have hmem := S.smul_mem c hxmem
          rw [← MvPolynomial.C_mul_X_eq_monomial]
          simpa [S, Algebra.smul_def, Ideal.Quotient.mk_algebraMap, map_mul] using hmem
        · have hxmem : Ideal.Quotient.mk (squareZeroPairIdeal k) (MvPolynomial.X 1) ∈ S := by
            exact Submodule.subset_span (by simp [s])
          have hmem := S.smul_mem c hxmem
          rw [← MvPolynomial.C_mul_X_eq_monomial]
          simpa [S, Algebra.smul_def, Ideal.Quotient.mk_algebraMap, map_mul] using hmem
      · have hd2 : 2 ≤ d.degree := by
          omega
        by_cases hc : c = 0
        · simp [hc, S]
        · have hmem_m2 :
              MvPolynomial.monomial d c ∈ MvPolynomial.idealOfVars (Fin 2) k ^ 2 := by
            exact (MvPolynomial.monomial_mem_pow_idealOfVars_iff
              (σ := Fin 2) (R := k) 2 d hc).mpr hd2
          have hmemI : MvPolynomial.monomial d c ∈ squareZeroPairIdeal k :=
            squareZeroPairIdeal_idealOfVars_sq_le (k := k) hmem_m2
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmemI]
          exact S.zero_mem
  have hmem : ∀ p : MvPolynomial (Fin 2) k,
      Ideal.Quotient.mk (squareZeroPairIdeal k) p ∈ S := by
    intro p
    exact MvPolynomial.induction_on' (P := fun p =>
      Ideal.Quotient.mk (squareZeroPairIdeal k) p ∈ S) p hmono
      (fun p q hp hq => by
        simpa using S.add_mem hp hq)
  refine Module.Finite.of_fg_top ?_
  have hspan : S = (⊤ : Submodule k (squareZeroPairRing k)) := by
    apply eq_top_iff.2
    intro y _
    rcases Ideal.Quotient.mk_surjective y with ⟨p, rfl⟩
    exact hmem p
  have hfg : S.FG := by
    exact Submodule.fg_span (by simp [s])
  exact hspan ▸ hfg

/-- Helper for Chap10 Example 10 91 5: the square-zero pair quotient has Krull dimension zero. -/
private lemma squareZeroPairRing_krullDimLE_zero : Ring.KrullDimLE 0 (squareZeroPairRing k) := by
  -- A finite algebra over the Artinian field `k` is Artinian, hence zero-dimensional.
  letI : Module.Finite k (squareZeroPairRing k) := squareZeroPairRing_moduleFinite k
  have hArt : IsArtinianRing (squareZeroPairRing k) :=
    IsArtinianRing.of_finite k (squareZeroPairRing k)
  exact (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp hArt).2

/-- Helper for Chap10 Example 10 91 5: a zero-dimensional local square-zero pair ring is
henselian. -/
private lemma squareZeroPairRing_henselianLocalRing_of_krullDimLE_zero
    [IsLocalRing (squareZeroPairRing k)] [Ring.KrullDimLE 0 (squareZeroPairRing k)] :
    HenselianLocalRing (squareZeroPairRing k) := by
  -- Once the local and zero-dimensional structure is isolated, Lemma 10.153.10 supplies the
  -- henselian-local conclusion.
  exact localRing_henselian_of_krullDimLE_zero (squareZeroPairRing k)

/-- Helper for Chap10 Example 10 91 5: the square-zero pair ring is henselian local. -/
lemma squareZeroPairRing_henselianLocalRing : HenselianLocalRing (squareZeroPairRing k) := by
  -- The quotient is local and zero-dimensional by the preceding concrete square-zero
  -- computations; Lemma 10.153.10 then gives henselianity.
  letI : IsLocalRing (squareZeroPairRing k) := squareZeroPairRing_isLocalRing k
  letI : Ring.KrullDimLE 0 (squareZeroPairRing k) := squareZeroPairRing_krullDimLE_zero k
  exact squareZeroPairRing_henselianLocalRing_of_krullDimLE_zero k

/-- Helper for Chap10 Example 10 91 5: the defining square-zero ideal is contained in the square
of the variable ideal. -/
private lemma squareZeroPairIdeal_le_idealOfVars_sq :
    squareZeroPairIdeal k ≤ MvPolynomial.idealOfVars (Fin 2) k ^ 2 := by
  apply Ideal.span_le.mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  have hx0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ∈
      MvPolynomial.idealOfVars (Fin 2) k :=
    Ideal.subset_span (Set.mem_range_self 0)
  have hx1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∈
      MvPolynomial.idealOfVars (Fin 2) k :=
    Ideal.subset_span (Set.mem_range_self 1)
  rcases hp with rfl | rfl | rfl
  · simpa [pow_two] using Ideal.mul_mem_mul hx0 hx0
  · simpa [pow_two] using Ideal.mul_mem_mul hx0 hx1
  · simpa [pow_two] using Ideal.mul_mem_mul hx1 hx1

/-- Helper for Chap10 Example 10 91 5: low-degree coefficient functionals vanish on the
square-zero ideal. -/
private lemma squareZeroPairIdeal_lcoeff_ker {d : Fin 2 →₀ ℕ} (hd : d.degree < 2) :
    (squareZeroPairIdeal k).restrictScalars k ≤ LinearMap.ker (MvPolynomial.lcoeff k d) := by
  intro p hp
  rw [LinearMap.mem_ker]
  exact (MvPolynomial.mem_pow_idealOfVars_iff' 2 p).mp
    (squareZeroPairIdeal_le_idealOfVars_sq (k := k) hp) d hd

/-- Helper for Chap10 Example 10 91 5: the zero multi-index has degree less than two. -/
private lemma squareZeroPairZeroDegree_lt_two : (0 : Fin 2 →₀ ℕ).degree < 2 := by
  simp

/-- Helper for Chap10 Example 10 91 5: a degree-one multi-index has degree less than two. -/
private lemma squareZeroPairSingleDegree_lt_two (i : Fin 2) :
    (Finsupp.single i 1 : Fin 2 →₀ ℕ).degree < 2 := by
  rw [Finsupp.degree_single]
  norm_num

/-- Helper for Chap10 Example 10 91 5: a low-degree coefficient functional on the square-zero
pair ring. -/
private def squareZeroPairCoeff (d : Fin 2 →₀ ℕ) (hd : d.degree < 2) :
    squareZeroPairRing k →ₗ[k] k :=
  Submodule.liftQ ((squareZeroPairIdeal k).restrictScalars k) (MvPolynomial.lcoeff k d)
    (squareZeroPairIdeal_lcoeff_ker (k := k) hd)

/-- Helper for Chap10 Example 10 91 5: the scalar coefficient of an element of the square-zero
pair ring. -/
private def squareZeroPairConstCoeff : squareZeroPairRing k →ₗ[k] k :=
  squareZeroPairCoeff k 0 squareZeroPairZeroDegree_lt_two

/-- Helper for Chap10 Example 10 91 5: the `a`-coefficient of an element of the square-zero pair
ring. -/
private def squareZeroPairACoeff : squareZeroPairRing k →ₗ[k] k :=
  squareZeroPairCoeff k (Finsupp.single 0 1) (squareZeroPairSingleDegree_lt_two 0)

/-- Helper for Chap10 Example 10 91 5: the `b`-coefficient of an element of the square-zero pair
ring. -/
private def squareZeroPairBCoeff : squareZeroPairRing k →ₗ[k] k :=
  squareZeroPairCoeff k (Finsupp.single 1 1) (squareZeroPairSingleDegree_lt_two 1)

/-- Helper for Chap10 Example 10 91 5: coefficient functionals evaluate on quotient classes by
the corresponding polynomial coefficient. -/
private lemma squareZeroPairCoeff_mk (d : Fin 2 →₀ ℕ) (hd : d.degree < 2)
    (p : MvPolynomial (Fin 2) k) :
    squareZeroPairCoeff k d hd (Ideal.Quotient.mk (squareZeroPairIdeal k) p) =
      MvPolynomial.lcoeff k d p := by
  change squareZeroPairCoeff k d hd
      (Submodule.Quotient.mk (p := (squareZeroPairIdeal k).restrictScalars k) p) =
    MvPolynomial.lcoeff k d p
  exact Submodule.liftQ_apply ((squareZeroPairIdeal k).restrictScalars k)
    (MvPolynomial.lcoeff k d) p

/-- Helper for Chap10 Example 10 91 5: the scalar coefficient of `1` is `1`. -/
private lemma squareZeroPairConstCoeff_one :
    squareZeroPairConstCoeff k (1 : squareZeroPairRing k) = 1 := by
  change squareZeroPairConstCoeff k
      (Ideal.Quotient.mk (squareZeroPairIdeal k) (1 : MvPolynomial (Fin 2) k)) = 1
  rw [squareZeroPairConstCoeff, squareZeroPairCoeff_mk]
  simp [MvPolynomial.lcoeff]

/-- Helper for Chap10 Example 10 91 5: scalar coefficients multiply multiplicatively. -/
private lemma squareZeroPairConstCoeff_mul (x y : squareZeroPairRing k) :
    squareZeroPairConstCoeff k (x * y) =
      squareZeroPairConstCoeff k x * squareZeroPairConstCoeff k y := by
  rcases Ideal.Quotient.mk_surjective x with ⟨p, rfl⟩
  rcases Ideal.Quotient.mk_surjective y with ⟨q, rfl⟩
  rw [← map_mul, squareZeroPairConstCoeff, squareZeroPairCoeff_mk,
    squareZeroPairCoeff_mk, squareZeroPairCoeff_mk]
  simp [MvPolynomial.lcoeff, MvPolynomial.coeff_mul]

/-- Helper for Chap10 Example 10 91 5: multiplying by `a` kills scalar coefficients. -/
private lemma squareZeroPairConstCoeff_A_mul (x : squareZeroPairRing k) :
    squareZeroPairConstCoeff k (squareZeroPairRingA k * x) = 0 := by
  rcases Ideal.Quotient.mk_surjective x with ⟨p, rfl⟩
  rw [squareZeroPairRingA, ← map_mul, squareZeroPairConstCoeff, squareZeroPairCoeff_mk,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_X_mul']
  simp

/-- Helper for Chap10 Example 10 91 5: multiplying by `b` kills scalar coefficients. -/
private lemma squareZeroPairConstCoeff_B_mul (x : squareZeroPairRing k) :
    squareZeroPairConstCoeff k (squareZeroPairRingB k * x) = 0 := by
  rcases Ideal.Quotient.mk_surjective x with ⟨p, rfl⟩
  rw [squareZeroPairRingB, ← map_mul, squareZeroPairConstCoeff, squareZeroPairCoeff_mk,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_X_mul']
  simp

/-- Helper for Chap10 Example 10 91 5: multiplying by `a` shifts scalar coefficients to
`a`-coefficients. -/
private lemma squareZeroPairACoeff_A_mul (x : squareZeroPairRing k) :
    squareZeroPairACoeff k (squareZeroPairRingA k * x) = squareZeroPairConstCoeff k x := by
  rcases Ideal.Quotient.mk_surjective x with ⟨p, rfl⟩
  rw [squareZeroPairRingA, ← map_mul, squareZeroPairACoeff, squareZeroPairConstCoeff,
    squareZeroPairCoeff_mk, squareZeroPairCoeff_mk, MvPolynomial.lcoeff_apply,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_X_mul']
  simp

/-- Helper for Chap10 Example 10 91 5: multiplying by `a` kills `b`-coefficients. -/
private lemma squareZeroPairBCoeff_A_mul (x : squareZeroPairRing k) :
    squareZeroPairBCoeff k (squareZeroPairRingA k * x) = 0 := by
  rcases Ideal.Quotient.mk_surjective x with ⟨p, rfl⟩
  rw [squareZeroPairRingA, ← map_mul, squareZeroPairBCoeff, squareZeroPairCoeff_mk,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_X_mul']
  simp

/-- Helper for Chap10 Example 10 91 5: multiplying by `b` kills `a`-coefficients. -/
private lemma squareZeroPairACoeff_B_mul (x : squareZeroPairRing k) :
    squareZeroPairACoeff k (squareZeroPairRingB k * x) = 0 := by
  rcases Ideal.Quotient.mk_surjective x with ⟨p, rfl⟩
  rw [squareZeroPairRingB, ← map_mul, squareZeroPairACoeff, squareZeroPairCoeff_mk,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_X_mul']
  simp

/-- Helper for Chap10 Example 10 91 5: multiplying by `b` shifts scalar coefficients to
`b`-coefficients. -/
private lemma squareZeroPairBCoeff_B_mul (x : squareZeroPairRing k) :
    squareZeroPairBCoeff k (squareZeroPairRingB k * x) = squareZeroPairConstCoeff k x := by
  rcases Ideal.Quotient.mk_surjective x with ⟨p, rfl⟩
  rw [squareZeroPairRingB, ← map_mul, squareZeroPairBCoeff, squareZeroPairConstCoeff,
    squareZeroPairCoeff_mk, squareZeroPairCoeff_mk, MvPolynomial.lcoeff_apply,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_X_mul']
  simp

/-- Helper for Chap10 Example 10 91 5: the polynomial relation `aT - b`. -/
private abbrev squareZeroPairAlgebraRelation : Polynomial (squareZeroPairRing k) :=
  Polynomial.C (squareZeroPairRingA k) * Polynomial.X - Polynomial.C (squareZeroPairRingB k)

/-- Helper for Chap10 Example 10 91 5: the ideal generated by the relation `aT - b`. -/
private abbrev squareZeroPairAlgebraIdeal : Ideal (Polynomial (squareZeroPairRing k)) :=
  Ideal.span ({squareZeroPairAlgebraRelation k} : Set (Polynomial (squareZeroPairRing k)))

/-- Helper for Chap10 Example 10 91 5: coefficient extraction from polynomials over the
square-zero pair ring. -/
private def squareZeroPairPolynomialCoeff (f : squareZeroPairRing k →ₗ[k] k) (n : ℕ) :
    Polynomial (squareZeroPairRing k) →ₗ[k] k :=
  f.comp ((Polynomial.lcoeff (squareZeroPairRing k) n).restrictScalars k)

/-- Helper for Chap10 Example 10 91 5: scalar coefficient extraction from the `n`th polynomial
coefficient. -/
private def squareZeroPairPolynomialConstCoeff (n : ℕ) :
    Polynomial (squareZeroPairRing k) →ₗ[k] k :=
  squareZeroPairPolynomialCoeff k (squareZeroPairConstCoeff k) n

/-- Helper for Chap10 Example 10 91 5: the `b_n + a_{n+1}` coefficient functional on
polynomials over the square-zero pair ring. -/
private def squareZeroPairPolynomialTailCoeff (n : ℕ) :
    Polynomial (squareZeroPairRing k) →ₗ[k] k :=
  squareZeroPairPolynomialCoeff k (squareZeroPairBCoeff k) n +
    squareZeroPairPolynomialCoeff k (squareZeroPairACoeff k) (n + 1)

/-- Helper for Chap10 Example 10 91 5: scalar polynomial coefficients kill multiples of
`aT - b`. -/
private lemma squareZeroPairPolynomialConstCoeff_mul_relation (n : ℕ)
    (q : Polynomial (squareZeroPairRing k)) :
    squareZeroPairPolynomialConstCoeff k n (q * squareZeroPairAlgebraRelation k) = 0 := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [add_mul, map_add, hp, hq, add_zero]
  | monomial m c =>
      rw [squareZeroPairPolynomialConstCoeff, squareZeroPairPolynomialCoeff,
        LinearMap.comp_apply, LinearMap.restrictScalars_apply, Polynomial.lcoeff_apply]
      rw [squareZeroPairAlgebraRelation, mul_sub, Polynomial.coeff_sub, map_sub]
      rw [← mul_assoc, Polynomial.monomial_mul_C, Polynomial.monomial_mul_X,
        Polynomial.monomial_mul_C]
      by_cases hsucc : m + 1 = n
      · have hmn : ¬ m = n := by omega
        simp [Polynomial.coeff_monomial, hsucc, hmn]
        simpa [mul_comm] using squareZeroPairConstCoeff_A_mul (k := k) c
      · by_cases hmn : m = n
        · simp [Polynomial.coeff_monomial, hmn]
          simpa [mul_comm] using squareZeroPairConstCoeff_B_mul (k := k) c
        · simp [Polynomial.coeff_monomial, hsucc, hmn]

/-- Helper for Chap10 Example 10 91 5: tail polynomial coefficients kill multiples of
`aT - b`. -/
private lemma squareZeroPairPolynomialTailCoeff_mul_relation (n : ℕ)
    (q : Polynomial (squareZeroPairRing k)) :
    squareZeroPairPolynomialTailCoeff k n (q * squareZeroPairAlgebraRelation k) = 0 := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [add_mul, map_add, hp, hq, add_zero]
  | monomial m c =>
      rw [squareZeroPairPolynomialTailCoeff, LinearMap.add_apply]
      rw [squareZeroPairPolynomialCoeff, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Polynomial.lcoeff_apply]
      rw [squareZeroPairPolynomialCoeff, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Polynomial.lcoeff_apply]
      rw [squareZeroPairAlgebraRelation, mul_sub, Polynomial.coeff_sub, Polynomial.coeff_sub,
        map_sub, map_sub]
      rw [← mul_assoc, Polynomial.monomial_mul_C, Polynomial.monomial_mul_X,
        Polynomial.monomial_mul_C]
      by_cases hmn : m = n
      · subst n
        suffices -squareZeroPairBCoeff k (c * squareZeroPairRingB k) +
            squareZeroPairACoeff k (c * squareZeroPairRingA k) = 0 by
          simpa [Polynomial.coeff_monomial] using this
        have hAA :
            squareZeroPairACoeff k (c * squareZeroPairRingA k) =
              squareZeroPairConstCoeff k c := by
          simpa [mul_comm] using squareZeroPairACoeff_A_mul (k := k) c
        have hBB :
            squareZeroPairBCoeff k (c * squareZeroPairRingB k) =
              squareZeroPairConstCoeff k c := by
          simpa [mul_comm] using squareZeroPairBCoeff_B_mul (k := k) c
        rw [hAA, hBB]
        abel
      · by_cases hsucc : m + 1 = n
        · have hmn1 : ¬ m = n + 1 := by omega
          simp [Polynomial.coeff_monomial, hmn, hsucc, hmn1]
          simpa [mul_comm] using squareZeroPairBCoeff_A_mul (k := k) c
        · by_cases hprev : m = n + 1
          · have hbad : ¬ n + 1 + 1 = n := by omega
            simp [Polynomial.coeff_monomial, hprev, hbad]
            simpa [mul_comm] using squareZeroPairACoeff_B_mul (k := k) c
          · have hbad : ¬ m + 1 = n + 1 := by omega
            simp [Polynomial.coeff_monomial, hmn, hsucc, hprev]

/-- Helper for Chap10 Example 10 91 5: scalar polynomial coefficients vanish on the relation
ideal. -/
private lemma squareZeroPairPolynomialConstCoeff_relationIdeal_le_ker (n : ℕ) :
    (squareZeroPairAlgebraIdeal k).restrictScalars k ≤
      LinearMap.ker (squareZeroPairPolynomialConstCoeff k n) := by
  intro p hp
  rw [LinearMap.mem_ker]
  rcases Ideal.mem_span_singleton'.mp hp with ⟨q, hq⟩
  rw [← hq]
  exact squareZeroPairPolynomialConstCoeff_mul_relation (k := k) n q

/-- Helper for Chap10 Example 10 91 5: tail polynomial coefficients vanish on the relation
ideal. -/
private lemma squareZeroPairPolynomialTailCoeff_relationIdeal_le_ker (n : ℕ) :
    (squareZeroPairAlgebraIdeal k).restrictScalars k ≤
      LinearMap.ker (squareZeroPairPolynomialTailCoeff k n) := by
  intro p hp
  rw [LinearMap.mem_ker]
  rcases Ideal.mem_span_singleton'.mp hp with ⟨q, hq⟩
  rw [← hq]
  exact squareZeroPairPolynomialTailCoeff_mul_relation (k := k) n q

/-- Helper for Chap10 Example 10 91 5: the scalar coefficient functional on the quotient
algebra. -/
private def squareZeroPairAlgebraCoeff (n : ℕ) : squareZeroPairAlgebra k →ₗ[k] k :=
  Submodule.liftQ ((squareZeroPairAlgebraIdeal k).restrictScalars k)
    (squareZeroPairPolynomialConstCoeff k n)
    (squareZeroPairPolynomialConstCoeff_relationIdeal_le_ker (k := k) n)

/-- Helper for Chap10 Example 10 91 5: the tail coefficient functional on the quotient algebra. -/
private def squareZeroPairAlgebraTailCoeff (n : ℕ) : squareZeroPairAlgebra k →ₗ[k] k :=
  Submodule.liftQ ((squareZeroPairAlgebraIdeal k).restrictScalars k)
    (squareZeroPairPolynomialTailCoeff k n)
    (squareZeroPairPolynomialTailCoeff_relationIdeal_le_ker (k := k) n)

/-- Helper for Chap10 Example 10 91 5: quotient algebra scalar coefficients evaluate on
representatives. -/
private lemma squareZeroPairAlgebraCoeff_mk (n : ℕ) (p : Polynomial (squareZeroPairRing k)) :
    squareZeroPairAlgebraCoeff k n (Ideal.Quotient.mk (squareZeroPairAlgebraIdeal k) p) =
      squareZeroPairPolynomialConstCoeff k n p := by
  change squareZeroPairAlgebraCoeff k n
      (Submodule.Quotient.mk (p := (squareZeroPairAlgebraIdeal k).restrictScalars k) p) =
    squareZeroPairPolynomialConstCoeff k n p
  exact Submodule.liftQ_apply ((squareZeroPairAlgebraIdeal k).restrictScalars k)
    (squareZeroPairPolynomialConstCoeff k n) p

/-- Helper for Chap10 Example 10 91 5: quotient algebra tail coefficients evaluate on
representatives. -/
private lemma squareZeroPairAlgebraTailCoeff_mk (n : ℕ) (p : Polynomial (squareZeroPairRing k)) :
    squareZeroPairAlgebraTailCoeff k n (Ideal.Quotient.mk (squareZeroPairAlgebraIdeal k) p) =
      squareZeroPairPolynomialTailCoeff k n p := by
  change squareZeroPairAlgebraTailCoeff k n
      (Submodule.Quotient.mk (p := (squareZeroPairAlgebraIdeal k).restrictScalars k) p) =
    squareZeroPairPolynomialTailCoeff k n p
  exact Submodule.liftQ_apply ((squareZeroPairAlgebraIdeal k).restrictScalars k)
    (squareZeroPairPolynomialTailCoeff k n) p

/-- Helper for Chap10 Example 10 91 5: the coefficient of `T^m` in `T^n` is the Kronecker
delta. -/
private lemma squareZeroPairAlgebraCoeff_mk_X_pow (n m : ℕ) :
    squareZeroPairAlgebraCoeff k n
        (Ideal.Quotient.mk (squareZeroPairAlgebraIdeal k)
          ((Polynomial.X : Polynomial (squareZeroPairRing k)) ^ m)) =
      if m = n then 1 else 0 := by
  rw [squareZeroPairAlgebraCoeff_mk, squareZeroPairPolynomialConstCoeff,
    squareZeroPairPolynomialCoeff, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Polynomial.lcoeff_apply]
  by_cases h : m = n
  · simp [h, squareZeroPairConstCoeff_one]
  · simp [Polynomial.coeff_X_pow, h, Ne.symm h]

/-- Helper for Chap10 Example 10 91 5: scalar coefficients are semilinear for the action of the
square-zero pair ring. -/
private lemma squareZeroPairAlgebraCoeff_smul (n : ℕ) (r : squareZeroPairRing k)
    (x : squareZeroPairAlgebra k) :
    squareZeroPairAlgebraCoeff k n (r • x) =
      squareZeroPairConstCoeff k r * squareZeroPairAlgebraCoeff k n x := by
  rcases Ideal.Quotient.mk_surjective x with ⟨p, rfl⟩
  rw [Algebra.smul_def]
  rw [← Ideal.Quotient.mk_algebraMap (R₁ := squareZeroPairRing k)
    (A := Polynomial (squareZeroPairRing k)) (squareZeroPairAlgebraIdeal k) r]
  rw [Polynomial.algebraMap_eq, ← map_mul, squareZeroPairAlgebraCoeff_mk,
    squareZeroPairAlgebraCoeff_mk, squareZeroPairPolynomialConstCoeff,
    squareZeroPairPolynomialCoeff, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Polynomial.lcoeff_apply]
  rw [Polynomial.coeff_C_mul, squareZeroPairConstCoeff_mul]
  rfl

/-- Helper for Chap10 Example 10 91 5: the tail coefficient of `b • x` is the scalar coefficient
of `x`. -/
private lemma squareZeroPairAlgebraTailCoeff_B_smul (n : ℕ) (x : squareZeroPairAlgebra k) :
    squareZeroPairAlgebraTailCoeff k n (squareZeroPairRingB k • x) =
      squareZeroPairAlgebraCoeff k n x := by
  rcases Ideal.Quotient.mk_surjective x with ⟨p, rfl⟩
  rw [Algebra.smul_def]
  rw [← Ideal.Quotient.mk_algebraMap (R₁ := squareZeroPairRing k)
    (A := Polynomial (squareZeroPairRing k)) (squareZeroPairAlgebraIdeal k)
    (squareZeroPairRingB k)]
  rw [Polynomial.algebraMap_eq, ← map_mul, squareZeroPairAlgebraTailCoeff_mk,
    squareZeroPairAlgebraCoeff_mk, squareZeroPairPolynomialTailCoeff, LinearMap.add_apply,
    squareZeroPairPolynomialCoeff, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Polynomial.lcoeff_apply, squareZeroPairPolynomialCoeff, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Polynomial.lcoeff_apply, squareZeroPairPolynomialConstCoeff,
    squareZeroPairPolynomialCoeff, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Polynomial.lcoeff_apply]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, squareZeroPairBCoeff_B_mul,
    squareZeroPairACoeff_B_mul]
  simp

/-- Helper for Chap10 Example 10 91 5: the tail coefficient of `a • x` is the next scalar
coefficient of `x`. -/
private lemma squareZeroPairAlgebraTailCoeff_A_smul (n : ℕ) (x : squareZeroPairAlgebra k) :
    squareZeroPairAlgebraTailCoeff k n (squareZeroPairRingA k • x) =
      squareZeroPairAlgebraCoeff k (n + 1) x := by
  rcases Ideal.Quotient.mk_surjective x with ⟨p, rfl⟩
  rw [Algebra.smul_def]
  rw [← Ideal.Quotient.mk_algebraMap (R₁ := squareZeroPairRing k)
    (A := Polynomial (squareZeroPairRing k)) (squareZeroPairAlgebraIdeal k)
    (squareZeroPairRingA k)]
  rw [Polynomial.algebraMap_eq, ← map_mul, squareZeroPairAlgebraTailCoeff_mk,
    squareZeroPairAlgebraCoeff_mk, squareZeroPairPolynomialTailCoeff, LinearMap.add_apply,
    squareZeroPairPolynomialCoeff, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Polynomial.lcoeff_apply, squareZeroPairPolynomialCoeff, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Polynomial.lcoeff_apply, squareZeroPairPolynomialConstCoeff,
    squareZeroPairPolynomialCoeff, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Polynomial.lcoeff_apply]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, squareZeroPairBCoeff_A_mul,
    squareZeroPairACoeff_A_mul]
  simp

/-- Helper for Chap10 Example 10 91 5: every element of the quotient algebra has bounded scalar
polynomial support. -/
private lemma squareZeroPairAlgebraCoeff_eventually_zero (x : squareZeroPairAlgebra k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      squareZeroPairAlgebraCoeff k n x = 0 := by
  rcases Ideal.Quotient.mk_surjective x with ⟨p, hp⟩
  refine ⟨p.natDegree + 1, ?_⟩
  intro n hn
  rw [← hp, squareZeroPairAlgebraCoeff_mk, squareZeroPairPolynomialConstCoeff,
    squareZeroPairPolynomialCoeff, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Polynomial.lcoeff_apply]
  have hpcoeff : p.coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hpcoeff, map_zero]

/-- Helper for Chap10 Example 10 91 5: scalar coefficient vanishing on finite generators extends
to their generated submodule. -/
private lemma squareZeroPairAlgebraCoeff_eq_zero_of_mem_span
    (A : Submodule (squareZeroPairRing k) (squareZeroPairAlgebra k))
    (s : Finset A) {n : ℕ}
    (hzero : ∀ x ∈ s,
      squareZeroPairAlgebraCoeff k n ((x : A) : squareZeroPairAlgebra k) = 0)
    {x : A} (hx : x ∈ Submodule.span (squareZeroPairRing k) (s : Set A)) :
    squareZeroPairAlgebraCoeff k n ((x : A) : squareZeroPairAlgebra k) = 0 := by
  refine Submodule.span_induction
    (p := fun x : A => fun _ =>
      squareZeroPairAlgebraCoeff k n ((x : A) : squareZeroPairAlgebra k) = 0)
    ?_ ?_ ?_ ?_ hx
  · intro x hx
    exact hzero x hx
  · simpa using (squareZeroPairAlgebraCoeff k n).map_zero
  · intro x y _ _ hx hy
    change squareZeroPairAlgebraCoeff k n
        ((x : squareZeroPairAlgebra k) + (y : squareZeroPairAlgebra k)) = 0
    rw [map_add, hx, hy, add_zero]
  · intro r x _ hx
    change squareZeroPairAlgebraCoeff k n (r • (x : squareZeroPairAlgebra k)) = 0
    rw [squareZeroPairAlgebraCoeff_smul, hx, mul_zero]

/-- Helper for Chap10 Example 10 91 5: finite submodules of the square-zero algebra have bounded
scalar polynomial support. -/
private lemma squareZeroPairAlgebraCoeff_bounded_of_finite
    (A : Submodule (squareZeroPairRing k) (squareZeroPairAlgebra k))
    [Module.Finite (squareZeroPairRing k) A] :
    ∃ N : ℕ, ∀ x : A, ∀ n : ℕ, N ≤ n →
      squareZeroPairAlgebraCoeff k n (x : squareZeroPairAlgebra k) = 0 := by
  classical
  have hfg : (⊤ : Submodule (squareZeroPairRing k) A).FG := Module.Finite.fg_top
  rcases hfg with ⟨s, hs⟩
  have hbound : ∀ x : A, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      squareZeroPairAlgebraCoeff k n (x : squareZeroPairAlgebra k) = 0 := by
    intro x
    exact squareZeroPairAlgebraCoeff_eventually_zero (k := k) (x : squareZeroPairAlgebra k)
  choose bound hbound using hbound
  refine ⟨s.sup bound, ?_⟩
  intro x n hn
  have hxmem : x ∈ Submodule.span (squareZeroPairRing k) (s : Set A) := by
    rw [hs]
    trivial
  exact squareZeroPairAlgebraCoeff_eq_zero_of_mem_span (k := k) (A := A) (s := s)
    (fun y hy => hbound y n (le_trans (Finset.le_sup (f := bound) hy) hn)) hxmem

/-- Helper for Chap10 Example 10 91 5: the quotient relation rewrites `bT^n - aT^(n+1)` as
the negative of `T^n(aT-b)`. -/
private lemma squareZeroPairPolynomial_relation_pow_identity (n : ℕ) :
    algebraMap (squareZeroPairRing k) (Polynomial (squareZeroPairRing k))
        (squareZeroPairRingB k) *
        (Polynomial.X : Polynomial (squareZeroPairRing k)) ^ n -
      algebraMap (squareZeroPairRing k) (Polynomial (squareZeroPairRing k))
        (squareZeroPairRingA k) *
        (Polynomial.X : Polynomial (squareZeroPairRing k)) ^ (n + 1) =
      -((Polynomial.X : Polynomial (squareZeroPairRing k)) ^ n *
        squareZeroPairAlgebraRelation k) := by
  simp only [Polynomial.algebraMap_eq]
  ring_nf

/-- Helper for Chap10 Example 10 91 5: the defining relation identifies `bT^n` with
`aT^(n+1)` in the quotient algebra. -/
private lemma squareZeroPairAlgebra_B_smul_T_pow_eq_A_smul_T_pow_succ (n : ℕ) :
    squareZeroPairRingB k •
        Ideal.Quotient.mk (squareZeroPairAlgebraIdeal k)
          ((Polynomial.X : Polynomial (squareZeroPairRing k)) ^ n) =
      squareZeroPairRingA k •
        Ideal.Quotient.mk (squareZeroPairAlgebraIdeal k)
          ((Polynomial.X : Polynomial (squareZeroPairRing k)) ^ (n + 1)) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rw [← Ideal.Quotient.mk_algebraMap (R₁ := squareZeroPairRing k)
    (A := Polynomial (squareZeroPairRing k)) (squareZeroPairAlgebraIdeal k)
    (squareZeroPairRingB k)]
  rw [← Ideal.Quotient.mk_algebraMap (R₁ := squareZeroPairRing k)
    (A := Polynomial (squareZeroPairRing k)) (squareZeroPairAlgebraIdeal k)
    (squareZeroPairRingA k)]
  rw [← map_mul, ← map_mul]
  rw [Ideal.Quotient.eq]
  have hrelmem : (Polynomial.X : Polynomial (squareZeroPairRing k)) ^ n *
      squareZeroPairAlgebraRelation k ∈ squareZeroPairAlgebraIdeal k := by
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  have hmem : -((Polynomial.X : Polynomial (squareZeroPairRing k)) ^ n *
      squareZeroPairAlgebraRelation k) ∈ squareZeroPairAlgebraIdeal k :=
    (squareZeroPairAlgebraIdeal k).neg_mem hrelmem
  rwa [squareZeroPairPolynomial_relation_pow_identity]

/-- Chap10 Example 10 91 5: the square-zero algebra is not a direct sum of finitely
presented submodules over the square-zero pair ring. -/
lemma squareZeroPairAlgebra_not_isDirectSumOfFinitePresentation :
    ¬ IsDirectSumOfFinitePresentation.{u, u, 0}
      (squareZeroPairRing k) (squareZeroPairAlgebra k) := by
  classical
  intro hsum
  rcases hsum with ⟨ι, A, hindep, htop, hfp⟩
  let tPow : ℕ → squareZeroPairAlgebra k := fun n =>
    Ideal.Quotient.mk (squareZeroPairAlgebraIdeal k)
      ((Polynomial.X : Polynomial (squareZeroPairRing k)) ^ n)
  let e := hindep.linearEquiv htop
  let z : ℕ → DFinsupp (fun i : ι => A i) := fun n => e.symm (tPow n)
  letI : (i : ι) → Zero (A i) := fun i => Submodule.zero (A i)
  letI : (i : ι) → SMulZeroClass (squareZeroPairRing k) (A i) := fun i =>
    { smul := fun r x => ⟨r • (x : squareZeroPairAlgebra k), (A i).smul_mem r x.2⟩
      smul_zero := by
        intro r
        ext
        change r • (0 : squareZeroPairAlgebra k) = 0
        rw [Algebra.smul_def, mul_zero] }
  have hzrel : ∀ n : ℕ,
      squareZeroPairRingB k • (z n) = squareZeroPairRingA k • (z (n + 1)) := by
    intro n
    calc
      squareZeroPairRingB k • (z n) =
          e.symm (squareZeroPairRingB k • (tPow n)) := by
            exact (e.symm.map_smul (squareZeroPairRingB k) (tPow n)).symm
      _ = e.symm (squareZeroPairRingA k • (tPow (n + 1))) := by
            exact congrArg e.symm
              (squareZeroPairAlgebra_B_smul_T_pow_eq_A_smul_T_pow_succ (k := k) n)
      _ = squareZeroPairRingA k • (z (n + 1)) := by
            exact e.symm.map_smul (squareZeroPairRingA k) (tPow (n + 1))
  have hstep : ∀ (i : ι) (n : ℕ),
      squareZeroPairAlgebraCoeff k n ((z n i : A i) : squareZeroPairAlgebra k) =
        squareZeroPairAlgebraCoeff k (n + 1)
          ((z (n + 1) i : A i) : squareZeroPairAlgebra k) := by
    intro i n
    have hcoord := congrArg
      (fun y : DFinsupp (fun i : ι => A i) =>
        ((y i : A i) : squareZeroPairAlgebra k)) (hzrel n)
    have htail := congrArg (squareZeroPairAlgebraTailCoeff k n) hcoord
    simpa [squareZeroPairAlgebraTailCoeff_B_smul,
      squareZeroPairAlgebraTailCoeff_A_smul] using htail
  have hzero_on_support : ∀ i ∈ (z 0).support,
      squareZeroPairAlgebraCoeff k 0 ((z 0 i : A i) : squareZeroPairAlgebra k) = 0 := by
    intro i hi
    letI : Module.FinitePresentation (squareZeroPairRing k) (A i) := hfp i
    obtain ⟨N, hN⟩ := squareZeroPairAlgebraCoeff_bounded_of_finite (k := k) (A := A i)
    have hconst : ∀ n : ℕ,
        squareZeroPairAlgebraCoeff k 0 ((z 0 i : A i) : squareZeroPairAlgebra k) =
          squareZeroPairAlgebraCoeff k n ((z n i : A i) : squareZeroPairAlgebra k) := by
      intro n
      induction n with
      | zero =>
          rfl
      | succ n ih =>
          exact ih.trans (hstep i n)
    exact (hconst N).trans (hN (z N i) N le_rfl)
  have hcoeff_sum :
      squareZeroPairAlgebraCoeff k 0 (e (z 0)) =
        (z 0).sum fun i xi =>
          squareZeroPairAlgebraCoeff k 0 ((xi : A i) : squareZeroPairAlgebra k) := by
    rw [iSupIndep.linearEquiv_apply]
    simp [DFinsupp.sumAddHom_apply]
  have hsum_zero :
      ((z 0).sum fun i xi =>
        squareZeroPairAlgebraCoeff k 0 ((xi : A i) : squareZeroPairAlgebra k)) = 0 := by
    apply DFinsupp.sum_eq_zero
    intro i
    by_cases hi : i ∈ (z 0).support
    · exact hzero_on_support i hi
    · have hzi : z 0 i = 0 := (DFinsupp.notMem_support_iff.mp hi)
      rw [hzi]
      exact (squareZeroPairAlgebraCoeff k 0).map_zero
  have hmain := congrArg (squareZeroPairAlgebraCoeff k 0) (e.apply_symm_apply (tPow 0))
  rw [hcoeff_sum, hsum_zero, squareZeroPairAlgebraCoeff_mk_X_pow] at hmain
  exact zero_ne_one hmain

-- Proof sketch: the ring `squareZeroPairRing k` is Artinian local and hence henselian. If
-- `squareZeroPairAlgebra k` were Mittag-Leffler, Lemma `10.153.13` would split it as a direct sum
-- of finitely presented modules. The textbook notes that this module is indecomposable, so such a
-- decomposition is impossible.
/-- The algebra `R[t] / (at - b)` is not Mittag-Leffler as an `R`-module for
`R = k[a, b] / (a^2, ab, b^2)`. -/
theorem squareZeroPairAlgebra_not_mittagLeffler :
    ¬ MittagLeffler (squareZeroPairRing k) (squareZeroPairAlgebra k) := by
  intro hML
  -- Lemma 10.153.13 converts countable generation and Mittag-Lefflerness over the henselian local
  -- base into a finite-presentation direct-sum decomposition.
  letI : HenselianLocalRing (squareZeroPairRing k) := squareZeroPairRing_henselianLocalRing k
  have hsum :
      IsDirectSumOfFinitePresentation.{u, u, 0}
        (squareZeroPairRing k) (squareZeroPairAlgebra k) :=
    isDirectSumOfFinitePresentation_of_henselianLocalRing_of_countablyGenerated_of_mittagLeffler
      (squareZeroPairRing k) (squareZeroPairAlgebra k)
      (squareZeroPairAlgebra_countablyGenerated k) hML
  -- The source-facing obstruction rules out exactly that decomposition.
  exact squareZeroPairAlgebra_not_isDirectSumOfFinitePresentation k hsum

end

end Module
