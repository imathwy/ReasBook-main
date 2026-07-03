import Mathlib
import StacksProject_2024.Chap10.Lemma_10_24_1

-- Declarations for this item will be appended below by the statement pipeline.

open LinearMap

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {ι : Type w}
variable (M : Type v) [AddCommGroup M] [Module R M] [Finite ι] (f : ι → R)

-- Proof sketch: if the canonical map to the family of away localizations is injective and every
-- component of the product linear map `pi fun i ↦ DistribSMul.toLinearMap R M (f i)` vanishes on
-- `m`, then the image of `m` in each `M_{f_i}` is zero, so `m = 0`. Conversely, if this product
-- linear map is injective and the image of `m` in each `M_{f_i}` vanishes, then some power of
-- each `f i` kills `m`; use induction on the finite sum of these exponents to reduce to the case
-- where every exponent is `1`.
/-- Helper for Lemma 10.24.4: vanishing in every away localization is equivalent to saying that
for each index `i`, some positive power of `f i` annihilates the source element. -/
lemma away_localization_family_map_eq_zero_iff {m : M} :
    awayLocalizationFamilyMap M f m = 0 ↔
      ∀ i, ∃ e : ℕ, 0 < e ∧ (f i) ^ e • m = 0 := by
  constructor
  · intro hm i
    -- Read the family-map equation componentwise and unpack the localization kernel criterion.
    have hi :
        LocalizedModule.mkLinearMap (.powers (f i)) M m = 0 := by
      simpa [awayLocalizationFamilyMap] using congrFun hm i
    rw [← LinearMap.mem_ker, LocalizedModule.mem_ker_mkLinearMap_iff] at hi
    rcases hi with ⟨r, hr, hrs⟩
    rcases (Submonoid.mem_powers_iff r (f i)).mp hr with ⟨n, rfl⟩
    cases n with
    | zero =>
        use 1
        constructor
        · simp
        · have hm_zero : m = 0 := by
            simpa using hrs
          simpa [hm_zero]
    | succ n =>
        use n + 1
        constructor
        · omega
        · simpa
  · intro hm
    -- Each positive-power annihilation witnesses that the corresponding localization component is
    -- in the kernel of the canonical map.
    ext i
    rcases hm i with ⟨e, hepos, hs⟩
    have hi :
        LocalizedModule.mkLinearMap (.powers (f i)) M m = 0 := by
      rw [← LinearMap.mem_ker, LocalizedModule.mem_ker_mkLinearMap_iff]
      exact ⟨(f i) ^ e, ⟨e, rfl⟩, hs⟩
    simpa [awayLocalizationFamilyMap] using hi

/-- Helper for Lemma 10.24.4: an element killed by each `f i` already maps to zero in every away
localization. -/
lemma away_localization_family_map_zero_of_mem_torsionBySet {m : M}
    (hm : m ∈ Submodule.torsionBySet R M (Set.range f)) :
    awayLocalizationFamilyMap M f m = 0 := by
  -- Route correction: use the new localization-zero bridge so the forward implication is a single
  -- torsion-by-set calculation.
  rw [away_localization_family_map_eq_zero_iff (M := M) (f := f)]
  intro i
  use 1
  constructor
  · simp
  · -- Membership in `torsionBySet` says every generator `f i` kills `m`.
    rw [Submodule.mem_torsionBySet_iff] at hm
    simpa using hm ⟨f i, Set.mem_range_self i⟩

/-- Helper for Lemma 10.24.4: if positive powers of all `f i` annihilate `m`, then `m = 0`
whenever the common `f i`-torsion submodule is trivial. -/
lemma eq_zero_of_forall_pos_pow_smul_eq_zero {m : M} {e : ι → ℕ}
    (hepos : ∀ i, 0 < e i)
    (hpow : ∀ i, (f i) ^ e i • m = 0)
    (hbot : Submodule.torsionBySet R M (Set.range f) = ⊥) :
    m = 0 := by
  classical
  letI := Fintype.ofFinite ι
  -- Follow the source proof: induct on the total sum of the positive exponents.
  have hP :
      ∀ n : ℕ, ∀ (m : M) (e : ι → ℕ), (∑ i, e i) = n →
        (∀ i, 0 < e i) →
        (∀ i, (f i) ^ e i • m = 0) →
        m = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih m e hsum hepos hpow
    by_cases hones : ∀ i, e i = 1
    · -- Base case: all exponents are `1`, so `m` lies in the torsion-by-set submodule.
      have hm_torsion : m ∈ Submodule.torsionBySet R M (Set.range f) := by
        rw [Submodule.mem_torsionBySet_iff]
        rintro ⟨a, ha⟩
        rcases ha with ⟨i, rfl⟩
        simpa [hones i] using hpow i
      have hm_bot : m ∈ (⊥ : Submodule R M) := by
        simpa [hbot] using hm_torsion
      simpa using hm_bot
    · push Not at hones
      rcases hones with ⟨i, hi_ne⟩
      have hi_gt : 1 < e i := by
        exact lt_of_le_of_ne (Nat.succ_le_of_lt (hepos i)) (by simpa using hi_ne.symm)
      let ePred : ι → ℕ := Function.update e i (e i - 1)
      have heposPred : ∀ j, 0 < ePred j := by
        intro j
        by_cases hj : j = i
        · subst hj
          simp [ePred, hi_gt]
        · simp [ePred, hj, hepos j]
      have hpowPred : ∀ j, (f j) ^ ePred j • (f i • m) = 0 := by
        intro j
        by_cases hj : j = i
        · subst hj
          -- Repackage the `i`-th annihilation as one lower exponent on `f i • m`.
          calc
            (f j) ^ ePred j • (f j • m)
                = (f j) ^ (e j - 1) • (f j • m) := by simp [ePred]
            _ = ((f j) ^ (e j - 1) * f j) • m := by rw [smul_smul]
            _ = (f j) ^ e j • m := by
                  rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt (hepos j))]
            _ = 0 := hpow j
        · -- Away from `i`, the same exponent still annihilates after multiplying by `f i`.
          calc
            (f j) ^ ePred j • (f i • m)
                = (f j) ^ e j • (f i • m) := by simp [ePred, hj]
            _ = ((f j) ^ e j * f i) • m := by rw [smul_smul]
            _ = (f i * (f j) ^ e j) • m := by rw [mul_comm]
            _ = f i • ((f j) ^ e j • m) := by rw [smul_smul]
            _ = 0 := by rw [hpow j, smul_zero]
      have hsumPred_lt : ∑ j, ePred j < n := by
        rw [← hsum]
        rw [Finset.sum_update_of_mem (s := Finset.univ) (i := i) (by simp) e (e i - 1)]
        rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (s := Finset.univ) (i := i) (by simp) e]
        omega
      have hfi_zero : f i • m = 0 := by
        exact ih (∑ j, ePred j) hsumPred_lt (f i • m) ePred rfl heposPred hpowPred
      let eOne : ι → ℕ := Function.update e i 1
      have heposOne : ∀ j, 0 < eOne j := by
        intro j
        by_cases hj : j = i
        · subst hj
          simp [eOne]
        · simp [eOne, hj, hepos j]
      have hpowOne : ∀ j, (f j) ^ eOne j • m = 0 := by
        intro j
        by_cases hj : j = i
        · subst hj
          simpa [eOne] using hfi_zero
        · simpa [eOne, hj] using hpow j
      have hsumOne_lt : ∑ j, eOne j < n := by
        rw [← hsum]
        rw [Finset.sum_update_of_mem (s := Finset.univ) (i := i) (by simp) e 1]
        rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (s := Finset.univ) (i := i) (by simp) e]
        omega
      exact ih (∑ j, eOne j) hsumOne_lt m eOne rfl heposOne hpowOne
  exact hP (∑ i, e i) m e rfl hepos hpow

/-- Bridge the injectivity of the canonical map to the family of away localizations with the
vanishing of the torsion submodule cut out by the generating set `Set.range f`. -/
theorem away_localization_family_map_injective_iff_torsionBySet_eq_bot :
    Function.Injective (awayLocalizationFamilyMap M f) ↔
      Submodule.torsionBySet R M (Set.range f) = ⊥ := by
  rw [← LinearMap.ker_eq_bot]
  constructor
  · intro hker
    -- The forward implication sends torsion elements to zero in every localization component.
    rw [Submodule.eq_bot_iff]
    intro m hm
    have hm_zero :
        awayLocalizationFamilyMap M f m = 0 :=
      away_localization_family_map_zero_of_mem_torsionBySet (M := M) (f := f) hm
    have hm_ker : m ∈ LinearMap.ker (awayLocalizationFamilyMap M f) := by
      rw [LinearMap.mem_ker]
      exact hm_zero
    have hm_bot : m ∈ (⊥ : Submodule R M) := by
      simpa [hker] using hm_ker
    simpa using hm_bot
  · intro hbot
    -- The reverse implication extracts positive exponents from localization vanishing and then
    -- runs the source-proof induction on their total sum.
    rw [Submodule.eq_bot_iff]
    intro m hm
    rw [LinearMap.mem_ker] at hm
    rw [away_localization_family_map_eq_zero_iff (M := M) (f := f)] at hm
    choose e hepos hpow using hm
    exact eq_zero_of_forall_pos_pow_smul_eq_zero (M := M) (f := f)
      (m := m) (e := e) hepos hpow
      hbot

/-- Lemma 10.24.4: for a finite family `f : ι → R`, the canonical map from `M` to the family of
away localizations `M_{f_i}` is injective if and only if the product linear map with components
`m ↦ f_i • m` is injective. The Stacks Project writes the targets as finite direct sums; in Lean
we use the canonically equivalent finite products `∀ i, LocalizedModule.Away (f i) M` and
`∀ i, M`. -/
theorem away_localization_family_map_injective_iff_smul_family_map_injective :
    Function.Injective (awayLocalizationFamilyMap M f) ↔
      Function.Injective (LinearMap.pi fun i ↦ DistribSMul.toLinearMap R M (f i)) := by
  have hker :
      LinearMap.ker (LinearMap.pi fun i ↦ DistribSMul.toLinearMap R M (f i)) =
        Submodule.torsionBySet R M (Set.range f) := by
    ext m
    rw [LinearMap.ker_pi, Submodule.mem_iInf, Submodule.mem_torsionBySet_iff]
    constructor
    · intro hm ⟨a, ha⟩
      rcases ha with ⟨i, rfl⟩
      simpa [LinearMap.mem_ker] using hm i
    · intro hm i
      simpa [LinearMap.mem_ker] using hm ⟨f i, Set.mem_range_self i⟩
  have hsmul :
      Function.Injective (LinearMap.pi fun i ↦ DistribSMul.toLinearMap R M (f i)) ↔
        Submodule.torsionBySet R M (Set.range f) = ⊥ := by
    rw [← LinearMap.ker_eq_bot, hker]
  exact (away_localization_family_map_injective_iff_torsionBySet_eq_bot M f).trans hsmul.symm

end
