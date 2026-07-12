import Mathlib
import DifferentialForms_Cartan_1970.III.section11.frozen_0003_Theorem_III_5_extra_2
import DifferentialForms_Cartan_1970.III.section11.«0010_Definition_III_5_extra_7»
import DifferentialForms_Cartan_1970.III.section11.«frozen_0011_Proposition_5_1»
import DifferentialForms_Cartan_1970.III.section11.«0007_Remark_III_5_extra_6»

open Filter
open scoped BigOperators Topology
open MeromorphicOn

noncomputable section

variable {f : ℂ → ℂ} (L : PeriodPair) (P : Set ℂ)

/-- Helper for Proposition 5.2: subtracting a constant preserves the meromorphic order at a
genuine pole. -/
lemma meromorphicOrderAt_sub_const_eq_of_lt_zero
    {f : ℂ → ℂ} {a z : ℂ}
    (hz : meromorphicOrderAt f z < 0) :
    meromorphicOrderAt (fun w ↦ f w - a) z = meromorphicOrderAt f z := by
  have hconst_nonneg : 0 ≤ meromorphicOrderAt (fun _ ↦ (-a : ℂ)) z := by
    by_cases ha : a = 0
    · simp [meromorphicOrderAt_const, ha]
    · have hne : (-a : ℂ) ≠ 0 := by simpa using ha
      simp [meromorphicOrderAt_const, hne]
  have hlt_const : meromorphicOrderAt f z < meromorphicOrderAt (fun _ ↦ (-a : ℂ)) z :=
    lt_of_lt_of_le hz hconst_nonneg
  simpa [sub_eq_add_neg] using
    (meromorphicOrderAt_add_eq_left_of_lt
      (f₁ := f) (f₂ := fun _ ↦ (-a : ℂ)) (x := z)
      (MeromorphicAt.const (-a) z) hlt_const)

/-- Helper for Proposition 5.2: subtracting a constant preserves the period lattice. -/
lemma hasPeriodLattice_sub_const
    {f : ℂ → ℂ} {a : ℂ}
    (hperiods : HasPeriodLattice L f) :
    HasPeriodLattice L (fun w ↦ f w - a) := by
  intro ω hω z
  simpa using congrArg (fun x : ℂ ↦ x - a) (hperiods ω hω z)

/-- Helper for Proposition 5.2: subtracting a constant does not change the chosen pole
representatives on `P`. -/
lemma isPoleRepresentativeSet_sub_const
    {f : ℂ → ℂ} {a : ℂ} {poles : Finset ℂ}
    (hf : Meromorphic f)
    (hpoles : IsPoleRepresentativeSet f P poles) :
    IsPoleRepresentativeSet (fun w ↦ f w - a) P poles := by
  have hsub_meromorphic : MeromorphicOn (fun w ↦ f w - a) P := by
    simpa using hf.meromorphicOn.sub
      ((analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ a) P).meromorphicOn)
  intro z
  rw [hpoles.mem_iff z]
  constructor
  · rintro ⟨hzP, hzneg⟩
    have horder_neg : meromorphicOrderAt f z < 0 := by
      exact lt_of_not_ge (by simpa using not_le_of_gt (show (meromorphicOrderAt f z).untop₀ < 0 by
        simpa [hf.meromorphicOn.divisor_apply hzP] using hzneg))
    have horder_eq :
        meromorphicOrderAt (fun w ↦ f w - a) z = meromorphicOrderAt f z :=
      meromorphicOrderAt_sub_const_eq_of_lt_zero (a := a) horder_neg
    refine ⟨hzP, ?_⟩
    simpa [hsub_meromorphic.divisor_apply hzP, hf.meromorphicOn.divisor_apply hzP, horder_eq] using
      hzneg
  · rintro ⟨hzP, hzneg⟩
    have horder_neg : meromorphicOrderAt (fun w ↦ f w - a) z < 0 := by
      exact lt_of_not_ge (by
        simpa using not_le_of_gt (show (meromorphicOrderAt (fun w ↦ f w - a) z).untop₀ < 0 by
          simpa [hsub_meromorphic.divisor_apply hzP] using hzneg))
    have horder_eq :
        meromorphicOrderAt f z = meromorphicOrderAt (fun w ↦ f w - a) z := by
      simpa using
        (meromorphicOrderAt_sub_const_eq_of_lt_zero
          (f := fun w ↦ f w - a) (a := -a) horder_neg)
    refine ⟨hzP, ?_⟩
    simpa [hf.meromorphicOn.divisor_apply hzP, hsub_meromorphic.divisor_apply hzP, horder_eq] using
      hzneg

/-- Helper for Proposition 5.2: subtracting a constant does not change the divisor value at a
genuine pole inside the chosen representative set. -/
lemma divisor_sub_const_eq_of_divisor_lt_zero
    {f : ℂ → ℂ} {a z : ℂ}
    (hf : Meromorphic f)
    (hzP : z ∈ P)
    (hzneg : divisor f P z < 0) :
    divisor (fun w ↦ f w - a) P z = divisor f P z := by
  have hsub_meromorphic : MeromorphicOn (fun w ↦ f w - a) P := by
    simpa using hf.meromorphicOn.sub
      ((analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ ↦ a) P).meromorphicOn)
  have horder_neg : meromorphicOrderAt f z < 0 := by
    exact lt_of_not_ge (by
      simpa [hf.meromorphicOn.divisor_apply hzP] using not_le_of_gt (show
        (meromorphicOrderAt f z).untop₀ < 0 by
          simpa [hf.meromorphicOn.divisor_apply hzP] using hzneg))
  have horder_eq :
      meromorphicOrderAt (fun w ↦ f w - a) z = meromorphicOrderAt f z :=
    meromorphicOrderAt_sub_const_eq_of_lt_zero (a := a) horder_neg
  simp [hsub_meromorphic.divisor_apply hzP, hf.meromorphicOn.divisor_apply hzP, horder_eq]
