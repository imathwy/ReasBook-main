import StacksProject_2024.stacks_project.Chap15.Definition_15_124_1

open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [ValuationRing A]
variable [CommRing B] [IsDomain B] [ValuationRing B]
variable [Algebra A B] [h : IsExtensionOfValuationRings A B]

/-- Helper for Lemma 15.116.11: in a finite family of elements of a valuation ring, one element
divides all the others. -/
lemma exists_mem_finset_dvd_all {ι : Type*} (s : Finset ι) (f : ι → A)
    (hs : s.Nonempty) :
    ∃ j ∈ s, ∀ i ∈ s, f j ∣ f i := by
  classical
  refine Finset.induction_on s ?_ ?_ hs
  · intro hs0
    simpa using hs0
  · intro a s ha hsind hsas
    by_cases hs' : s.Nonempty
    · rcases hsind hs' with ⟨j, hj, hdiv⟩
      have htotal : Std.Total (fun I J : Ideal A ↦ I ≤ J) :=
        ValuationRing.iff_ideal_total.mp inferInstance
      rcases htotal.total (Ideal.span ({f a} : Set A)) (Ideal.span ({f j} : Set A)) with
          hle | hle
      · refine ⟨j, Finset.mem_insert_of_mem hj, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact Ideal.span_singleton_le_span_singleton.mp hle
        · exact hdiv i hi'
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact dvd_rfl
        · exact dvd_trans (Ideal.span_singleton_le_span_singleton.mp hle) (hdiv i hi')
    · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst hs_empty
      refine ⟨a, by simp, ?_⟩
      intro i hi
      have hi' : i = a := by simpa using hi
      subst hi'
      exact dvd_rfl

/-- Helper for Lemma 15.116.11: residue-field linear independence of lifts already implies
`A`-linear independence in `B`. -/
lemma residue_lifts_linearIndependent_over_base
    {ι : Type*} (u : ι → B)
    (hu : LinearIndependent (ResidueField A) (fun i ↦ IsLocalRing.residue B (u i))) :
    LinearIndependent A u := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  by_cases hl0 : l = 0
  · exact hl0
  have hs : l.support.Nonempty := Finsupp.support_nonempty_iff.mpr hl0
  rcases exists_mem_finset_dvd_all (A := A) l.support (fun i ↦ l i) hs with ⟨j, hj, hdiv⟩
  have hj0 : l j ≠ 0 := Finsupp.mem_support_iff.mp hj
  have hcoeff :
      ∀ i, i ∈ l.support → ∃ a : A, l i = a * l j := by
    intro i hi
    rcases hdiv i hi with ⟨a, ha⟩
    exact ⟨a, by simpa [mul_comm] using ha⟩
  let mFun : ι → A := fun i ↦
    if hli : l i = 0 then 0 else
      Classical.choose (hcoeff i (Finsupp.mem_support_iff.mpr hli))
  have hmFun_support : ∀ i, mFun i ≠ 0 → i ∈ l.support := by
    intro i hi
    by_cases hli : l i = 0
    · simp [mFun, hli] at hi
    · exact Finsupp.mem_support_iff.mpr hli
  let m : ι →₀ A := Finsupp.onFinset l.support mFun hmFun_support
  have hm_eq :
      ∀ i, i ∈ l.support → l i = m i * l j := by
    intro i hi
    have hli : l i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hchoice := Classical.choose_spec (hcoeff i hi)
    simpa [m, mFun, hli] using hchoice
  have hl_eq_smul : l = l j • m := by
    apply Finsupp.ext
    intro i
    by_cases hi : i ∈ l.support
    · rw [Finsupp.smul_apply]
      calc
        l i = m i * l j := hm_eq i hi
        _ = l j * m i := by simp [mul_comm]
        _ = (l j • m) i := by simp [smul_eq_mul]
    · have hli : l i = 0 := by
        by_contra hli
        exact hi (Finsupp.mem_support_iff.mpr hli)
      have hmi : m i = 0 := by
        rw [Finsupp.onFinset_apply]
        simp [mFun, hli]
      simp [Finsupp.smul_apply, hli, hmi]
  have hm_relation : Finsupp.linearCombination A u m = 0 := by
    -- Factor out the coefficient of smallest valuation from the original relation.
    have hsmul :
        (Finsupp.linearCombination A u) (l j • m) =
          l j • (Finsupp.linearCombination A u m) := by
      simpa using (Finsupp.linearCombination A u).map_smul (l j) m
    have hscaled' : (Finsupp.linearCombination A u) (l j • m) = 0 := by
      exact hl_eq_smul ▸ hl
    have hscaled : l j • Finsupp.linearCombination A u m = 0 := by
      calc
        l j • Finsupp.linearCombination A u m
            = (Finsupp.linearCombination A u) (l j • m) := by simpa using hsmul.symm
        _ = 0 := hscaled'
    have hmul :
        algebraMap A B (l j) * Finsupp.linearCombination A u m = 0 := by
      simpa [smul_eq_mul] using hscaled
    have hmapj : algebraMap A B (l j) ≠ 0 := by
      intro hzero
      exact hj0 (h.algebraMap_injective (by simpa using hzero))
    exact (mul_eq_zero.mp hmul).resolve_left hmapj
  let mκ : ι →₀ ResidueField A :=
    m.mapRange (IsLocalRing.residue A) (by simp)
  have hmκ_relation :
      Finsupp.linearCombination (ResidueField A)
        (fun i ↦ IsLocalRing.residue B (u i)) mκ = 0 := by
    -- Reducing the normalized relation modulo the maximal ideal transfers it to the residue field.
    let ρ : B →+* ResidueField B := IsLocalRing.residue B
    have hm_relation_sum : m.sum (fun i c ↦ c • u i) = 0 := by
      simpa [Finsupp.linearCombination] using hm_relation
    have hresEq : ρ (m.sum fun i c ↦ c • u i) = ρ (0 : B) := by
      exact congrArg ρ hm_relation_sum
    have hmapSum :
        ρ (m.sum fun i c ↦ c • u i) = Finset.sum m.support (fun i ↦ ρ (m i • u i)) := by
      simpa [Finsupp.sum] using (map_sum ρ (fun i ↦ m i • u i) m.support)
    have hres1 :
        m.sum (fun i c ↦ IsLocalRing.residue A c • ρ (u i)) = 0 := by
      calc
        m.sum (fun i c ↦ IsLocalRing.residue A c • ρ (u i))
            = Finset.sum m.support (fun i ↦ ρ (m i • u i)) := by
                change
                  Finset.sum m.support (fun i ↦ IsLocalRing.residue A (m i) • ρ (u i)) =
                    Finset.sum m.support (fun i ↦ ρ (m i • u i))
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [Algebra.smul_def]
                rw [show
                  algebraMap (ResidueField A) (ResidueField B) =
                    IsLocalRing.ResidueField.map (algebraMap A B) by rfl]
                calc
                  (IsLocalRing.ResidueField.map (algebraMap A B) (IsLocalRing.residue A (m i))) *
                      ρ (u i)
                      = ρ (algebraMap A B (m i)) * ρ (u i) := by
                          rw [IsLocalRing.ResidueField.map_residue (algebraMap A B)]
                  _ = ρ ((algebraMap A B (m i)) * u i) := by rw [← map_mul]
                  _ = ρ (m i • u i) := by simp [ρ, Algebra.smul_def]
        _ = ρ (m.sum fun i c ↦ c • u i) := by simpa using hmapSum.symm
        _ = ρ (0 : B) := hresEq
        _ = 0 := by simp [ρ]
    have hmκ_sum :
        mκ.sum (fun i c ↦ c • ρ (u i)) =
          m.sum (fun i c ↦ IsLocalRing.residue A c • ρ (u i)) := by
      simpa [mκ] using
        (Finsupp.sum_mapRange_index
          (f := IsLocalRing.residue A) (hf := by simp) (g := m)
          (h := fun i c ↦ c • ρ (u i))
          (fun i ↦ by simp))
    simpa [Finsupp.linearCombination] using hmκ_sum.trans hres1
  have hmκ_zero : mκ = 0 := by
    exact (linearIndependent_iff.mp hu) mκ hmκ_relation
  have hmj : m j = 1 := by
    have hmjj : l j = m j * l j := hm_eq j hj
    exact (mul_eq_right₀ hj0).mp hmjj.symm
  have hmκj : mκ j = 1 := by
    simpa [mκ, hmj] using congrArg (IsLocalRing.residue A) hmj
  have : mκ j = 0 := by simpa [hmκ_zero]
  exact False.elim (zero_ne_one (this.symm.trans hmκj))

end
