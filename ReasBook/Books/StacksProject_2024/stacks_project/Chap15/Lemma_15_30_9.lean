import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_30_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_30_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Ideal

open RingTheory.Sequence

variable {A : Type u} [CommRing A]

/- Domain triage:
* primary domain: commutative algebra of ideals in quotient rings and finite `H₁`-regular
  sequences;
* sampled owner declarations in this domain:
  - `Ideal.map_span`,
  - `Ideal.map_eq_iff_sup_ker_eq_of_surjective`,
  - `Ideal.mk_ker`,
  - `RingTheory.Sequence.ideal_inf_span_eq_mul_of_isH1RegularSequence_quotient`;
* layer split:
  - `source-facing`: the quotient-generation hypothesis for one fixed pair `I ≤ J`, expressed by
    a finite family in the quotient ring `A ⧸ I`;
  - `core/canonical`: the ideal owner surface, using the quotient ideal correspondence through
    `Ideal.map_eq_iff_sup_ker_eq_of_surjective` together with the finite-sequence bridge from
    Lemma `15.30.8`;
  - `bridge/view`: choose lifts of the quotient family privately, rewrite the quotient-span
    hypothesis as equality of mapped ideals, then transport it back through the canonical quotient
    ideal correspondence to recover `J = I ⊔ Ideal.span (Set.range g)`.
* primitive data vs derived API: the primitive source data are the ideals `I ≤ J` and the finite
  `H₁`-regular family in the quotient; the chosen lifts in `A` and the equality
  `J = I ⊔ Ideal.span (Set.range g)` are derived from the canonical quotient ideal correspondence
  and should not be stored as separate public data.
-/

/-- Lemma 15.30.9: if the quotient ideal `J / I` is generated in `A ⧸ I` by an `H_1`-regular
finite sequence, then `I ∩ J^2 = IJ`. -/
theorem inf_sq_eq_mul_of_quotient_generated_by_h1RegularSequence
    (I J : Ideal A) (hIJ : I ≤ J)
    (hgen :
      ∃ (m : ℕ) (f : Fin m → A ⧸ I),
        J.map (Ideal.Quotient.mk I) = Ideal.span (Set.range f) ∧ IsH1RegularSequence f) :
    I ⊓ J ^ 2 = I * J := by
  classical
  obtain ⟨m, f, hmap, hreg⟩ := hgen
  let π : A →+* A ⧸ I := Ideal.Quotient.mk I
  choose g hg using fun i ↦ Ideal.Quotient.mk_surjective (f i)
  let K : Ideal A := Ideal.span (Set.range g)
  have hg' : (fun i ↦ π (g i)) = f := funext hg
  have hJ : J = I ⊔ K := by
    have hrange : Set.range f = π '' Set.range g := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨g i, ⟨i, rfl⟩, hg i⟩
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hg i).symm⟩
    have hmap' : J.map π = K.map π := by
      rw [hmap]
      simpa [K, Ideal.map_span] using congrArg Ideal.span hrange
    rw [Ideal.map_eq_iff_sup_ker_eq_of_surjective π Ideal.Quotient.mk_surjective] at hmap'
    simpa [π, K, Ideal.mk_ker, sup_eq_left.mpr hIJ, sup_comm] using hmap'
  have hIK :
      I ⊓ K = I * K := by
    have hreg' : IsH1RegularSequence (fun i ↦ π (g i)) := by
      simpa [π, hg'] using hreg
    simpa [π, K] using ideal_inf_span_eq_mul_of_isH1RegularSequence_quotient I g hreg'
  have hKJ : K ≤ J := by
    rw [hJ]
    exact le_sup_right
  have hIK_le_hIJ :
      I * K ≤ I * J :=
    Ideal.mul_mono_right hKJ
  have hJ_sq :
      J ^ 2 = I * J ⊔ K ^ 2 := by
    calc
      J ^ 2 = J * J := by rw [pow_two]
      _ = (I ⊔ K) * J := by rw [hJ]
      _ = I * J ⊔ K * J := by rw [Ideal.sup_mul]
      _ = I * J ⊔ K * (I ⊔ K) := by rw [hJ]
      _ = I * J ⊔ (K * I ⊔ K ^ 2) := by rw [Ideal.mul_sup, pow_two]
      _ = I * J ⊔ (I * K ⊔ K ^ 2) := by rw [Ideal.mul_comm K I]
      _ = I * J ⊔ K ^ 2 := by
        rw [← sup_assoc, sup_eq_left.mpr hIK_le_hIJ]
  have hIinfKsq :
      I ⊓ K ^ 2 ≤ I * J := by
    calc
      I ⊓ K ^ 2 ≤ I ⊓ K := by
        refine inf_le_inf_left _ ?_
        simpa [pow_two] using (show K * K ≤ K from Ideal.mul_le_right)
      _ = I * K := hIK
      _ ≤ I * J := hIK_le_hIJ
  have hmul_le_I : I * J ≤ I := Ideal.mul_le_right
  apply le_antisymm
  · calc
      I ⊓ J ^ 2 = I ⊓ (I * J ⊔ K ^ 2) := by rw [hJ_sq]
      _ = I * J ⊔ (I ⊓ K ^ 2) := by
        rw [sup_comm, ← inf_sup_assoc_of_le (K ^ 2) hmul_le_I, sup_comm]
      _ = I * J := sup_eq_left.mpr hIinfKsq
      _ ≤ I * J := le_rfl
  · refine le_inf Ideal.mul_le_right ?_
    have hmul : I * J ≤ J * J := Ideal.mul_mono_left hIJ
    simpa [pow_two] using hmul

end Ideal
