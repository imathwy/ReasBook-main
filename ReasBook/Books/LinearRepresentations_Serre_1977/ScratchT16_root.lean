import Mathlib
noncomputable section
universe u
namespace Representation
section
variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable [IsDomain A]
variable [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

open Polynomial IsLocalRing

theorem exists_primitiveRoot_lift (m : ℕ) (hm0 : m ≠ 0) (hm : ¬ p ∣ m) :
    ∃ ω : A, IsPrimitiveRoot ω m := by
  classical
  set k := IsLocalRing.ResidueField A with hk
  have hmk : (m : k) ≠ 0 := fun h ↦ hm ((CharP.cast_eq_zero_iff k p m).1 h)
  have : NeZero (m : k) := ⟨hmk⟩
  obtain ⟨ωbar, hωbar⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k m
  -- f = X^m - C 1
  set f : A[X] := X ^ m - C 1 with hf
  have hfmonic : f.Monic := monic_X_pow_sub_C (1 : A) hm0
  -- Henselian TFAE clause 2
  have htfae := (HenselianLocalRing.TFAE A).out 0 1
  have hclause2 := htfae.mp (inferInstance : HenselianLocalRing A)
  -- aeval ωbar f = 0
  have hroot : (aeval ωbar) f = 0 := by
    rw [hf]
    simp only [map_sub, map_pow, aeval_X, map_one]
    rw [hωbar.pow_eq_one, sub_self]
  -- aeval ωbar (derivative f) ≠ 0
  have hsep : (aeval ωbar) (derivative f) ≠ 0 := by
    rw [hf]
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero,
      map_mul, map_pow, aeval_X, aeval_C]
    -- = (m : k) * ωbar^(m-1) ≠ 0
    have hωbar0 : ωbar ≠ 0 := hωbar.ne_zero hm0
    exact mul_ne_zero hmk (pow_ne_zero _ hωbar0)
  obtain ⟨ω, hωroot, hωres⟩ := hclause2 f hfmonic ωbar hroot hsep
  -- now: ω^m = 1, residue ω = ωbar; build IsPrimitiveRoot ω m
  refine ⟨ω, ?_, ?_⟩
  · -- ω^m = 1
    have : f.IsRoot ω := hωroot
    rw [IsRoot.def, hf] at this
    simpa [sub_eq_zero] using this
  · -- ∀ l, ω^l = 1 → m ∣ l
    intro l hl
    apply hωbar.dvd_of_pow_eq_one
    -- residue (ω^l) = ωbar^l = residue 1 = 1
    have : (residue A) (ω ^ l) = (residue A) 1 := by rw [hl]
    rw [map_pow, map_one] at this
    rw [← hωres, ← map_pow, hl, map_one]

end
end Representation
