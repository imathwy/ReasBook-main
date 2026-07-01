import Mathlib
import Serre.Chap14.Lemma_14_14_4_1

open scoped MonoidAlgebra

universe u v w

section

variable {A : Type u} [CommRing A] [IsLocalRing A]

namespace Representation

section LocalProjectiveBridges

variable {p : ℕ}
variable [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type v} [Group G] [Finite G]
variable {P : Type w} [AddCommGroup P] [Module A P] [Module A[G] P]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Exercise 15-15.5-3: if `p` does not divide `|G|`, then the image of `|G|` in the
local ring `A` is a unit. -/
private lemma card_unit_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G) :
    IsUnit (Nat.card G : A) := by
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  have hresidue_ne_zero : IsLocalRing.residue A (Nat.card G : A) ≠ 0 := by
    rw [← IsLocalRing.ResidueField.algebraMap_eq]
    exact NeZero.ne (Nat.card G : k)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit (Nat.card G : A)).mp hresidue_ne_zero

/-- Helper for Exercise 15-15.5-3: if `|G|` is a unit in `A`, then any `A[G]`-module whose
underlying `A`-module is projective is projective over `A[G]`. -/
private theorem groupAlgebra_module_projective_of_card_unit_of_projective
    (hcard : IsUnit (Nat.card G : A))
    [IsScalarTower A A[G] P]
    (hP : Module.Projective A P) :
    Module.Projective A[G] P := by
  let _ : Fintype G := Fintype.ofFinite G
  let u : Module.End A P := Ring.inverse (Nat.card G : A) • LinearMap.id
  refine
    (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
      (Λ := A) (G := G) (P := P)).mpr ?_
  refine ⟨hP, u, ?_⟩
  ext x
  rw [LinearMap.sumOfConjugates_apply]
  calc
    ∑ g : G, u.conjugate g x = ∑ g : G, Ring.inverse (Nat.card G : A) • x := by
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      calc
        u.conjugate g x
            = MonoidAlgebra.single g⁻¹ (1 : A) •
                (Ring.inverse (Nat.card G : A) • (MonoidAlgebra.single g (1 : A) • x)) := by
                  simp [u, LinearMap.conjugate_apply]
        _ = Ring.inverse (Nat.card G : A) •
              (MonoidAlgebra.single g⁻¹ (1 : A) • (MonoidAlgebra.single g (1 : A) • x)) := by
                rw [action_right_smul (Λ := A) (G := G) (P := P)]
        _ = Ring.inverse (Nat.card G : A) • ((1 : A[G]) • x) := by
              rw [← mul_smul, MonoidAlgebra.single_mul_single, inv_mul_cancel, mul_one,
                MonoidAlgebra.one_def]
        _ = Ring.inverse (Nat.card G : A) • x := by
              rw [one_smul]
    _ = (Fintype.card G : A) • (Ring.inverse (Nat.card G : A) • x) := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul A]
    _ = x := by
          rw [smul_smul, Fintype.card_eq_nat_card, mul_comm,
            Ring.inverse_mul_cancel _ hcard, one_smul]

/-- Helper for Exercise 15-15.5-3: if `p` does not divide `|G|`, then every free `A`-module with
`A[G]`-action is projective over `A[G]`. -/
theorem free_groupAlgebra_module_projective_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G)
    [IsScalarTower A A[G] P]
    [Module.Free A P] :
    Module.Projective A[G] P := by
  let _ : Module.Projective A P := inferInstance
  exact
    groupAlgebra_module_projective_of_card_unit_of_projective
      (A := A) (G := G) (P := P)
      (card_unit_of_order_prime_to_p (A := A) (G := G) (p := p) hG)
      inferInstance

end LocalProjectiveBridges

end Representation

end
