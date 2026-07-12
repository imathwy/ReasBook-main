import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_5
import LinearRepresentations_Serre_1977.Chap14.Infra_14_4_ProjectiveLift
import LinearRepresentations_Serre_1977.Chap14.Lemma_14_14_4_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_2_5
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ReductionMkQ
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.StableLatticeExactOwner
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open Representation
open scoped MonoidAlgebra Representation TensorProduct

universe u v

section ProjectiveModules

variable {p : ℕ}
variable {k : Type u} [Field k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]

/-
Domain-style sampling for this item:
* `projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism` is the canonical
  projectivity owner for `A[G]`-modules; its primitive input is invertibility of `Nat.card G` in
  the coefficient ring, not the source-facing divisibility condition `¬ p ∣ Nat.card G`.
* `group_algebra_isSemisimpleRing_of_char_not_dvd_group_order` is the Chapter `6` source-facing
  bridge from `¬ p ∣ Nat.card G` to the Maschke owner over a field.
* `decompositionHom` is the owner of the reduction map `R_K(G) → R_k(G)`, so decomposition-matrix
  statements should be organized around that owner rather than a basis-dependent `Basis.constr`
  surrogate.
-/

/-- Proposition 15-15.5-1 (1): part (i). If the order of `G` is prime to `p`, then every
`k[G]`-module is projective. This is the source-facing projectivity consequence of the canonical
Maschke semisimplicity owner instance on `k[G]`. -/
-- Proof sketch: use Maschke semisimplicity for `k[G]` under `¬ p ∣ |G|`, then apply the standard
-- fact that modules over a semisimple ring are projective.
theorem groupAlgebra_module_projective_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G) {M : Type v} [AddCommGroup M] [Module k[G] M] :
    Module.Projective k[G] M := by
  let _ : Fintype G := Fintype.ofFinite G
  -- Maschke's theorem turns the prime-to-`p` hypothesis into semisimplicity of `k[G]`.
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  let _ : IsSemisimpleRing k[G] := by
    infer_instance
  -- Over a semisimple ring, every module is projective.
  exact Module.projective_of_isSemisimpleRing k[G] M

end ProjectiveModules

section ProjectiveModulesOfCardUnit

variable {A : Type u} [CommRing A]
variable {G : Type u} [Group G] [Finite G]
variable {P : Type v} [AddCommGroup P] [Module A[G] P]

-- Proof sketch: apply the averaging-endomorphism owner
-- `projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism` with the averaged
-- scalar multiple of `LinearMap.id`.
/-- Companion bridge: if `|G|` is invertible in `A`, then every `A[G]`-module whose underlying
`A`-module is projective is projective over `A[G]`. This is the primitive invertible-order input
to the local-ring source-facing form of Proposition `15-15.5-1 (2)`. -/
-- Proof sketch: apply the averaging-endomorphism criterion with the inverse of `|G|` times the
-- identity endomorphism.
theorem groupAlgebra_module_projective_of_card_unit_of_projective
    (hcard : IsUnit (Nat.card G : A))
    (hP : Module.Projective A (RestrictScalars A A[G] P)) :
    Module.Projective A[G] P := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Module A P := Module.compHom P (algebraMap A A[G])
  let _ : IsScalarTower A A[G] P := IsScalarTower.of_compHom A A[G] P
  let u : Module.End A P :=
    Ring.inverse (Nat.card G : A) • LinearMap.id
  refine
    (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
      (Λ := A) (G := G) (P := P)).mpr ?_
  refine ⟨by simpa using hP, u, ?_⟩
  -- The inverse scalar multiple of the identity has average equal to the identity.
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

end ProjectiveModulesOfCardUnit

section LocalProjectiveModules

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type u} [Group G] [Finite G]
variable {P : Type v} [AddCommGroup P] [Module A[G] P]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Proposition 15-15.5-1: if `p` does not divide `|G|`, then the image of `|G|` in the
local ring `A` is a unit. -/
-- Proof sketch: the image of `|G|` in the residue field is nonzero because the residue field has
-- characteristic `p` and `p ∤ |G|`; local-ring theory then upgrades this to invertibility in `A`.
lemma card_unit_of_order_prime_to_p (hG : ¬ p ∣ Nat.card G) :
    IsUnit (Nat.card G : A) := by
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  -- The residue of `|G|` is nonzero in characteristic `p`, so local-ring theory upgrades it to a
  -- unit already over `A`.
  have hresidue_ne_zero : IsLocalRing.residue A (Nat.card G : A) ≠ 0 := by
    rw [← IsLocalRing.ResidueField.algebraMap_eq]
    exact NeZero.ne (Nat.card G : k)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit (Nat.card G : A)).mp hresidue_ne_zero

-- Proof sketch: part `(1)` applies over the residue field because `¬ p ∣ Nat.card G`, so the
-- image of `Nat.card G` in `A ⧸ 𝔪_A` is nonzero. In a local ring this implies that
-- `(Nat.card G : A)` is a unit, and the companion invertible-order bridge above then yields the
-- projectivity statement over `A[G]`.
/-- Proposition 15-15.5-1 (2): if the order of `G` is prime to `p`, then every `A[G]`-module
whose underlying `A`-module is projective is projective over `A[G]`. -/
theorem groupAlgebra_module_projective_of_order_prime_to_p_of_projective
    (hG : ¬ p ∣ Nat.card G)
    (hP : Module.Projective A (RestrictScalars A A[G] P)) :
    Module.Projective A[G] P := by
  -- First convert the prime-to-`p` hypothesis into invertibility of `|G|` inside the local ring.
  exact
    groupAlgebra_module_projective_of_card_unit_of_projective
      (A := A) (G := G) (P := P)
      (card_unit_of_order_prime_to_p (A := A) (G := G) (p := p) hG)
      hP

/-- Source-facing corollary of the preceding bridge theorem: if the order of `G` is prime to `p`,
then every `A[G]`-module that is free over `A` is projective. -/
-- Proof sketch: a free `A`-module is projective, so the preceding theorem applies immediately.
theorem free_groupAlgebra_module_projective_of_order_prime_to_p
    (hG : ¬ p ∣ Nat.card G) [Module.Free A (RestrictScalars A A[G] P)] :
    Module.Projective A[G] P := by
  -- Free modules are projective over the base ring, so the local projectivity bridge applies.
  let _ : Module.Projective A (RestrictScalars A A[G] P) := inferInstance
  exact
    groupAlgebra_module_projective_of_order_prime_to_p_of_projective
      (A := A) (G := G) (P := P) hG inferInstance

end LocalProjectiveModules

section DecompositionHom

variable {p : ℕ}
