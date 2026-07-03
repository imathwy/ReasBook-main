import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_6
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type v} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Theorem 17-17.6-1: when the Hall kernel `I` has order prime to `p`, any free
lift carrier of LinearRepresentations_Serre_1977's fixed constituent is already projective over the group algebra `A[I]`.
This isolates the projectivity input needed before invoking the Chapter `14` endomorphism
transport API. -/
theorem fixed_constituent_lift_projective_of_order_prime_to_p
    (hp : Nat.Prime p)
    (I : Subgroup G)
    (hIcop : Nat.Coprime p (Nat.card I))
    {P_S : Type w} [AddCommGroup P_S] [Module A P_S]
    [Module (MonoidAlgebra A I) P_S]
    [IsScalarTower A (MonoidAlgebra A I) P_S]
    [Module.Free A P_S] :
    Module.Projective (MonoidAlgebra A I) P_S := by
  -- LinearRepresentations_Serre_1977's Hall-kernel hypothesis makes `|I|` a unit in `A`, so the standard averaging
  -- argument upgrades free `A`-modules to projective `A[I]`-modules.
  exact
    free_groupAlgebra_module_projective_of_order_prime_to_p
      (A := A) (p := p) (G := I)
      (hp.coprime_iff_not_dvd.mp hIcop)

/-- Helper for Theorem 17-17.6-1: any residue-field lift is surjective on the underlying
modules. This re-exposes the closed-fiber surjectivity used in the scalar-reduction step without
reopening the whole Chapter `14` base-change file. -/
theorem fixed_constituent_reduction_surjective
    {H : Type*} [Group H] [Finite H]
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module (MonoidAlgebra A H) P] [IsScalarTower A (MonoidAlgebra A H) P]
    [Module.Free A P] [Module.Finite A P]
    {Pbar : Type*} [AddCommGroup Pbar] [Module A Pbar] [Module k Pbar]
    [IsScalarTower A k Pbar]
    [Module (MonoidAlgebra k H) Pbar]
    [IsScalarTower k (MonoidAlgebra k H) Pbar]
    {red : P →ₗ[A] Pbar}
    (hred : red.IsResidueFieldReduction H) :
    Function.Surjective red := by
  -- Write a target vector as the image of a pure tensor through the base-change equivalence, then
  -- choose a lift of the scalar coefficient along `A → k`.
  intro x
  obtain ⟨t, rfl⟩ := hred.1.equiv.surjective x
  have hres :
      Function.Surjective (algebraMap A k) := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using IsLocalRing.residue_surjective
  obtain ⟨y, hy⟩ :=
    TensorProduct.mk_surjective (R := A) (S := k) (M := P) hres t
  refine ⟨y, ?_⟩
  calc
    red y = (1 : k) • red y := by simp
    _ = hred.1.equiv ((TensorProduct.mk A k P 1) y) := by
          symm
          simpa using hred.1.equiv_tmul (1 : k) y
    _ = hred.1.equiv t := by rw [hy]

end

end Representation
