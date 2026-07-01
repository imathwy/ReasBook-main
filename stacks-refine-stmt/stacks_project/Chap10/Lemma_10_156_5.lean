import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open IsLocalRing
open Algebra.TensorProduct

universe u v w

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
variable [Algebra A B] [Algebra A C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]
variable [Algebra.IsIntegral A C]
variable (hκ :
  IsPurelyInseparable (ResidueField A) (ResidueField C) ∨
    IsPurelyInseparable (ResidueField A) (ResidueField B))

-- Proof sketch: because `A → C` is integral, the base-changed map
-- `includeLeftRingHom : B →+* B ⊗[A] C` is integral, so every maximal ideal of `B ⊗[A] C` lies
-- over the maximal ideal of `B`. Modding out by `maximalIdeal B` identifies the closed fiber with
-- `ResidueField B ⊗[ResidueField A] ResidueField C`, whose spectrum is a single point when either
-- of the two residue-field extensions over `ResidueField A` is purely inseparable. Hence the
-- tensor product has a unique maximal ideal.
/-- Lemma 10.156.5: if `A → B` and `A → C` are local homomorphisms of local rings, `A → C` is
integral, and either `ResidueField C / ResidueField A` or `ResidueField B / ResidueField A` is
purely inseparable, then `B ⊗[A] C` is a local ring. -/
theorem tensorProduct_isLocalRing_of_local_of_integral_of_residueField_purelyInseparable
    : IsLocalRing (B ⊗[A] C) := sorry

-- Proof sketch: after the previous theorem gives `B ⊗[A] C` a local-ring structure, the unique
-- maximal ideal of the tensor product lies over the maximal ideal of `B`, so the left structural
-- map reflects units. Equivalently, its maximal-ideal comap is the maximal ideal of `B`.
/-- Under the residue-field purely inseparable hypothesis, the canonical map
`B → B ⊗[A] C` is a local homomorphism. -/
theorem tensorProduct_includeLeft_isLocalHom_of_local_of_integral_of_residueField_purelyInseparable
    : IsLocalHom (includeLeft : B →ₐ[A] B ⊗[A] C) := by
  letI : IsLocalRing (B ⊗[A] C) :=
    tensorProduct_isLocalRing_of_local_of_integral_of_residueField_purelyInseparable
  sorry

-- Proof sketch: the same unique-maximal-ideal argument shows that the maximal ideal of
-- `B ⊗[A] C` also lies over the maximal ideal of `C`. Therefore the right structural map satisfies
-- the local-homomorphism criterion via comap of maximal ideals.
/-- Under the residue-field purely inseparable hypothesis, the canonical map
`C → B ⊗[A] C` is a local homomorphism. -/
theorem tensorProduct_includeRight_isLocalHom_of_local_of_integral_of_residueField_purelyInseparable
    : IsLocalHom (includeRight : C →ₐ[A] B ⊗[A] C) := by
  letI : IsLocalRing (B ⊗[A] C) :=
    tensorProduct_isLocalRing_of_local_of_integral_of_residueField_purelyInseparable
  sorry

end
