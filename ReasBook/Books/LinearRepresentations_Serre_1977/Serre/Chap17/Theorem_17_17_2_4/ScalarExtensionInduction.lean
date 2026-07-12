import Mathlib
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5.SubgroupInduction
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_2_1.ProjectiveInductionScalarExtension
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.ProjectionFormula

/-!
# Ordinary scalar extension commutes with subgroup induction

For a field extension `F → k` and a subgroup `H ≤ G`, scalar extension of finite-dimensional
representations commutes with subgroup induction:
`scalarExt (Ind_H^G V) ≅ Ind_H^G (scalarExt V)`, hence the Grothendieck-group homomorphism
`finiteRepGrothendieckScalarExtensionHom` commutes with `finiteRepGrothendieckGroupInduction`.

This is the ordinary (`R₀`) analogue of the projective scalar-extension/induction class equality
`finiteRep_subgroupInduction_projective_scalarExtension_class_eq`.
-/

noncomputable section

universe u

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct

namespace Representation

section

variable {F : Type u} [Field F]
variable {k : Type u} [Field k] [Algebra F k]
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- A `Rep`-level isomorphism of the images under `forget₂` upgrades to a Grothendieck-class
equality in `R₀[k](G)`. -/
private theorem fdRepClass_eq_of_rep_iso
    {V W : FDRep k G}
    (eRep : ((forget₂ (FDRep k G) (Rep k G)).obj V) ≅
      ((forget₂ (FDRep k G) (Rep k G)).obj W)) :
    [V]₀ = [W]₀ := by
  let e : V ≅ W := by
    refine ⟨(FDRep.forget₂HomLinearEquiv V W) eRep.hom,
      (FDRep.forget₂HomLinearEquiv W V) eRep.inv, ?_, ?_⟩
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.hom ≫ eRep.inv = 𝟙 _
      exact eRep.hom_inv_id
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.inv ≫ eRep.hom = 𝟙 _
      exact eRep.inv_hom_id
  exact finiteRepGrothendieckClass_eq_of_iso e

/-- On generator classes, ordinary subgroup induction commutes with scalar extension. -/
theorem finiteRep_subgroupInduction_scalarExtension_class_eq
    (H : Subgroup G) (V : FDRep F H) :
    ([FDRep.scalarExtension (k := k) (FDRep.subgroupInduction V)]₀ : R₀[k](G)) =
      [FDRep.subgroupInduction (FDRep.scalarExtension (k := k) V)]₀ := by
  apply fdRepClass_eq_of_rep_iso (k := k) (G := G)
  let ρ : Representation F H V.V := V.ρ
  let e₁ :
      ((forget₂ (FDRep k G) (Rep k G)).obj
        (FDRep.scalarExtension (k := k) (FDRep.subgroupInduction (k := F) (G := G) V))) ≅
        Rep.of (Representation.scalarExtension (k := k) (Representation.ind H.subtype ρ)) :=
    Iso.refl _
  let e₂ :
      Rep.of (Representation.scalarExtension (k := k) (Representation.ind H.subtype ρ)) ≅
        Rep.ind H.subtype (Rep.of (Representation.scalarExtension (k := k) ρ)) :=
    scalarExtension_ind_iso_ind_scalarExtension (A := F) (K := k) (G := G) (H := H) ρ
  let e₃ :
      Rep.ind H.subtype (Rep.of (Representation.scalarExtension (k := k) ρ)) ≅
        ((forget₂ (FDRep k G) (Rep k G)).obj
          (FDRep.subgroupInduction (k := k) (G := G) (FDRep.scalarExtension (k := k) V))) :=
    Iso.refl _
  exact e₁ ≪≫ e₂ ≪≫ e₃

/-- Ordinary scalar extension commutes with subgroup induction on all of `R₀[F](H)`. -/
theorem finiteRepGrothendieckScalarExtensionHom_subgroupInduction
    (H : Subgroup G) (y : R₀[F](H)) :
    finiteRepGrothendieckScalarExtensionHom F k G
        (Representation.Subgroup.finiteRepGrothendieckGroupInduction F H y) =
      Representation.Subgroup.finiteRepGrothendieckGroupInduction k H
        (finiteRepGrothendieckScalarExtensionHom F k H y) := by
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    change finiteRepGrothendieckScalarExtensionHom F k G
        (Representation.Subgroup.finiteRepGrothendieckGroupInduction F H [V]₀) =
      Representation.Subgroup.finiteRepGrothendieckGroupInduction k H
        (finiteRepGrothendieckScalarExtensionHom F k H [V]₀)
    simp only [Representation.Subgroup.finiteRepGrothendieckGroupInduction_apply_class,
      finiteRepGrothendieckScalarExtensionHom_class_eq]
    exact finiteRep_subgroupInduction_scalarExtension_class_eq H V
  · intro V hV
    simp [map_neg, hV]
  · intro a b ha hb
    simp [map_add, ha, hb]

omit [Finite G] in
/-- The scalar extension of the one-dimensional trivial representation is the trivial
representation: `k ⊗[F] (trivial F) ≅ trivial k`. -/
theorem finiteRepGrothendieckScalarExtensionHom_trivial_class :
    finiteRepGrothendieckScalarExtensionHom F k G
        [FDRep.of (Representation.trivial F G F)]₀ =
      [FDRep.of (Representation.trivial k G k)]₀ := by
  rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
  apply finiteRepGrothendieckClass_eq_of_iso
  refine Representation.Equiv.toFDRepIso
    (Representation.Equiv.mk
      (TensorProduct.AlgebraTensorModule.rid F k k) ?_)
  intro g
  apply LinearMap.ext
  intro x
  simp [Representation.scalarExtension, Representation.trivial]

end

end Representation
