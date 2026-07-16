import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.SubgroupInduction
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1

/-!
# Decomposition commutes with subgroup induction (modulo the induced-lattice bridge)

`decompositionHom_subgroupInduction_of_bridge` is step (D) of Theorem 17-17.2-1: Serre's
decomposition homomorphism `d` commutes with subgroup induction on the Grothendieck groups,
`d (Ind_H y) = Ind_H (d y)`, **given** the induced-lattice/reduction bridge hypothesis `hind`
(for every stable lattice `L` of `V`, there is a stable lattice of `Ind_H V` whose reduction is
isomorphic to `Ind_H` of the reduction of `L`).

This re-proves the content of `Serre/Chap16/SubgroupInductionDecompositionBridge.lean` in a file that
does NOT import `Serre.Chap16.Theorem_16_16_2_1` (which is currently broken by an unrelated universe
bug in `Serre/Chap12/Exercise_12_12_2_6/ScalarExtensionPairing.lean`), and uses the project's
canonical Grothendieck induction `Subgroup.finiteRepGrothendieckGroupInduction`.

The `private def indOwnerK` alias keeps `FDRep.subgroupInduction V` opaque to instance synthesis so
the `Module A` / `IsScalarTower` instances on the induced carrier resolve canonically.
-/
noncomputable section
universe u
open CategoryTheory
open scoped Representation
namespace Representation
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

/-- Opaque alias for the induced FDRep (semireducible `def`: invisible to instance synthesis so the
canonical `FDRep.instModuleRestrictScalars`/`instIsScalarTowerRestrictScalars` resolve without
diamond; unfolds at default transparency in proofs). -/
def indOwnerK {H : Subgroup G} (V : FDRep K H) : FDRep K G :=
  FDRep.subgroupInduction (k := K) (G := G) V

theorem decomposition_subgroupInduction_class_eq_of_reduction_iso
    {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ)
    (Lind : StableLattice A (indOwnerK V).ρ)
    (hLind : Nonempty (FDRep.of Lind.reductionRepresentation ≅
      FDRep.subgroupInduction (k := IsLocalRing.ResidueField A) (G := G)
        (FDRep.of L.reductionRepresentation))) :
    decompositionHom A K G [indOwnerK V]₀ =
      Representation.Subgroup.finiteRepGrothendieckGroupInduction (IsLocalRing.ResidueField A) H
        (decompositionHom A K H [V]₀) := by
  calc
    decompositionHom A K G [indOwnerK V]₀
        = [FDRep.of Lind.reductionRepresentation]₀ := by
          rw [decompositionHom_finiteRepClass_eq A K G (indOwnerK V) Lind]
    _ = [FDRep.subgroupInduction (k := IsLocalRing.ResidueField A) (G := G)
          (FDRep.of L.reductionRepresentation)]₀ :=
          finiteRepGrothendieckClass_eq_of_nonempty_iso hLind
    _ = Representation.Subgroup.finiteRepGrothendieckGroupInduction (IsLocalRing.ResidueField A) H
          [FDRep.of L.reductionRepresentation]₀ := by
          rw [Representation.Subgroup.finiteRepGrothendieckGroupInduction_apply_class]
    _ = Representation.Subgroup.finiteRepGrothendieckGroupInduction (IsLocalRing.ResidueField A) H
          (decompositionHom A K H [V]₀) := by
          rw [decompositionHom_finiteRepClass_eq A K H V L]

theorem decompositionHom_subgroupInduction_of_bridge (H : Subgroup G)
    (hind : ∀ V : FDRep K H, ∀ L : StableLattice A V.ρ,
      ∃ Lind : StableLattice A (indOwnerK V).ρ,
        Nonempty (FDRep.of Lind.reductionRepresentation ≅
          FDRep.subgroupInduction (k := IsLocalRing.ResidueField A) (G := G)
            (FDRep.of L.reductionRepresentation)))
    (y : R₀[K](H)) :
    decompositionHom A K G
        (Representation.Subgroup.finiteRepGrothendieckGroupInduction K H y) =
      Representation.Subgroup.finiteRepGrothendieckGroupInduction (IsLocalRing.ResidueField A) H
        (decompositionHom A K H y) := by
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp
  · intro V
    obtain ⟨L⟩ := Representation.exists_stableLattice A V.ρ
    obtain ⟨Lind, hLind⟩ := hind V L
    show decompositionHom A K G
        (Representation.Subgroup.finiteRepGrothendieckGroupInduction K H [V]₀)
      = Representation.Subgroup.finiteRepGrothendieckGroupInduction (IsLocalRing.ResidueField A) H
          (decompositionHom A K H [V]₀)
    rw [Representation.Subgroup.finiteRepGrothendieckGroupInduction_apply_class]
    exact decomposition_subgroupInduction_class_eq_of_reduction_iso V L Lind hLind
  · intro a ha
    simp [map_neg, ha]
  · intro a b ha hb
    simp [map_add, ha, hb]
end Representation
