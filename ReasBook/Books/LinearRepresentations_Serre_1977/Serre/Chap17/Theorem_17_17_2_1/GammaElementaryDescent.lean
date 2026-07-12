import Mathlib
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.CharZeroBrauer
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.DecompositionUnit
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.DecompositionInductionBridge
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.ProjectionFormulaClass
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.SubgroupRestriction

/-!
# Theorem 17-17.2-1, assembled modulo the induced-lattice bridge `hind`

In the DVR framework (`A` a discrete valuation ring, `↥K = Frac A` a characteristic-zero
intermediate field of a cyclotomic extension, `k = ResidueField A`), the induction from
`Γ_K`-elementary subgroups is surjective onto `R₀[k](G)` — **given** the induced-lattice/reduction
bridge `hind` (for each stable lattice `L` of `V`, an induced stable lattice whose reduction is
`Ind` of the reduction of `L`).

* `one_eq_sum_residue_of_hind` — the unit `1_k = d(1_K)` is a sum of `Γ_K`-elementary inductions
  (Serre's `1_k = d(1_K) = Σ Ind(d x_H)`), via step-1 (`CharZeroBrauer`), `d(1)=1`
  (`DecompositionUnit`), and `d∘Ind=Ind∘d` (`DecompositionInductionBridge`).
* `gammaElementary_surjective_of_hind` — every `x ∈ R₀[k](G)` is such a sum, since the induction
  image is an ideal (projection formula `finiteRepGrothendieckGroupInduction_mul`) containing the
  unit: `x = 1·x = Σ Ind(z_H · Res_H x)`.

This is the entire proof of Theorem 17-17.2-1 except the lattice lemma `hind` itself.
-/
noncomputable section
universe u
open scoped Representation
namespace Representation
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {G : Type u} [Group G] [Finite G]
variable {L : Type u} [Field L] [NumberField L] [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L) [Algebra A ↥K] [IsFractionRing A ↥K]

local instance instDecEqGammaElem_ged :
    DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H } :=
  Classical.decEq _
local instance instDecNeR0K_ged (i : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
    (x : R₀[↥K](i.1)) : Decidable (x ≠ 0) := Classical.dec _
local instance instDecNeR0Res_ged (i : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
    (x : R₀[IsLocalRing.ResidueField A](i.1)) : Decidable (x ≠ 0) := Classical.dec _

theorem one_eq_sum_residue_of_hind
    (hind : ∀ (H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
      (V : FDRep ↥K H.1) (Lᵥ : StableLattice A V.ρ),
      ∃ Lind : StableLattice A (indOwnerK V).ρ,
        Nonempty (FDRep.of Lind.reductionRepresentation ≅
          FDRep.subgroupInduction (k := IsLocalRing.ResidueField A) (G := G)
            (FDRep.of Lᵥ.reductionRepresentation))) :
    ∃ z' : Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        R₀[IsLocalRing.ResidueField A](H.1),
      (1 : R₀[IsLocalRing.ResidueField A](G))
        = z'.sum (fun H => ⇑(Representation.Subgroup.finiteRepGrothendieckGroupInduction
            (IsLocalRing.ResidueField A) H.1)) := by
  classical
  obtain ⟨z, hz⟩ := one_eq_sum_gammaElementary_finiteRepGrothendieckInduction (G := G) K
  refine ⟨DFinsupp.mapRange (fun H => decompositionHom A (↥K) H.1) (fun H => map_zero _) z, ?_⟩
  rw [← decompositionHom_one (A := A) (K := ↥K) (G := G), hz]
  rw [DFinsupp.sum_mapRange_index (fun H => map_zero _)]
  rw [← DFinsupp.sumAddHom_apply, ← AddMonoidHom.comp_apply, DFinsupp.comp_sumAddHom,
    DFinsupp.sumAddHom_apply]
  rw [DFinsupp.sum, DFinsupp.sum]
  refine Finset.sum_congr rfl (fun H _ => ?_)
  exact decompositionHom_subgroupInduction_of_bridge (A := A) (K := ↥K) (G := G) H.1 (hind H) (z H)

theorem gammaElementary_surjective_of_hind
    (hind : ∀ (H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
      (V : FDRep ↥K H.1) (Lᵥ : StableLattice A V.ρ),
      ∃ Lind : StableLattice A (indOwnerK V).ρ,
        Nonempty (FDRep.of Lind.reductionRepresentation ≅
          FDRep.subgroupInduction (k := IsLocalRing.ResidueField A) (G := G)
            (FDRep.of Lᵥ.reductionRepresentation)))
    (x : R₀[IsLocalRing.ResidueField A](G)) :
    ∃ z'' : Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        R₀[IsLocalRing.ResidueField A](H.1),
      x = z''.sum (fun H => ⇑(Representation.Subgroup.finiteRepGrothendieckGroupInduction
            (IsLocalRing.ResidueField A) H.1)) := by
  classical
  obtain ⟨z', hz'⟩ := one_eq_sum_residue_of_hind K hind
  refine ⟨DFinsupp.mapRange (fun H a =>
      a * Representation.Subgroup.finiteRepGrothendieckGroupRestriction
        (IsLocalRing.ResidueField A) H.1 x) (fun H => by simp) z', ?_⟩
  rw [DFinsupp.sum_mapRange_index (fun H => by simp)]
  conv_lhs => rw [show x = (z'.sum (fun H => ⇑(Representation.Subgroup.finiteRepGrothendieckGroupInduction
      (IsLocalRing.ResidueField A) H.1))) * x from by rw [← hz', one_mul]]
  rw [DFinsupp.sum, DFinsupp.sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun H _ => ?_)
  exact Representation.finiteRepGrothendieckGroupInduction_mul (k := IsLocalRing.ResidueField A)
    H.1 (z' H) x
end Representation
