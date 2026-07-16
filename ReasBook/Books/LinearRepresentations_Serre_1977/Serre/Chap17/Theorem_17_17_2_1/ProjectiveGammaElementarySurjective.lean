import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.GammaElementaryDescent
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.HindComplete
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.ProjectiveProjectionFormula
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.ProjectiveSubgroupRestriction

/-!
# Theorem 17-17.2-1 (projective version, DVR framework)

The projective analog of `gammaElementary_finiteRepGrothendieck_surjective`: in the modular DVR
framework (`A` a discrete valuation ring, `↥K = Frac A` a characteristic-zero intermediate field of
a cyclotomic extension, `k = ResidueField A`), every class in `P₀[k](G)` is a finite sum of classes
induced from `Γ_K`-elementary subgroups.

The proof reuses the **R₀ unit decomposition** `1 = ∑ Ind_H(z_H)` (`one_eq_sum_residue_of_hind`,
discharging the bridge with `hind_complete`) together with the **projective projection formula**
`Ind_H(a) • p = Ind_H(a • Res_H p)` (`finiteProjectiveGroupAlgebraGrothendieckGroupInduction_smul`),
since `P₀[k](G)` is a module over the ring `R₀[k](G)`:
`p = 1 • p = (∑ Ind_H(z_H)) • p = ∑ Ind_H(z_H • Res_H p)`.
-/

noncomputable section

universe u

open scoped Representation

namespace Representation

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {G : Type u} [Group G] [Finite G]
variable {L : Type u} [Field L] [NumberField L] [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L) [Algebra A ↥K] [IsFractionRing A ↥K]

local instance decEqGammaSubP : DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H } :=
  Classical.decEq _
local instance decNeGammaR0P (i : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
    (x : R₀[IsLocalRing.ResidueField A](i.1)) : Decidable (x ≠ 0) := Classical.dec _
local instance decNeGammaP0P (i : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
    (x : P₀[IsLocalRing.ResidueField A](i.1)) : Decidable (x ≠ 0) := Classical.dec _

/-- **Theorem 17-17.2-1, projective version (DVR framework).**  Every class `x ∈ P₀[k](G)` is a
finite sum of classes induced from `Γ_K`-elementary subgroups, where `k = ResidueField A`. -/
theorem gammaElementary_finiteProjectiveGrothendieck_surjective
    (x : P₀[IsLocalRing.ResidueField A](G)) :
    ∃ z'' : Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        P₀[IsLocalRing.ResidueField A](H.1),
      x = z''.sum (fun H => ⇑(Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction
            (IsLocalRing.ResidueField A) H.1)) := by
  classical
  obtain ⟨z', hz'⟩ := one_eq_sum_residue_of_hind (G := G) (L := L) K
    (fun H => hind_complete (A := A) (K := ↥K) H.1)
  refine ⟨DFinsupp.mapRange (fun H a => a •
    Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRestriction
      (IsLocalRing.ResidueField A) H.1 x) (fun H => by simp) z', ?_⟩
  rw [DFinsupp.sum_mapRange_index (fun H => by simp)]
  conv_lhs => rw [show x = (z'.sum (fun H => ⇑(Representation.Subgroup.finiteRepGrothendieckGroupInduction
    (IsLocalRing.ResidueField A) H.1))) • x from by rw [← hz', one_smul]]
  rw [DFinsupp.sum, DFinsupp.sum, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun H _ => ?_)
  exact finiteProjectiveGroupAlgebraGrothendieckGroupInduction_smul H.1 (z' H) x

end Representation
