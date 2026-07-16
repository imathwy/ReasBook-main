import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.GammaElementaryDescent
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.HindComplete

/-!
# Theorem 17-17.2-1: induction from `Γ_K`-elementary subgroups is surjective (DVR framework)

This file discharges the induced-lattice/reduction bridge `hind` (now proved in `HindComplete.lean`)
in the assembled descent `gammaElementary_surjective_of_hind`, yielding the unconditional statement:
in the modular DVR framework (`A` a discrete valuation ring, `↥K = Frac A` a characteristic-zero
intermediate field of a cyclotomic extension of `ℚ`, `k = ResidueField A`), every class in
`R₀[k](G)` is a finite sum of classes induced from `Γ_K`-elementary subgroups.

This is the faithful form of Serre's Theorem 39 (Theorem 17-17.2-1).  (The statement in the original
`Theorem_17_17_2_1.lean`, quantified over an *arbitrary* field `k`, is false — see the `S₃/𝔽₂`
counterexample documented there; the DVR framework here is what makes it true.)
-/

noncomputable section

universe u

open scoped Representation

namespace Representation

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {G : Type u} [Group G] [Finite G]
variable {L : Type u} [Field L] [NumberField L] [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L) [Algebra A ↥K] [IsFractionRing A ↥K]

local instance decEqGammaSubR : DecidableEq { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H } :=
  Classical.decEq _
local instance decNeGammaR0R (i : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H })
    (x : R₀[IsLocalRing.ResidueField A](i.1)) : Decidable (x ≠ 0) := Classical.dec _

/-- **Theorem 17-17.2-1 (DVR framework).**  Every class `x ∈ R₀[k](G)` is a finite sum of classes
induced from `Γ_K`-elementary subgroups, where `k = ResidueField A`.  Obtained from the assembled
descent by discharging the bridge hypothesis `hind` with `hind_complete`. -/
theorem gammaElementary_finiteRepGrothendieck_surjective
    (x : R₀[IsLocalRing.ResidueField A](G)) :
    ∃ z'' : Π₀ H : { H : Subgroup G // Subgroup.IsGammaElementary (Γ[K](G)) H },
        R₀[IsLocalRing.ResidueField A](H.1),
      x = z''.sum (fun H => ⇑(Representation.Subgroup.finiteRepGrothendieckGroupInduction
            (IsLocalRing.ResidueField A) H.1)) :=
  gammaElementary_surjective_of_hind K (fun H => hind_complete (A := A) (K := ↥K) H.1) x

end Representation
