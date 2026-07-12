import Mathlib
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_2_1

open scoped MonoidAlgebra Representation
open CategoryTheory

noncomputable section

universe u

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Theorem 17-17.2-4: once a supplied induced stable-lattice witness identifies the
reduction of `Ind_H^G(V)` with the induction of the reduction of `V`, Serre's decomposition
homomorphism commutes with subgroup induction on all subgroup Grothendieck classes.

The actual content is the re-proof in `Chap17.Theorem_17_17_2_1.DecompositionInductionBridge`
(`decompositionHom_subgroupInduction_of_bridge`), which is transitively in scope; this file simply
re-exports it under the original Chapter-16 name.  The `indOwnerK` opaque alias for the induced
owner is what lets the `Module A` / `IsScalarTower` instances on the induced carrier resolve. -/
theorem decomposition_subgroupInduction_eq_subgroupInduction_decomposition_of_bridge
    (H : Subgroup G)
    (hind :
      ∀ V : FDRep K H, ∀ L : StableLattice A V.ρ,
        ∃ Lind : StableLattice A (Representation.indOwnerK V).ρ,
          Nonempty
            (FDRep.of Lind.reductionRepresentation ≅
              @FDRep.subgroupInduction k _ G _ _ H
                (FDRep.of L.reductionRepresentation)))
    (y : R₀[K](H)) :
    decompositionHom A K G
        (Representation.Subgroup.finiteRepGrothendieckGroupInduction K H y) =
      Representation.Subgroup.finiteRepGrothendieckGroupInduction k H
        (decompositionHom A K H y) :=
  Representation.decompositionHom_subgroupInduction_of_bridge (A := A) (K := K) (G := G) H hind y

end

end Representation
