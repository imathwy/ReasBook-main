import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_5.SubgroupInduction
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.InducedLattice
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.ReductionInductionIso
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.ReductionFinrank
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_2_1.InductionFinrank
import LinearRepresentations_Serre_1977.Serre.Chap02.Theorem_2_2_3_5

/-!
# The induced-lattice/reduction bridge `hind` (complete)

This file completes the bridge hypothesis `hind` of `decompositionHom_subgroupInduction_of_bridge`
(step (D) of Theorem 17-17.2-1): for every `V : FDRep K H` and every stable `A`-lattice `L` of
`V.ρ`, the reduction of the induced lattice is `G`-equivariantly isomorphic to the induction of the
reduction,
`reduction (inducedStableLattice V L) ≅ Ind_H^G (reduction L)`.

The isomorphism is the inverse map `Ψ` (`Representation.psi`, `IndV.mk g [l] ↦ [indMk V g ↑l]`),
which is surjective (`psi_surjective`) and `G`-equivariant (`psi_equivariant`); it is bijective by a
dimension count: both sides have dimension `[G : H] · dim_K V`, using
`finrank_indV` (`dim (Ind W) = [G:H]·dim W`) and `finrank_reduction_eq` (`dim_{k̄} (reduction) =
dim_K` of the ambient).
-/

noncomputable section

universe u

open Finsupp TensorProduct CategoryTheory

namespace Representation

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k̄" => IsLocalRing.ResidueField A

/-- **Part 2 of `hind` (the reduction isomorphism).**  For `V : FDRep K H` and a stable lattice `L`
of `V.ρ`, the reduction of the induced lattice is `G`-equivariantly isomorphic to the induction of
the reduction. -/
theorem reduction_subgroupInduction_iso {H : Subgroup G} (V : FDRep K H) (L : StableLattice A V.ρ) :
    Nonempty (FDRep.of (inducedStableLattice V L).reductionRepresentation ≅
      FDRep.subgroupInduction (k := k̄) (G := G) (FDRep.of L.reductionRepresentation)) := by
  haveI : FiniteDimensional K V.V := inferInstance
  haveI : Module.Finite k̄ (Representation.IndV H.subtype L.reductionRepresentation) :=
    FDRep.subgroupInduction_finite (k := k̄) (FDRep.of L.reductionRepresentation)
  -- Dimension equality: both sides equal `[G:H] · dim_K V`.
  have hdim : Module.finrank k̄ (Representation.IndV H.subtype L.reductionRepresentation)
      = Module.finrank k̄ (inducedStableLattice V L).reduction := by
    have e1 := finrank_indV (k := k̄) (FDRep.of L.reductionRepresentation)
    rw [FDRep.of_ρ'] at e1
    have e2 := finrank_indV (k := K) V
    rw [finrank_reduction_eq (indOwnerK V).ρ (inducedStableLattice V L),
      show Module.finrank K (indOwnerK V).V = Module.finrank K (Representation.IndV H.subtype V.ρ)
        from rfl, e2, e1, finrank_reduction_eq V.ρ L]
  -- `Ψ` is bijective (surjective + equal dimension), hence an isomorphism of representations.
  have hbij : Function.Bijective (psi V L) :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr (psi_surjective V L),
      psi_surjective V L⟩
  let e : Representation.Equiv (Representation.ind H.subtype L.reductionRepresentation)
      (inducedStableLattice V L).reductionRepresentation :=
    Representation.Equiv.mk (LinearEquiv.ofBijective (psi V L) hbij) (psi_equivariant V L)
  exact ⟨e.toFDRepIso.symm⟩

/-- **The bridge hypothesis `hind` of `decompositionHom_subgroupInduction_of_bridge`, discharged.**
Combining the induced lattice (part 1) with the reduction isomorphism (part 2). -/
theorem hind_complete (H : Subgroup G) :
    ∀ V : FDRep K H, ∀ L : StableLattice A V.ρ,
      ∃ Lind : StableLattice A (indOwnerK V).ρ,
        Nonempty (FDRep.of Lind.reductionRepresentation ≅
          FDRep.subgroupInduction (k := IsLocalRing.ResidueField A) (G := G)
            (FDRep.of L.reductionRepresentation)) :=
  hind_of_inducedStableLattice_reductionIso H (fun V L => reduction_subgroupInduction_iso V L)

end Representation
