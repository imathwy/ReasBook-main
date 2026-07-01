import Mathlib
import Serre.Chap16.Theorem_16_16_2_1

open scoped MonoidAlgebra Representation
open CategoryTheory

noncomputable section

universe u

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Theorem 17-17.2-4: a generator-level reduction isomorphism for an induced stable
lattice is the exact bridge needed to commute `decompositionHom` with subgroup induction on one
finite-dimensional representation class. -/
private theorem decomposition_subgroupInduction_class_eq_of_reduction_iso
    (H : Subgroup G) (V : FDRep K H) (L : StableLattice A V.ρ)
    (Lind : StableLattice A (FDRep.subgroupInduction (k := K) (G := G) V).ρ)
    (hLind :
      Nonempty
        (FDRep.of Lind.reductionRepresentation ≅
          FDRep.subgroupInduction (k := k) (G := G) (FDRep.of L.reductionRepresentation))) :
    decompositionHom A K G [FDRep.subgroupInduction (k := K) (G := G) V]₀ =
      Representation.finiteRep_subgroupInduction (k := k) (G := G) H
        (decompositionHom A K H [V]₀) := by
  rcases hLind with ⟨eLind⟩
  -- Evaluate `decompositionHom` on the chosen induced stable lattice for `Ind_H^G(V)`.
  calc
    decompositionHom A K G [FDRep.subgroupInduction (k := K) (G := G) V]₀ =
        [FDRep.of Lind.reductionRepresentation]₀ := by
          rw [decompositionHom_finiteRepClass_eq
            (A := A) (K := K) (G := G)
            (FDRep.subgroupInduction (k := K) (G := G) V) Lind]
    _ =
        [FDRep.subgroupInduction (k := k) (G := G) (FDRep.of L.reductionRepresentation)]₀ := by
          exact finiteRepGrothendieckClass_eq_of_nonempty_iso eLind
    _ =
        Representation.finiteRep_subgroupInduction (k := k) (G := G) H
          [FDRep.of L.reductionRepresentation]₀ := by
            rw [Representation.finiteRep_subgroupInduction_apply_class]
    _ =
        Representation.finiteRep_subgroupInduction (k := k) (G := G) H
          (decompositionHom A K H [V]₀) := by
            rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := H) V L]

/-- Helper for Theorem 17-17.2-4: once a supplied induced stable-lattice witness identifies the
reduction of `Ind_H^G(V)` with the induction of the reduction of `V`, Serre's decomposition
homomorphism commutes with subgroup induction on all subgroup Grothendieck classes. -/
theorem decomposition_subgroupInduction_eq_subgroupInduction_decomposition_of_bridge
    (H : Subgroup G)
    (hind :
      ∀ V : FDRep K H, ∀ L : StableLattice A V.ρ,
        ∃ Lind : StableLattice A (FDRep.subgroupInduction (k := K) (G := G) V).ρ,
          Nonempty
            (FDRep.of Lind.reductionRepresentation ≅
              FDRep.subgroupInduction (k := k) (G := G)
                (FDRep.of L.reductionRepresentation)))
    (y : R₀[K](H)) :
    decompositionHom A K G
        (Representation.finiteRep_subgroupInduction (k := K) (G := G) H y) =
      Representation.finiteRep_subgroupInduction (k := k) (G := G) H
        (decompositionHom A K H y) := by
  refine QuotientAddGroup.induction_on y ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · -- Both additive maps send the zero class to zero.
    simp
  · intro V
    obtain ⟨L⟩ := Representation.exists_stableLattice A V.ρ
    obtain ⟨Lind, hLind⟩ := hind V L
    -- The generator case is exactly the induced-lattice bridge recorded above.
    simpa using
      decomposition_subgroupInduction_class_eq_of_reduction_iso
        (A := A) (K := K) (G := G) (H := H) V L Lind hLind
  · intro a ha
    -- Negation is preserved because both subgroup-induction maps are additive.
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    -- Additivity descends the generator compatibility to all of `R₀[K](H)`.
    simp [map_add, ha, hb]

end

end Representation
