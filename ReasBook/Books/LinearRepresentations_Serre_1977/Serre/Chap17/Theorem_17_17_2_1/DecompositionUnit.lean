import Mathlib
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.ReductionFinrank
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_1_2.FiniteRepTensorRing
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1

/-!
# Serre's decomposition homomorphism sends the unit to the unit

For a discrete valuation ring `A` with fraction field `K` and residue field `k`, the decomposition
homomorphism `d = decompositionHom : R₀[K](G) → R₀[k](G)` satisfies `d 1 = 1`.

This is the step `1_k = d(1_K)` in Serre's proof of Theorem 39 (= Theorem 17-17.2-1).  The unit
class is `[𝟙]₀`, represented by the one-dimensional trivial representation; any stable lattice of a
one-dimensional trivial representation reduces (by `finrank_reduction_eq`) to a one-dimensional
trivial residue representation, which is the unit class of `R₀[k](G)`.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped Representation

namespace Representation

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- The class of the one-dimensional trivial representation is the ring unit of `R₀[F](G)`. -/
theorem finiteRepGrothendieckClass_trivial_eq_one (F : Type u) [Field F] :
    ([FDRep.of (Representation.trivial F G F)]₀ : R₀[F](G)) = 1 := by
  symm
  show ([𝟙_ (FDRep F G)]₀ : R₀[F](G)) = [FDRep.of (Representation.trivial F G F)]₀
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso
    ⟨Action.mkIso (Iso.refl _) (fun g => by ext x; rfl)⟩

/-- The decomposition homomorphism sends the class of a one-dimensional trivial representation to
the unit of `R₀[k](G)`: its reduction is one-dimensional (`finrank_reduction_eq`) with trivial
action, hence isomorphic to the trivial residue representation. -/
theorem decompositionHom_class_eq_one_of_isTrivial (W : FDRep K G)
    (htriv : Representation.IsTrivial W.ρ) (hW1 : Module.finrank K W = 1) :
    decompositionHom A K G [W]₀ = 1 := by
  obtain ⟨L⟩ := Representation.exists_stableLattice A W.ρ
  rw [decompositionHom_finiteRepClass_eq A K G W L,
    ← finiteRepGrothendieckClass_trivial_eq_one (G := G) k]
  apply finiteRepGrothendieckClass_eq_of_nonempty_iso
  have hdim : Module.finrank k L.reduction = 1 := by rw [finrank_reduction_eq]; exact hW1
  haveI hredtriv : Representation.IsTrivial L.reductionRepresentation := ⟨fun g => by
    refine LinearMap.ext fun z => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [StableLattice.reductionRepresentation_apply_mk]
    have hy : (L.toRepresentation g) y = y := by
      apply Subtype.ext
      rw [StableLattice.toRepresentation_apply_coe, htriv.out g]; rfl
    rw [hy]; rfl⟩
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hdim
  refine ⟨Representation.Equiv.toFDRepIso (Representation.Equiv.mk e.symm (fun g => ?_))⟩
  refine LinearMap.ext fun z => ?_
  show e.symm (L.reductionRepresentation g z) = (Representation.trivial k G k g) (e.symm z)
  rw [hredtriv.out g]
  rfl

/-- Serre's decomposition homomorphism sends the unit class to the unit class: `d 1 = 1`. -/
theorem decompositionHom_one : decompositionHom A K G 1 = 1 := by
  rw [← finiteRepGrothendieckClass_trivial_eq_one (G := G) K]
  refine decompositionHom_class_eq_one_of_isTrivial (FDRep.of (Representation.trivial K G K))
    (inferInstanceAs (Representation.IsTrivial (Representation.trivial K G K))) ?_
  change Module.finrank K K = 1
  exact Module.finrank_self K

end Representation
