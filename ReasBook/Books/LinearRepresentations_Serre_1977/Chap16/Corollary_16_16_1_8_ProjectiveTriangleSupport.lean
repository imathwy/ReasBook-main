import Mathlib
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Corollary 16-16.1-8: support theorem packaging the projective-generator case of
LinearRepresentations_Serre_1977's `c = d ∘ e` triangle. -/
theorem decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
  sorry

/-- Helper for Corollary 16-16.1-8: support theorem packaging the additive compatibility
`d ∘ e = c` on projective Grothendieck classes over the residue field. -/
theorem decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom_local_support
    [HenselianLocalRing A]
    (x : finiteProjectiveGroupAlgebraGrothendieckGroup k G) :
    decompositionHom A K G
        ((projectiveGrothendieckScalarExtensionHom A K) x) =
      cartanHom k G x := by
  sorry

end

end Representation
