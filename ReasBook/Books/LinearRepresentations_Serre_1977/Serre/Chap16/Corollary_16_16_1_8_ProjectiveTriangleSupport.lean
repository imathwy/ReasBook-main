import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1.ProjectiveLiteralReduction
import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1

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
Serre's `c = d ∘ e` triangle. -/
theorem decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_support
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    decompositionHom A K G [Q.scalarExtension K]₀ =
      cartanHom k G [Q.residueFieldReduction]ₚ₀ := by
  -- Serre §16 prop 11 on a projective generator: `d([Q⊗K]₀) = [Q̄]₀ = c([Q̄]ₚ₀)`.  The first step
  -- (the FDRep/TensorProduct instance diamond) is supplied by the literal-reduction lemma; the
  -- second is `cartanHom_projectiveClass_eq` (`c([P]ₚ₀) = [P.toFiniteRep]₀`, definitional).
  rw [decompositionHom_projective_scalarExtension_class_eq_residueFieldReduction_finiteRepClass_support,
    cartanHom_projectiveClass_eq]

/-- Helper for Corollary 16-16.1-8: support theorem packaging the additive compatibility
`d ∘ e = c` on projective Grothendieck classes over the residue field. -/
theorem decompositionHom_comp_projectiveGrothendieckScalarExtensionHom_eq_cartanHom_local_support
    [HenselianLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (x : finiteProjectiveGroupAlgebraGrothendieckGroup k G) :
    decompositionHom A K G
        ((projectiveGrothendieckScalarExtensionHom A K) x) =
      cartanHom k G x := by
  -- `e = (base change) ∘ (reduction equivalence)⁻¹`; the additive `d ∘ (base change) = c ∘ reduction`
  -- on `P₀[A](G)` is proved by lifting to the free abelian group and reducing each projective
  -- generator `[Q]ₚ₀` to the just-proved generator case `d([Q⊗K]₀) = c([Q̄]ₚ₀)`.
  have key : ∀ y : finiteProjectiveGroupAlgebraGrothendieckGroup A G,
      decompositionHom A K G ((projectiveGrothendieckBaseChangeHom K) y) =
        cartanHom k G ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) y) := by
    intro y
    refine QuotientAddGroup.induction_on y ?_
    intro a
    refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
    · simp
    · intro Q
      have hred :
          projectiveGrothendieckReductionEquiv (A := A) (G := G) [Q]ₚ₀ =
            [Q.residueFieldReduction]ₚ₀ := by
        change
          projectiveGrothendieckReductionHom (A := A) (G := G) [Q]ₚ₀ =
            [Q.residueFieldReduction]ₚ₀
        simpa using
          projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) Q
      calc
        decompositionHom A K G ((projectiveGrothendieckBaseChangeHom K) [Q]ₚ₀) =
            decompositionHom A K G [Q.scalarExtension K]₀ := by
              rw [projectiveGrothendieckBaseChangeHom_projectiveClass_eq]
        _ = cartanHom k G [Q.residueFieldReduction]ₚ₀ :=
              decompositionHom_projective_scalarExtension_class_eq_cartan_reduction_class_support
                (A := A) (K := K) (G := G) Q
        _ = cartanHom k G ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) [Q]ₚ₀) := by
              rw [hred]
    · intro a ha
      simpa using congrArg Neg.neg ha
    · intro a b ha hb
      simpa [map_add] using congrArg₂ (fun u v ↦ u + v) ha hb
  let y : finiteProjectiveGroupAlgebraGrothendieckGroup A G :=
    (projectiveGrothendieckReductionEquiv (A := A) (G := G)).symm x
  calc
    decompositionHom A K G ((projectiveGrothendieckScalarExtensionHom A K) x) =
        decompositionHom A K G ((projectiveGrothendieckBaseChangeHom K) y) := by
          simp [projectiveGrothendieckScalarExtensionHom_apply, y]
    _ = cartanHom k G ((projectiveGrothendieckReductionEquiv (A := A) (G := G)) y) := key y
    _ = cartanHom k G x := by simp [y]

end

end Representation
