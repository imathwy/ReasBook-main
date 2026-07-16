import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import StacksProject_2024.stacks_project.Chap24.Lemma_24_25_10
import StacksProject_2024.stacks_project.Chap24.Lemma_24_25_12

open CategoryTheory
open ComplexShape
open DerivedCategory

noncomputable section

universe u v uGr vGr

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite
namespace DifferentialGradedAlgebra

section

variable {X : RingedSite.{u, v}} (𝒜 : DifferentialGradedAlgebra X)
variable {GrModA : Type uGr} [Category.{vGr} GrModA] [Abelian GrModA]

local notation "KQ" => HomotopyCategory.quotient 𝒜.moduleCat (up ℤ)

-- Semantic search note: `lean_leansearch` returned the canonical derived-category comparison
-- theorem `CochainComplex.IsKInjective.Qh_map_bijective`; the source-facing specialization below
-- keeps the Chapter 24 quasi-isomorphism `N ⟶ I` and the graded-injective hypothesis from
-- `Lemma_24_25_10`.

/-- Lemma 24.26.7: let `(\mathcal C, \mathcal O)` be a ringed site, let `(\mathcal A, d)` be a
sheaf of differential graded algebras on it, let `\mathcal M` and `\mathcal N` be differential
graded `\mathcal A`-modules, and let `\mathcal N \to \mathcal I` be a quasi-isomorphism with
`\mathcal I` graded injective and K-injective. In the canonical homotopy/derived-category
formalization, morphisms from `\mathcal M` to `\mathcal N` in `D(\mathcal A, d)` are therefore in
bijection with morphisms from `\mathcal M` to `\mathcal I` in
`K(\textit{Mod}(\mathcal A, d))`, via postcomposition with the inverse of the derived image of the
chosen quasi-isomorphism `\mathcal N \to \mathcal I`. -/
theorem derivedHomBijectiveOfQuasiIsoToKInjectiveOfIsGradedInjective
    (forgetToGraded : CochainComplex 𝒜.moduleCat ℤ ⥤ GrModA)
    {M N I : CochainComplex 𝒜.moduleCat ℤ} (i : N ⟶ I)
    [QuasiIso i] [I.IsKInjective]
    [DifferentialGradedModule.IsGradedInjective forgetToGraded I] :
    Function.Bijective
      (fun f : (KQ).obj M ⟶ (KQ).obj I ↦
        (DerivedCategory.quotientCompQhIso 𝒜.moduleCat).inv.app M ≫
          DerivedCategory.Qh.map f ≫
            (DerivedCategory.quotientCompQhIso 𝒜.moduleCat).hom.app I ≫
              inv (DerivedCategory.Q.map i)) := sorry

end

end DifferentialGradedAlgebra
end RingedSite
