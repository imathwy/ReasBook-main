import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Lemma_13_12_1
import StacksProject_2024.Chap24.Definition_24_13_1

open CategoryTheory
open ComplexShape
open DerivedCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

attribute [local instance] HasDerivedCategory.standard

local notation "DGAO" => @DifferentialGradedAlgebra C _ J _ 𝒪 _
local notation "DGModA" => @DifferentialGradedModule.moduleCategory C _ J _ 𝒪 _

namespace DifferentialGradedAlgebra

variable (𝒜 : DGAO)
variable [Abelian (DGModA 𝒜)]

local notation "QDGA" => @DerivedCategory.Q (DGModA 𝒜) _ inferInstance _
local notation "triangleOfSESδDGA" =>
  @DerivedCategory.triangleOfSESδ (DGModA 𝒜) _ inferInstance _

/- Lemma 24.27.1: let `(\mathcal C, \mathcal O)` be a ringed site and let `(\mathcal A, d)` be a
sheaf of differential graded algebras on it. The localization functor
`\textit{Mod}(\mathcal A, d) \to D(\mathcal A, d)` has a natural `δ`-functor structure.
In Chapter 24 this is exactly the canonical owner
`cochainComplexToDerivedDeltaFunctor`, specialized to cochain complexes in
`\mathrm{Mod}(\mathcal A, d)`. -/
recall CategoryTheory.cochainComplexToDerivedDeltaFunctor

/- The underlying functor of the canonical `δ`-functor is the canonical localization functor from
cochain complexes in `\mathrm{Mod}(\mathcal A, d)` to the derived category. -/
@[simp] theorem cochainComplexToDerivedDeltaFunctor_toFunctor :
    (CategoryTheory.cochainComplexToDerivedDeltaFunctor (DGModA 𝒜)).toFunctor =
      (QDGA : CochainComplex (DGModA 𝒜) ℤ ⥤ DerivedCategory (DGModA 𝒜)) :=
  rfl

/- The connecting morphism of the canonical `δ`-functor is the standard derived-category boundary
morphism attached to a short exact sequence, matching the Stacks formula `-p \circ q^{-1}` from
the preceding construction. -/
@[simp] theorem cochainComplexToDerivedDeltaFunctor_δ
    {S : ShortComplex (CochainComplex (DGModA 𝒜) ℤ)} (hS : S.ShortExact) :
    (CategoryTheory.cochainComplexToDerivedDeltaFunctor (DGModA 𝒜)).δ hS =
      triangleOfSESδDGA hS :=
  rfl

end DifferentialGradedAlgebra
end
end SheafOfModules.RingedSite
