import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap24.Definition_24_4_1

open CategoryTheory Limits
open scoped SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

-- Semantic search note: `lean_leansearch` suggested sheaf/module evaluation precedents such as
-- `SheafOfModules.evaluationPreservesLimitsOfShape` and
-- `PresheafOfModules.evaluation_preservesColimit`; the source-facing owner here remains
-- `Mod(𝒜)`, with degree evaluation as the needed bridge to `Mod(𝒪)`.

namespace GradedModuleSheaf

/-- The degree-`n` evaluation functor on graded `\mathcal A`-modules. -/
def evaluation (𝒜 : GradedAlgebraSheaf 𝒪) (n : ℤ) :
    Mod(𝒜) ⥤ Mod(𝒪) :=
  GradedModuleSheaf.forgetToGraded 𝒜 ⋙ CategoryTheory.GradedObject.eval n

/-- Lemma 24.4.2 (1): the functor `\mathcal M \mapsto \mathcal M^n` from graded
`\mathcal A`-modules to `\mathcal O`-modules commutes with all limits. -/
instance evaluationPreservesLimits (𝒜 : GradedAlgebraSheaf 𝒪) (n : ℤ) :
    PreservesLimits (evaluation 𝒜 n) := sorry

/-- Lemma 24.4.2 (2): the functor `\mathcal M \mapsto \mathcal M^n` from graded
`\mathcal A`-modules to `\mathcal O`-modules commutes with all colimits. -/
instance evaluationPreservesColimits (𝒜 : GradedAlgebraSheaf 𝒪) (n : ℤ) :
    PreservesColimits (evaluation 𝒜 n) := sorry

end GradedModuleSheaf

variable (𝒜 : GradedAlgebraSheaf 𝒪)

/- Lemma 24.4.2 (1): the category `\mathrm{Mod}(\mathcal A)` of graded `\mathcal A`-modules is
abelian. -/
recall Abelian

/- Lemma 24.4.2 (2): the category `\mathrm{Mod}(\mathcal A)` has arbitrary direct sums, i.e.
the canonical coproduct structure `HasCoproducts`. -/
recall HasCoproducts

/- Lemma 24.4.2 (3): the category `\mathrm{Mod}(\mathcal A)` has arbitrary colimits. -/
recall HasColimits

/- Lemma 24.4.2 (4): filtered colimits in `\mathrm{Mod}(\mathcal A)` are exact; canonically,
`Mod(𝒜)` satisfies `AB5`. -/
recall AB5

/- Lemma 24.4.2 (5): the category `\mathrm{Mod}(\mathcal A)` has arbitrary products. -/
recall HasProducts

/- Lemma 24.4.2 (6): the category `\mathrm{Mod}(\mathcal A)` has arbitrary limits. -/
recall HasLimits

end

end SheafOfModules.RingedSite
