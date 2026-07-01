import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap17.Definition_17_11_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u w

namespace SheafOfModules

/- Domain-style sampling for Lemma 17.22.7:
- primary domain: internal Hom in the closed monoidal category of sheaves of modules over a sheaf
  of rings, together with its interaction with filtered colimits;
- sampled owner declarations:
  `colimit.post`,
  `ihom`,
  `SheafOfModules.IsFinitePresentation`;
- best owner abstraction: the canonical comparison morphism is the generic categorical owner
  `colimit.post`, specialized here to the right adjoint `ihom ℱ`;
- primitive data: a ring-valued sheaf `𝒪`, a module sheaf `ℱ`, and a diagram `𝒢`;
- derived API: the specialized `colimit.post 𝒢 (ihom ℱ)` morphism and the finitely presented
  isomorphism theorem.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization in `AlgebraicGeometry.RingedSpace`;
- `core/canonical`: the owner-level declarations below in `SheafOfModules`;
- `bridge/view`: specialization along `𝒪 = (RingedSpace.ringCatSheaf X)`. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J RingCat.{u}}
variable {Λ : Type w} [SmallCategory Λ]
variable [MonoidalCategory (SheafOfModules 𝒪)] [MonoidalClosed (SheafOfModules 𝒪)]

-- Proof sketch: finite presentation is local on the ringed site, so after restricting to a cover
-- one may choose a finite free presentation of `ℱ`. Internal Hom from such a presentation is the
-- kernel of a morphism between finite direct sums, and filtered colimits commute with those finite
-- sums and preserve exactness, forcing the canonical comparison morphism to be an isomorphism.
/-- If `ℱ` is a finitely presented `\mathcal O`-module and `𝒢` is a filtered diagram of
`\mathcal O`-modules, then the canonical morphism
`colim_λ ℋom_𝒪(ℱ, 𝒢_λ) ⟶ ℋom_𝒪(ℱ, colim_λ 𝒢_λ)` is an isomorphism. -/
theorem isIso_internalHomColimitComparison_of_isFinitePresentation
    [IsFiltered Λ]
    (ℱ : SheafOfModules 𝒪) [ℱ.IsFinitePresentation]
    (𝒢 : Λ ⥤ SheafOfModules 𝒪)
    [HasColimit 𝒢] [HasColimit (𝒢 ⋙ ihom ℱ)] :
    IsIso (colimit.post 𝒢 (ihom ℱ)) := sorry

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {Λ : Type w} [SmallCategory Λ] [IsFiltered Λ]
    [MonoidalCategory (RingedSpace.Modules X)] [MonoidalClosed (RingedSpace.Modules X)]
variable (ℱ : RingedSpace.Modules X) [ℱ.IsFinitePresentation]
variable (𝒢 : Λ ⥤ RingedSpace.Modules X)
  [HasColimit 𝒢] [HasColimit (𝒢 ⋙ ihom ℱ)]

/- Lemma 17.22.7, source-facing bridge/view specialization: for a ringed space `X`, the
comparison morphism
`colim_\lambda \mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G_\lambda) ⟶
\mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F, colim_\lambda \mathcal G_\lambda)`
is covered exactly by
`SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation`
on `(RingedSpace.Modules X)`. -/
#check (SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation ℱ 𝒢 :
  IsIso (colimit.post 𝒢 (ihom ℱ)))

end AlgebraicGeometry.RingedSpace
