import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (p : GrothendieckTopology.Point J)
variable (ℱ : SheafOfModules (ringSheaf J 𝒪))

/-- The stalk functor on `\mathcal O`-modules at the point `p`, obtained by forgetting to sheaves
of abelian groups and then applying the point fiber functor. -/
abbrev point_stalk_functor :
    SheafOfModules (ringSheaf J 𝒪) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ p.sheafFiber

/-- Tensoring on the right by `ℱ` and then taking the stalk at `p`. This is the categorical form
of tensoring with the stalk `ℱ_p`. -/
abbrev point_tensor_stalk_functor :
    SheafOfModules (ringSheaf J 𝒪) ⥤ AddCommGrpCat.{u} :=
  sheafModuleTensorRightFunctor ℱ ⋙ point_stalk_functor 𝒪 p

/-- Flatness of `ℱ` at the point `p`, expressed as exactness of the tensor-then-stalk functor.
This packages the textbook statement that the stalk `ℱ_p` is flat over the stalk ring
`\mathcal O_p` in the available site-theoretic API. -/
def IsFlatAtPoint : Prop :=
  exactFunctor
    (SheafOfModules (ringSheaf J 𝒪))
    AddCommGrpCat.{u}
    (point_tensor_stalk_functor 𝒪 p ℱ)

-- Proof sketch: flatness of `ℱ` means tensoring with `ℱ` is exact on `\mathcal O`-modules. The
-- point fiber functor `p.sheafFiber` is exact on sheaves of abelian groups, so the composite
-- tensor-then-stalk functor is exact. This is the canonical categorical rendering of the
-- textbook claim that `ℱ_p` is a flat `\mathcal O_p`-module.
/-- Lemma 18.39.2: if `ℱ` is a flat `\mathcal O`-module on a ringed site and `p` is a point of
the site, then `ℱ` is flat at `p`, i.e. the stalkwise tensor functor at `p` is exact. This is
the canonical site-theoretic formulation of the statement that the stalk `ℱ_p` is a flat
`\mathcal O_p`-module. -/
theorem isFlatAtPoint_of_isFlat [IsFlat 𝒪 ℱ] :
    IsFlatAtPoint 𝒪 p ℱ := sorry

end
