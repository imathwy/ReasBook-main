import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite

noncomputable section

universe u w

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {I : Type w}
variable (p : I → GrothendieckTopology.Point J)
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (ℱ : SheafOfModules (ringSheaf J 𝒪))

-- Proof sketch: the forward implication is Lemma 18.39.2 applied pointwise. For the converse,
-- flatness means exactness of tensoring with `ℱ`, and exactness of the resulting short complexes
-- of abelian sheaves can be checked on the conservative family `p` by Lemma 18.14.4. The stalk
-- identification for tensor products from Lemma 18.26.2 matches those stalkwise exactness
-- conditions with `IsFlatAtPoint`.
/-- Lemma 18.39.3: a sheaf of `\mathcal O`-modules on a ringed site is flat if and only if it is
flat at every point of a conservative family, expressed here by exactness of tensoring with
`\mathcal F` followed by taking the fiber functor at each `p_i`; this is the site-theoretic form
of saying that each stalk `\mathcal F_{p_i}` is a flat `\mathcal O_{p_i}`-module. -/
theorem isFlat_iff_isFlatAtPoint_of_conservativeFamily
    (hp : (ofObj p).IsConservativeFamilyOfPoints) :
    IsFlat 𝒪 ℱ ↔
      ∀ i : I,
        exactFunctor
          (SheafOfModules (ringSheaf J 𝒪))
          AddCommGrpCat.{u}
          (sheafModuleTensorRightFunctor ℱ ⋙
            SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
              (p i).sheafFiber) := sorry

end
