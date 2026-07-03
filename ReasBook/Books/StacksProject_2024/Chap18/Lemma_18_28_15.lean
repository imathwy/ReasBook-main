import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import StacksProject_2024.Chap18.Lemma_18_28_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{u}}

/-- Restriction of scalars along `α`, written as the pushforward functor for the identity functor
on the underlying site. -/
abbrev restrictionAlong (α : 𝒪' ⟶ 𝒪) :
    SheafOfModules (ringSheaf J 𝒪) ⥤ SheafOfModules (ringSheaf J 𝒪') :=
  SheafOfModules.pushforward (ringedSiteStructureMap α)

/-- A square-zero reduction datum consists of a kernel ideal sheaf
`\mathcal I \hookrightarrow \mathcal O'`, a quotient presentation
`\mathcal F' \twoheadrightarrow \mathcal F`, and the sectionwise square-zero condition on
`\mathcal I`. Here `restrictionAlong α` is the same-site restriction-of-scalars functor attached
to `\alpha : \mathcal O' \to \mathcal O`. -/
structure IsSquareZeroReduction
    (α : 𝒪' ⟶ 𝒪)
    (𝓘 : SheafOfModules (ringSheaf J 𝒪'))
    (ι : 𝓘 ⟶ SheafOfModules.unit (ringSheaf J 𝒪'))
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (tensorTo : moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ) ⟶ ℱ')
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ) : Prop where
  /-- The ideal sheaf maps trivially to the quotient structure sheaf `\mathcal O`. -/
  ideal_comp :
    ι ≫ SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap α) = 0
  /-- The ideal sheaf is included as a submodule of `\mathcal O'`. -/
  ideal_mono : Mono ι
  /-- The sequence `\mathcal I \to \mathcal O' \to \mathcal O` is exact. -/
  ideal_exact :
    (ShortComplex.mk ι
      (SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap α))
      ideal_comp).Exact
  /-- The map `\mathcal O' \to \mathcal O` is an epimorphism of sheaves of modules. -/
  ideal_epi : Epi (SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap α))
  /-- Sectionwise, the kernel ideal squares to zero. -/
  square_zero :
    ∀ U : Cᵒᵖ, ∀ x y : 𝓘.val.obj U,
      ((show ↑((ringSheaf J 𝒪').obj.obj U) from ι.val.app U x) *
        (show ↑((ringSheaf J 𝒪').obj.obj U) from ι.val.app U y)) = 0
  /-- The tensor-action map and quotient map compose to zero. -/
  quot_comp : tensorTo ≫ quot = 0
  /-- The sequence `\mathcal I \otimes_{\mathcal O} \mathcal F \to \mathcal F' \to \mathcal F`
  is exact in the categorical formulation used in this file. -/
  quot_exact : (ShortComplex.mk tensorTo quot quot_comp).Exact
  /-- The quotient map `\mathcal F' \to \mathcal F` is an epimorphism. -/
  quot_epi : Epi quot

-- Proof sketch: for the forward implication, use Lemma `18.28.13` to descend flatness along the
-- quotient map `\mathcal O' \twoheadrightarrow \mathcal O`, and apply Lemma `18.28.9` to the
-- exact sequence defining `\mathcal F`. Conversely, test flatness of `\mathcal F'` on a monic
-- map, pass to the quotient exact sequence from `IsSquareZeroReduction`, and use flatness of
-- `\mathcal F` together with the assumed monomorphism of `tensorTo` to recover injectivity after
-- tensoring.
/-- Lemma 18.28.15: let `(\mathcal C, J)` be a site, let `\alpha : \mathcal O' \to \mathcal O` be
a surjection of sheaves of rings with square-zero kernel ideal sheaf `\mathcal I`, let
`\mathcal F'` be an `\mathcal O'`-module, and let `\mathcal F = \mathcal F'/\mathcal I\mathcal
F'`. In the categorical formulation used here, the quotient data are encoded by
`IsSquareZeroReduction α 𝓘 ι ℱ' ℱ tensorTo quot`, and the map `tensorTo` is the textbook map
`\mathcal I \otimes_{\mathcal O} \mathcal F \to \mathcal F'` after viewing `\mathcal F` as an
`\mathcal O'`-module by restriction of scalars. Then `\mathcal F'` is flat over `\mathcal O'` if
and only if `\mathcal F` is flat over `\mathcal O` and `tensorTo` is injective. -/
theorem isFlat_iff_isFlat_reduction_and_mono_tensor_of_squareZeroReduction
    (α : 𝒪' ⟶ 𝒪) [Epi α]
    (𝓘 : SheafOfModules (ringSheaf J 𝒪'))
    (ι : 𝓘 ⟶ SheafOfModules.unit (ringSheaf J 𝒪'))
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (tensorTo : moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ) ⟶ ℱ')
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ)
    (hsetup : IsSquareZeroReduction α 𝓘 ι ℱ' ℱ tensorTo quot) :
    IsFlat 𝒪' ℱ' ↔
      IsFlat 𝒪 ℱ ∧ Mono tensorTo := sorry

end SheafOfModules.RingedSite
