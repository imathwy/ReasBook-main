import Mathlib
import stacks_project.Chap18.Definition_18_43_1
import stacks_project.Chap07.Definition_7_15_1_Topoi

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped MorphismOfTopoiIn

noncomputable section

universe u₁ u₂ u₃ u₄ u₅ v₁ v₂ v₃ w

namespace CategoryTheory

/- Domain-style sampling for Lemma 18.43.2:
- primary domain: inverse image for morphisms of topoi and locally constant sheaves.
- sampled owner/bridge declarations:
  `Sheaf.IsLocallyConstant`,
  the inverse-image notation `f⁻¹`,
  `sheaf_pullback_forget`,
  `MorphismOfTopoiIn.presentationFunctor_inverseImageIso`.
- best owner abstraction: the source-facing theorem should be stated directly for the canonical
  inverse-image functor `f⁻¹` of a morphism of topoi; forget-compatibility for algebraic-valued
  sheaves is derived bridge data.
- primitive data: a morphism of topoi `f`, a sheaf `𝒢`, and local constancy of `𝒢`.
- derived API: the set-valued inverse image `f⁻¹ 𝒢` is locally constant, plus the companion
  bridge theorem for `A`-valued inverse image functors commuting with the forgetful functor. -/

namespace Sheaf

/-- Local constancy is invariant under isomorphism. -/
theorem isLocallyConstant_of_iso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C}
    [HasWeakSheafify J D] [∀ U : C, HasWeakSheafify (J.over U) D]
    {F G : Sheaf J D} (e : F ≅ G) [Sheaf.IsLocallyConstant F] :
    Sheaf.IsLocallyConstant G := sorry

end Sheaf

-- Proof sketch: use the compatibility isomorphism `hforget` to identify the underlying
-- set-valued sheaf of `inverseImageA.obj G` with the inverse image of the underlying set-valued
-- sheaf of `G`, then transport local constancy across this isomorphism.
private theorem inverseImageA_isLocallyConstant_of_forget
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {A : Type u₃} [Category.{v₃} A]
    {FA : A → A → Type u₄} {CA : A → Type u₅}
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [JC.HasSheafCompose (forget A)] [JD.HasSheafCompose (forget A)]
    [HasWeakSheafify JC (Type u₅)] [HasWeakSheafify JD (Type u₅)]
    [∀ X : C, HasWeakSheafify (JC.over X) (Type u₅)]
    [∀ Y : D, HasWeakSheafify (JD.over Y) (Type u₅)]
    (f : MorphismOfTopoiIn JD JC)
    (inverseImageA : Sheaf JD A ⥤ Sheaf JC A)
    (hforget :
      inverseImageA ⋙ sheafCompose JC (forget A) ≅
        sheafCompose JD (forget A) ⋙ f⁻¹)
    (𝒢 : Sheaf JD A)
    [Sheaf.IsLocallyConstant ((sheafCompose JD (forget A)).obj 𝒢)] :
    Sheaf.IsLocallyConstant ((sheafCompose JC (forget A)).obj (inverseImageA.obj 𝒢)) := sorry

-- Proof sketch: this is the direct set-valued specialization of the preceding forget-compatibility
-- bridge, using that `forget (Type w)` is definitionally the identity functor and hence
-- `sheafCompose _ (forget (Type w))` is definitionally the identity on set-valued sheaves.
/-- Lemma 18.43.2: if `f : \mathit{Sh}(\mathcal C) \to \mathit{Sh}(\mathcal D)` is a morphism of
topoi and `\mathcal G` is a locally constant sheaf of sets on `\mathcal D`, then its inverse
image `f^{-1}\mathcal G` is a locally constant sheaf of sets on `\mathcal C`. -/
theorem inverseImage_isLocallyConstant
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [HasWeakSheafify JC (Type w)] [HasWeakSheafify JD (Type w)]
    [∀ X : C, HasWeakSheafify (JC.over X) (Type w)]
    [∀ Y : D, HasWeakSheafify (JD.over Y) (Type w)]
    (f : MorphismOfTopoiIn JD JC)
    (𝒢 : Sheaf JD (Type w))
    [Sheaf.IsLocallyConstant 𝒢] :
    Sheaf.IsLocallyConstant ((f⁻¹).obj 𝒢) := by
  let _ : Sheaf.IsLocallyConstant ((sheafCompose JD (forget (Type w))).obj 𝒢) := by
    simpa using (inferInstance : Sheaf.IsLocallyConstant 𝒢)
  simpa using
    inverseImageA_isLocallyConstant_of_forget f (f⁻¹) (Iso.refl _) 𝒢

/-- Companion bridge theorem: if forgetting a sheaf `\mathcal G` in a concrete algebraic
category on `\mathcal D` yields a locally constant sheaf of sets, then after pulling back along a
morphism of topoi `f : \mathit{Sh}(\mathcal C) \to \mathit{Sh}(\mathcal D)`, the underlying
set-valued sheaf of the chosen `A`-valued inverse image is again locally constant. -/
theorem inverseImage_isLocallyConstant_of_forget
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {A : Type u₃} [Category.{v₃} A]
    {FA : A → A → Type u₄} {CA : A → Type u₅}
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [JC.HasSheafCompose (forget A)] [JD.HasSheafCompose (forget A)]
    [HasWeakSheafify JC (Type u₅)] [HasWeakSheafify JD (Type u₅)]
    [∀ X : C, HasWeakSheafify (JC.over X) (Type u₅)]
    [∀ Y : D, HasWeakSheafify (JD.over Y) (Type u₅)]
    (f : MorphismOfTopoiIn JD JC)
    (inverseImageA : Sheaf JD A ⥤ Sheaf JC A)
    (hforget :
      inverseImageA ⋙ sheafCompose JC (forget A) ≅
        sheafCompose JD (forget A) ⋙ f.inverseImage)
    (𝒢 : Sheaf JD A)
    [Sheaf.IsLocallyConstant ((sheafCompose JD (forget A)).obj 𝒢)] :
    Sheaf.IsLocallyConstant ((sheafCompose JC (forget A)).obj (inverseImageA.obj 𝒢)) :=
  inverseImageA_isLocallyConstant_of_forget f inverseImageA hforget 𝒢

end CategoryTheory
