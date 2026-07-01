import Mathlib
import stacks_project.Chap18.Lemma_18_33_2
import stacks_project.Chap18.Lemma_18_34_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}} (φ : O₁ ⟶ O₂)
variable {F G P Q : ringedSiteModuleCategory J O₂}

/-- The tensor product of two sheaves of modules over a sheaf of commutative rings, defined by
sheafifying the tensor product of their underlying presheaves. -/
noncomputable abbrev sheafModuleTensor
    {𝒪 : Sheaf J CommRingCat.{u}}
    (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪) :
    ringedSiteModuleCategory J 𝒪 :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj)).obj
    (show PresheafOfModules (ringSheaf J 𝒪).obj from
      PresheafOfModules.Monoidal.tensorObj
        (show PresheafOfModules (ringSheaf J 𝒪).obj from ℱ.val)
        (show PresheafOfModules (ringSheaf J 𝒪).obj from 𝒢.val))

/-- The cotangent-term `\Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F`
appearing on the left of the first principal-parts sequence. -/
noncomputable abbrev principalPartsCotangentTensor
    {O₁ O₂ : Sheaf J CommRingCat.{u}} (φ : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    ringedSiteModuleCategory J O₂ :=
  sheafModuleTensor (Ω(φ)) F

/-- A chosen first principal-parts module `P` for `F` fits into a principal-parts sequence when it
appears in a short exact sequence
`\Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F \to P \to \mathcal F`. -/
def IsPrincipalPartsSequence
    {O₁ O₂ : Sheaf J CommRingCat.{u}} (φ : O₁ ⟶ O₂)
    (F P : ringedSiteModuleCategory J O₂) : Prop :=
  ∃ (ι : principalPartsCotangentTensor φ F ⟶ P)
    (π : P ⟶ F) (hcomp : ι ≫ π = 0),
    (ShortComplex.mk ι π hcomp).ShortExact

-- Proof sketch: the composite
-- `(restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G ⟶ (restrictionAlong φ).obj Q`
-- is an order-one differential operator because `principalPartsDifferentialOperator hQ` is the
-- corepresenting first-order differential operator of `G`. Apply the representing property of
-- `hP` to this operator to obtain the unique induced `O₂`-linear map `P ⟶ Q`.
/-- A morphism of module sheaves induces a unique morphism between chosen first principal-parts
modules. -/
theorem principalPartsMap_existsUnique
    (hP : (differentialOperatorsFunctor φ F 1).CorepresentableBy P)
    (hQ : (differentialOperatorsFunctor φ G 1).CorepresentableBy Q)
    (f : F ⟶ G) :
    ∃! τ : P ⟶ Q,
      principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map τ =
        (restrictionAlong φ).map f ≫ principalPartsDifferentialOperator hQ := sorry

-- Proof sketch: apply the algebraic first principal-parts short exact sequence from
-- `Lemma 10.133.6` objectwise on the site, sheafify the resulting sequence, identify the left term
-- with `\Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F` using the
-- sheafified relative-differentials construction from `Lemma 18.33.4`, and identify the middle
-- term with the chosen universal first principal-parts sheaf using `Lemma 18.34.5`.
/-- Lemma 18.34.6: if `P` is a chosen first principal-parts sheaf of `F` relative to
`φ : O₁ ⟶ O₂`, then `P` fits into the canonical short exact sequence
`0 ⟶ \Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F ⟶ P ⟶ \mathcal F ⟶ 0`,
called the sequence of principal parts. -/
theorem principalPartsSequence_shortExact
    (F : ringedSiteModuleCategory J O₂)
    (P : ringedSiteModuleCategory J O₂)
    (hP : (differentialOperatorsFunctor φ F 1).CorepresentableBy P) :
    IsPrincipalPartsSequence φ F P := sorry

end
