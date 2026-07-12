import Mathlib
import StacksProject_2024.Chap10.Lemma_10_133_6
import StacksProject_2024.Chap18.Lemma_18_33_2
import StacksProject_2024.Chap18.Lemma_18_33_4
import StacksProject_2024.Chap18.Lemma_18_34_3
import StacksProject_2024.Chap18.Lemma_18_34_5

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
        (restrictionAlong φ).map f ≫ principalPartsDifferentialOperator hQ := by
  -- Proof comment: the desired morphism is the factorization of the composite order-one
  -- differential operator through the chosen principal-parts object `P`.
  refine principalParts_representsDifferentialOperators (hP := hP) Q
    ((restrictionAlong φ).map f ≫ principalPartsDifferentialOperator hQ) ?_
  -- Proof comment: `f` contributes order `0`, while the universal operator of `hQ` has order `1`.
  simpa [Nat.zero_add] using
    isDifferentialOperatorOfOrder_comp (φ := φ)
      (D := (restrictionAlong φ).map f)
      (D' := principalPartsDifferentialOperator hQ)
      (isDifferentialOperatorOfOrder_restrictionAlong_map (φ := φ) f)
      (principalPartsDifferentialOperator_isDifferentialOperatorOfOrder hQ)

/-- Helper for Lemma 18.34.6: two chosen first principal-parts objects corepresenting the same
functor are canonically isomorphic. -/
theorem principalPartsIsoOfCorepresentable
    (hP : (differentialOperatorsFunctor φ F 1).CorepresentableBy P)
    (hQ : (differentialOperatorsFunctor φ F 1).CorepresentableBy Q) :
    ∃ e : P ≅ Q,
      principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map e.hom =
        principalPartsDifferentialOperator hQ := by
  -- Proof comment: the identity differential operator on `F` induces comparison maps in both
  -- directions, and uniqueness forces the two composites to be identities.
  rcases principalPartsMap_existsUnique (φ := φ) (hP := hP) (hQ := hQ) (𝟙 F) with
    ⟨τ, hτ, _⟩
  rcases principalPartsMap_existsUnique (φ := φ) (hP := hQ) (hQ := hP) (𝟙 F) with
    ⟨σ, hσ, _⟩
  have hτσ :
      τ ≫ σ = 𝟙 P := by
    rcases principalPartsMap_existsUnique (φ := φ) (hP := hP) (hQ := hP) (𝟙 F) with
      ⟨_, _, hu_unique⟩
    have hτσ_fac :
        principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map (τ ≫ σ) =
          (restrictionAlong φ).map (𝟙 F) ≫ principalPartsDifferentialOperator hP := by
      -- Proof comment: the comparison composite still factors the identity differential
      -- operator because the intermediate corepresenting object `Q` cancels out.
      calc
        principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map (τ ≫ σ) =
            (principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map τ) ≫
              (restrictionAlong φ).map σ := by
          simp [Functor.map_comp, Category.assoc]
        _ = principalPartsDifferentialOperator hQ ≫ (restrictionAlong φ).map σ := by
          simpa using congrArg (fun f ↦ f ≫ (restrictionAlong φ).map σ) hτ
        _ = (restrictionAlong φ).map (𝟙 F) ≫ principalPartsDifferentialOperator hP := by
          simpa using hσ
    have hId_fac :
        principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map (𝟙 P) =
          (restrictionAlong φ).map (𝟙 F) ≫ principalPartsDifferentialOperator hP := by
      simp
    exact (hu_unique _ hτσ_fac).trans (hu_unique _ hId_fac).symm
  have hστ :
      σ ≫ τ = 𝟙 Q := by
    rcases principalPartsMap_existsUnique (φ := φ) (hP := hQ) (hQ := hQ) (𝟙 F) with
      ⟨_, _, hu_unique⟩
    have hστ_fac :
        principalPartsDifferentialOperator hQ ≫ (restrictionAlong φ).map (σ ≫ τ) =
          (restrictionAlong φ).map (𝟙 F) ≫ principalPartsDifferentialOperator hQ := by
      -- Proof comment: the mirror composite on `Q` factors the identity differential operator in
      -- exactly the same way.
      calc
        principalPartsDifferentialOperator hQ ≫ (restrictionAlong φ).map (σ ≫ τ) =
            (principalPartsDifferentialOperator hQ ≫ (restrictionAlong φ).map σ) ≫
              (restrictionAlong φ).map τ := by
          simp [Functor.map_comp, Category.assoc]
        _ = principalPartsDifferentialOperator hP ≫ (restrictionAlong φ).map τ := by
          simpa using congrArg (fun f ↦ f ≫ (restrictionAlong φ).map τ) hσ
        _ = (restrictionAlong φ).map (𝟙 F) ≫ principalPartsDifferentialOperator hQ := by
          simpa using hτ
    have hId_fac :
        principalPartsDifferentialOperator hQ ≫ (restrictionAlong φ).map (𝟙 Q) =
          (restrictionAlong φ).map (𝟙 F) ≫ principalPartsDifferentialOperator hQ := by
      simp
    exact (hu_unique _ hστ_fac).trans (hu_unique _ hId_fac).symm
  refine ⟨⟨τ, σ, hτσ, hστ⟩, ?_⟩
  simpa using hτ

/-- Helper for Lemma 18.34.6: transporting the middle term of a principal-parts sequence across
an isomorphism preserves short exactness. -/
theorem isPrincipalPartsSequence_of_iso
    (e : P ≅ Q) :
    IsPrincipalPartsSequence φ F Q → IsPrincipalPartsSequence φ F P := by
  intro hQseq
  rcases hQseq with ⟨ιQ, πQ, hcompQ, hshortQ⟩
  let ιP : principalPartsCotangentTensor φ F ⟶ P := ιQ ≫ e.inv
  let πP : P ⟶ F := e.hom ≫ πQ
  have hcompP : ιP ≫ πP = 0 := by
    -- Proof comment: after inserting `e.inv ≫ e.hom = 𝟙`, the transported composite is the
    -- original zero composite.
    simpa [ιP, πP, Category.assoc] using hcompQ
  let eSeq :
      ShortComplex.mk ιQ πQ hcompQ ≅ ShortComplex.mk ιP πP hcompP :=
    ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _)
      (by simp [ιP, Category.assoc])
      (by simp [πP, Category.assoc])
  refine ⟨ιP, πP, hcompP, ?_⟩
  -- Proof comment: short exactness is invariant under isomorphism of short complexes.
  exact ShortComplex.shortExact_of_iso eSeq hshortQ

/-- Helper for Lemma 18.34.6: the explicit first principal-parts sheaf from Lemma 18.34.5, still
living over the sheafified owner `O₂^#`. -/
private noncomputable abbrev sheafifiedCanonicalPrincipalParts :
    ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat.{u}).obj O₂.val) :=
  P^{1}_[φ.hom](F.val)

/-- Helper for Lemma 18.34.6: the sheafification counit identifies the sheafified owner `O₂^#`
with the original sheaf `O₂`. -/
private noncomputable abbrev currentOwnerIso :
    ((presheafToSheaf J CommRingCat.{u}).obj O₂.val) ≅ O₂ :=
  (asIso (CategoryTheory.sheafificationAdjunction J CommRingCat.{u}).counit).app O₂

/-- Helper for Lemma 18.34.6: transport the explicit first principal-parts sheaf from Lemma
18.34.5 back to the current owner `O₂` by restriction of scalars along the sheafification counit.
-/
private noncomputable abbrev currentOwnerCanonicalPrincipalParts :
    ringedSiteModuleCategory J O₂ :=
  (restrictionAlong (currentOwnerIso (J := J) (O₂ := O₂)).inv.hom).obj
    (sheafifiedCanonicalPrincipalParts (J := J) (φ := φ) (F := F))

/-- Helper for Lemma 18.34.6: sheafifying an already-sheaf `O₂`-module and then viewing it over
the sheafified owner agrees with restricting scalars along the sheafification counit. -/
private noncomputable def currentOwnerModuleSheafificationIso
    (G : ringedSiteModuleCategory J O₂) :
    ((PresheafOfModules.moduleSheafification J O₂.val).obj G.val) ≅
      ((restrictionAlong (currentOwnerIso (J := J) (O₂ := O₂)).hom).obj G) := by
  -- Proof comment: this is the counit of the module-sheafification adjunction along the
  -- canonical map `O₂.val ⟶ O₂^#`, evaluated on `G` after rewriting its target owner as `O₂^#`.
  let e := asIso
    (PresheafOfModules.sheafificationAdjunction
      (PresheafOfModules.sheafificationRingMap (J := J) O₂.val)).counit
  simpa [currentOwnerIso, SheafOfModules.RingedSite.restrictionAlong,
    SheafOfModules.RingedSite.ringSheafMap] using
    (e.app ((restrictionAlong (currentOwnerIso (J := J) (O₂ := O₂)).hom).obj G))

/-- Helper for Lemma 18.34.6: the section algebra on `O₂(X)` induced by `φ`. -/
private abbrev principalPartsSectionAlgebra
    (φ : O₁ ⟶ O₂) (X : Cᵒᵖ) :
    Algebra (O₁.obj.obj X) (O₂.obj.obj X) :=
  (φ.hom.app X).hom.toAlgebra

/-- Helper for Lemma 18.34.6: the restricted `O₁(X)`-module structure on `F(X)`. -/
private abbrev principalPartsSectionModule
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (X : Cᵒᵖ) :
    Module (O₁.obj.obj X) (F.val.obj X) :=
  Module.compHom (F.val.obj X) (φ.hom.app X).hom

/-- Helper for Lemma 18.34.6: the sectionwise scalar tower
`O₁(X) → O₂(X) → F(X)`. -/
private abbrev principalPartsSectionIsScalarTower
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (X : Cᵒᵖ) :
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := principalPartsSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (F.val.obj X) := principalPartsSectionModule φ F X
    IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
  by
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := principalPartsSectionAlgebra φ X
    letI : Module (O₁.obj.obj X) (F.val.obj X) := principalPartsSectionModule φ F X
    exact IsScalarTower.of_compHom (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X)

/-- Helper for Lemma 18.34.6: the sectionwise first principal-parts row is the algebraic short
exact sequence from Lemma 10.133.6. -/
private theorem principalPartsSequence_sectionwiseShortExact
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (X : Cᵒᵖ) :
    (Module.principalPartsSequence
      (R := O₁.obj.obj X) (S := O₂.obj.obj X) (M := F.val.obj X)).ShortExact := by
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := principalPartsSectionAlgebra φ X
  letI : Module (O₁.obj.obj X) (F.val.obj X) := principalPartsSectionModule φ F X
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (F.val.obj X) :=
    principalPartsSectionIsScalarTower φ F X
  -- Proof comment: after installing the sectionwise algebra and scalar-tower instances, the
  -- target row is exactly the algebraic principal-parts short exact sequence.
  simpa using
    (principal_parts_sequence_shortExact
      (R := O₁.obj.obj X) (S := O₂.obj.obj X) (M := F.val.obj X))

/-- Helper for Lemma 18.34.6: the explicit sheafified first principal-parts sheaf from Lemma
18.34.5 corepresents order-one differential operators over the sheafified owner. -/
private theorem sheafifiedCanonicalPrincipalPartsCorepresentable :
    (differentialOperatorsFunctor
      ((presheafToSheaf J CommRingCat.{u}).map φ.hom)
      ((PresheafOfModules.moduleSheafification J O₂.val).obj F.val) 1).CorepresentableBy
      (sheafifiedCanonicalPrincipalParts (J := J) (φ := φ) (F := F)) := by
  -- Proof comment: this is exactly the public corepresentability witness established in
  -- Lemma 18.34.5 for the explicit sheafified principal-parts sheaf.
  simpa [sheafifiedCanonicalPrincipalParts] using
    (principalParts_is_principal_parts_module_of_order
      (J := J) (φ := φ.hom) (F := F.val) 1)

-- Proof sketch: apply the algebraic first principal-parts short exact sequence from
-- `Lemma 10.133.6` objectwise on the site, sheafify the resulting sequence, identify the left term
-- with `\Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F` using the
-- sheafified relative-differentials construction from `Lemma 18.33.4`, and identify the middle
-- term with the chosen universal first principal-parts sheaf using `Lemma 18.34.5`.
/-- Lemma 18.34.6: if `P` is a chosen first principal-parts sheaf of `F` relative to
`φ : O₁ ⟶ O₂`, then `P` fits into the canonical short exact sequence
`0 ⟶ \Omega_{\mathcal O_2/\mathcal O_1} \otimes_{\mathcal O_2} \mathcal F ⟶ P ⟶ \mathcal F ⟶ 0`,
called the sequence of principal parts. -/
@[stacks 09CW]
theorem principalPartsSequence_shortExact
    (F : ringedSiteModuleCategory J O₂)
    (P : ringedSiteModuleCategory J O₂)
    (hP : (differentialOperatorsFunctor φ F 1).CorepresentableBy P) :
    IsPrincipalPartsSequence φ F P := by
  let Q := currentOwnerCanonicalPrincipalParts (J := J) (φ := φ) (F := F)
  have hQ :
      (differentialOperatorsFunctor φ F 1).CorepresentableBy Q := by
    -- Proof comment: the explicit `18.34.5` model already corepresents the sheafified functor;
    -- the remaining task is to transport that witness across the sheafification counit on the
    -- owner and on `F`.
    --
    -- TODO: use `Functor.CorepresentableBy.ofIso` together with the sheafification counit
    -- comparison to move `sheafifiedCanonicalPrincipalPartsCorepresentable` back to the current
    -- owner `O₂`.
    sorry
  have hQseq : IsPrincipalPartsSequence φ F Q := by
    -- Proof comment: once the same counit transport is applied to the canonical sheafified row,
    -- the already-proved `isPrincipalPartsSequence_of_iso` will move the exact sequence to the
    -- current owner `O₂`.
    --
    -- TODO: first prove the short exact sequence for the explicit sheafified row from
    -- `Lemma 18.34.5`, then transport that row along `currentOwnerIso`.
    sorry
  rcases principalPartsIsoOfCorepresentable (φ := φ) (F := F) hP hQ with ⟨e, _⟩
  -- Proof comment: every chosen first principal-parts sheaf is uniquely isomorphic to the
  -- canonical transported one, so the short exact sequence carries over along that isomorphism.
  exact isPrincipalPartsSequence_of_iso (φ := φ) (F := F) e hQseq

end
