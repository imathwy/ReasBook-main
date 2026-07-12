import Mathlib
import StacksProject_2024.Chap06.Basis_extension_preserves_stalks
import StacksProject_2024.Chap06.Lemma_6_30_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open BasisSiteSheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}} {B : Set (Opens X)} {hB : Opens.IsBasis B}

local notation "BasisRingSheaf" => BasisSiteSheaf RingCat B hB

private instance basisOpenInclusion_isContinuous :
    Functor.IsContinuous (basisOpenInclusion B)
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X) := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  exact
    Functor.IsCoverDense.isContinuous
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X) (basisOpenInclusion B)
      (Functor.inducedTopology_coverPreserving (basisOpenInclusion B)
        (Opens.grothendieckTopology X))

private abbrev basisSiteSheafComparisonEquiv {C : Type (u + 1)} [Category.{u} C]
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion B).op) C] :
    BasisSiteSheaf C B hB ≌ TopCat.Sheaf C X := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  change Sheaf (basisGrothendieckTopology B hB) C ≌ TopCat.Sheaf C X
  exact (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
    (Opens.grothendieckTopology X) C

private abbrev basisRingSheafExtensionUnit
    (𝒪 : BasisRingSheaf) :
    𝒪 ⟶
      ((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj
        𝒪.extend :=
  (basisSiteSheafComparisonEquiv.unitIso.app 𝒪).hom

private noncomputable abbrev basisModuleSheafExtensionPullback
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪) :
    SheafOfModules 𝒪.extend :=
  (SheafOfModules.pullback (basisRingSheafExtensionUnit 𝒪)).obj ℱ

private noncomputable abbrev basisModuleSheafExtensionPullbackUnitHom
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪) :
    ℱ ⟶
      (SheafOfModules.pushforward (basisRingSheafExtensionUnit 𝒪)).obj
        (basisModuleSheafExtensionPullback 𝒪 ℱ) :=
  (SheafOfModules.pullbackPushforwardAdjunction
    (basisRingSheafExtensionUnit 𝒪)).unit.app ℱ

-- Proof sketch: `basisRingSheafExtensionUnit 𝒪` is the unit isomorphism of the dense-subsite
-- comparison equivalence for ring-valued sheaves. Pullback along this isomorphism yields an
-- equivalence on module sheaves, so the adjunction unit is an isomorphism.
private instance basisModuleSheafExtensionPullbackUnitHom_isIso
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪) :
    IsIso (basisModuleSheafExtensionPullbackUnitHom 𝒪 ℱ) := sorry

private noncomputable def basisModuleSheafExtensionPullback_toSheafIso
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪) :
    BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj ℱ) ≅
      (SheafOfModules.toSheaf 𝒪.extend).obj
        (basisModuleSheafExtensionPullback 𝒪 ℱ) := by
  let e : BasisSiteSheaf AddCommGrpCat.{u} B hB ≌ TopCat.Sheaf AddCommGrpCat.{u} X :=
    basisSiteSheafComparisonEquiv
  let hℱ :
      (SheafOfModules.toSheaf 𝒪).obj ℱ ≅
        e.inverse.obj
          ((SheafOfModules.toSheaf 𝒪.extend).obj
            (basisModuleSheafExtensionPullback 𝒪 ℱ)) := by
    change (SheafOfModules.toSheaf 𝒪).obj ℱ ≅
        (SheafOfModules.toSheaf 𝒪).obj
          ((SheafOfModules.pushforward (basisRingSheafExtensionUnit 𝒪)).obj
            (basisModuleSheafExtensionPullback 𝒪 ℱ))
    exact asIso ((SheafOfModules.toSheaf 𝒪).map
      (basisModuleSheafExtensionPullbackUnitHom 𝒪 ℱ))
  exact ((e.counitIso.app _).symm ≪≫ e.functor.mapIso hℱ.symm).symm

private noncomputable def basisModuleSheafExtensionVal
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪) :
    PresheafOfModules 𝒪.extend.obj :=
  let e := basisModuleSheafExtensionPullback_toSheafIso 𝒪 ℱ
  let G := BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj ℱ)
  let e' := (TopCat.Sheaf.forget AddCommGrpCat X).mapIso e
  letI :
      ∀ U : (Opens X)ᵒᵖ,
        Module (𝒪.extend.presheaf.obj U) (G.presheaf.obj U) :=
    fun U ↦ by
      letI :
          Module (𝒪.extend.presheaf.obj U)
            (((TopCat.Sheaf.forget AddCommGrpCat X).obj
                ((SheafOfModules.toSheaf 𝒪.extend).obj
                  (basisModuleSheafExtensionPullback 𝒪 ℱ))).obj U) := by
        change Module (𝒪.extend.presheaf.obj U)
          ((basisModuleSheafExtensionPullback 𝒪 ℱ).val.obj U)
        infer_instance
      exact
        (Iso.addCommGroupIsoToAddEquiv (e'.app U)).module (𝒪.extend.presheaf.obj U)
  PresheafOfModules.ofPresheaf G.presheaf fun {U V} f r m ↦ by
    let hU := Iso.addCommGroupIsoToAddEquiv (e'.app U)
    let hV := Iso.addCommGroupIsoToAddEquiv (e'.app V)
    letI :
        Module (𝒪.extend.obj.obj U)
          (((TopCat.Sheaf.forget AddCommGrpCat X).obj
              (BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj ℱ))).obj U) := by
      change Module (𝒪.extend.presheaf.obj U) (G.presheaf.obj U)
      infer_instance
    letI :
        Module (𝒪.extend.obj.obj V)
          (((TopCat.Sheaf.forget AddCommGrpCat X).obj
              (BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj ℱ))).obj V) := by
      change Module (𝒪.extend.presheaf.obj V) (G.presheaf.obj V)
      infer_instance
    letI :
        Module (𝒪.extend.presheaf.obj U)
          (((TopCat.Sheaf.forget AddCommGrpCat X).obj
              ((SheafOfModules.toSheaf 𝒪.extend).obj
                (basisModuleSheafExtensionPullback 𝒪 ℱ))).obj U) := by
      change Module (𝒪.extend.presheaf.obj U)
        ((basisModuleSheafExtensionPullback 𝒪 ℱ).val.obj U)
      infer_instance
    letI :
        Module (𝒪.extend.presheaf.obj V)
          (((TopCat.Sheaf.forget AddCommGrpCat X).obj
              ((SheafOfModules.toSheaf 𝒪.extend).obj
                (basisModuleSheafExtensionPullback 𝒪 ℱ))).obj V) := by
      change Module (𝒪.extend.presheaf.obj V)
        ((basisModuleSheafExtensionPullback 𝒪 ℱ).val.obj V)
      infer_instance
    apply hV.injective
    change
      (e'.hom.app V) ((G.presheaf.map f) (r • m)) =
        (e'.hom.app V) ((𝒪.extend.obj.map f) r • (G.presheaf.map f) m)
    let h₁ := CategoryTheory.congr_fun (e'.hom.naturality f) (r • m)
    let h₂ := CategoryTheory.congr_fun (e'.hom.naturality f) m
    have h_left :
        (e'.hom.app V) ((G.presheaf.map f) (r • m)) =
          ((basisModuleSheafExtensionPullback 𝒪 ℱ).val.presheaf.map f) (hU (r • m)) := by
      change
        (e'.hom.app V) ((G.presheaf.map f) (r • m)) =
          (((TopCat.Sheaf.forget AddCommGrpCat X).obj
                ((SheafOfModules.toSheaf 𝒪.extend).obj
                  (basisModuleSheafExtensionPullback 𝒪 ℱ))).map f)
            ((e'.hom.app U) (r • m))
      exact h₁
    have h_right :
        ((basisModuleSheafExtensionPullback 𝒪 ℱ).val.presheaf.map f) (hU m) =
          (e'.hom.app V) ((G.presheaf.map f) m) := by
      change
        (((TopCat.Sheaf.forget AddCommGrpCat X).obj
              ((SheafOfModules.toSheaf 𝒪.extend).obj
                (basisModuleSheafExtensionPullback 𝒪 ℱ))).map f)
          ((e'.hom.app U) m) =
            (e'.hom.app V) ((G.presheaf.map f) m)
      exact h₂.symm
    rw [h_left]
    have h_smul :
        ((basisModuleSheafExtensionPullback 𝒪 ℱ).val.presheaf.map f) (hU (r • m)) =
          (𝒪.extend.presheaf.map f r) •
            ((basisModuleSheafExtensionPullback 𝒪 ℱ).val.presheaf.map f) (hU m) := by
      rw [show hU (r • m) = r • hU m by
        exact (hU.linearEquiv (𝒪.extend.obj.obj U)).toLinearMap.map_smul r m]
      exact PresheafOfModules.map_smul
        (basisModuleSheafExtensionPullback 𝒪 ℱ).val f
        r (hU m)
    rw [h_smul, h_right]
    exact ((hV.linearEquiv (𝒪.extend.obj.obj V)).toLinearMap.map_smul _ _).symm

/-- Lemma 6.30.12: a sheaf of `𝒪`-modules on the basis site acquires a canonical
`𝒪.extend`-module structure on its extension to `X`. -/
noncomputable def basisModuleSheafExtension
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪) :
    SheafOfModules 𝒪.extend where
  val := basisModuleSheafExtensionVal 𝒪 ℱ
  isSheaf := (BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj ℱ)).2

/-- The underlying additive sheaf of `basisModuleSheafExtension 𝒪 ℱ` is definitionally the
canonical extension of the underlying additive sheaf of `ℱ` from the basis site to `X`. -/
@[simp]
theorem basisModuleSheafExtension_toSheaf
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪) :
    (SheafOfModules.toSheaf 𝒪.extend).obj
        (basisModuleSheafExtension 𝒪 ℱ) =
      BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj ℱ) :=
  rfl

private instance basisModuleSheafExtension_restrictExtendComponentHom_module
    (𝒪 : BasisRingSheaf) (ℱ : SheafOfModules 𝒪) (U : (BasisOpen B)ᵒᵖ) :
    Module (((basisOpenInclusion B).op ⋙ 𝒪.extend.presheaf).obj U)
      (((basisOpenInclusion B).op ⋙
          (BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj ℱ)).presheaf).obj U) := by
  change Module (𝒪.extend.presheaf.obj ((basisOpenInclusion B).op.obj U))
    ((basisModuleSheafExtension 𝒪 ℱ).val.obj ((basisOpenInclusion B).op.obj U))
  infer_instance

/-- On a basis open, the canonical comparison map from `ℱ` to the restriction of
`basisModuleSheafExtension 𝒪 ℱ` is semilinear for the comparison map from `𝒪` to
`𝒪.extend`. This is the compatibility clause in Stacks Lemma 6.30.12 saying that the
extended action agrees with the original `𝒪`-module action on basis opens. -/
theorem basisModuleSheafExtension_restrictExtendComponentHom_smul
    (𝒪 : BasisRingSheaf) (ℱ : SheafOfModules 𝒪) (U : (BasisOpen B)ᵒᵖ)
    (r : 𝒪.presheaf.obj U) (m : ℱ.val.obj U) :
    BasisSiteSheaf.restrictExtendComponentHom ((SheafOfModules.toSheaf 𝒪).obj ℱ) U (r • m) =
      𝒪.restrictExtendComponentHom U r •
        BasisSiteSheaf.restrictExtendComponentHom ((SheafOfModules.toSheaf 𝒪).obj ℱ) U m := by
  sorry

end
