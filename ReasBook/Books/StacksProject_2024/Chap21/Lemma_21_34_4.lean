import Mathlib
import StacksProject_2024.Chap21.Lemma_21_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

universe u v

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasProducts (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory J 𝒪))]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex Mod ℤ

/-- The degree-`n` component of postcomposition by a cochain map on the internal-Hom complex of
ringed-site module complexes. -/
noncomputable def ringedSiteModuleComplexInternalHomPostComponent
    {L M₁ M₂ : CpxO} (g : M₁ ⟶ M₂) (n : ℤ) :
    ringedSiteModuleComplexInternalHomDegree L M₁ n ⟶
      ringedSiteModuleComplexInternalHomDegree L M₂ n :=
  Pi.lift (fun p : ℤ ↦
    Pi.π (fun q : ℤ ↦ (ihom (L.X q)).obj (M₁.X (n + q))) p ≫
      (ihom (L.X p)).map (g.f (n + p)))

-- Proof sketch: postcomposition with `g` commutes with both pieces of the internal-Hom
-- differential because `g` is a cochain map, so the defining squares commute after projecting to
-- each factor of the product.
/-- Postcomposition by a cochain map is itself a cochain map on internal-Hom complexes of
`\mathcal O`-modules. -/
theorem ringedSiteModuleComplexInternalHomPostComm
    {L M₁ M₂ : CpxO} (g : M₁ ⟶ M₂) (i j : ℤ)
    (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomPostComponent g i ≫
        ringedSiteModuleComplexInternalHomD L M₂ i j =
      ringedSiteModuleComplexInternalHomD L M₁ i j ≫
        ringedSiteModuleComplexInternalHomPostComponent g j := sorry

/-- Postcomposition by a cochain map on the internal-Hom complex of ringed-site module
complexes. -/
noncomputable def ringedSiteModuleComplexInternalHomPost
    {L M₁ M₂ : CpxO} (g : M₁ ⟶ M₂) :
    ringedSiteModuleComplexInternalHom L M₁ ⟶
      ringedSiteModuleComplexInternalHom L M₂ where
  f n := ringedSiteModuleComplexInternalHomPostComponent g n
  comm' i j hij := ringedSiteModuleComplexInternalHomPostComm g i j hij

/-- The degree-`n` component of precomposition by a cochain map on the internal-Hom complex of
ringed-site module complexes. -/
noncomputable def ringedSiteModuleComplexInternalHomPreComponent
    {L₁ L₂ M : CpxO} (f : L₁ ⟶ L₂) (n : ℤ) :
    ringedSiteModuleComplexInternalHomDegree L₂ M n ⟶
      ringedSiteModuleComplexInternalHomDegree L₁ M n :=
  Pi.lift (fun p : ℤ ↦
    Pi.π (fun q : ℤ ↦ (ihom (L₂.X q)).obj (M.X (n + q))) p ≫
      (MonoidalClosed.pre (f.f p)).app (M.X (n + p)))

-- Proof sketch: precomposition with `f` is compatible with the internal-Hom differential by the
-- naturality of `MonoidalClosed.pre` together with the cochain-map identities for `f`.
/-- Precomposition by a cochain map is itself a cochain map on internal-Hom complexes of
`\mathcal O`-modules. -/
theorem ringedSiteModuleComplexInternalHomPreComm
    {L₁ L₂ M : CpxO} (f : L₁ ⟶ L₂) (i j : ℤ)
    (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexInternalHomPreComponent f i ≫
        ringedSiteModuleComplexInternalHomD L₁ M i j =
      ringedSiteModuleComplexInternalHomD L₂ M i j ≫
        ringedSiteModuleComplexInternalHomPreComponent f j := sorry

/-- Precomposition by a cochain map on the internal-Hom complex of ringed-site module
complexes. -/
noncomputable def ringedSiteModuleComplexInternalHomPre
    {L₁ L₂ M : CpxO} (f : L₁ ⟶ L₂) :
    ringedSiteModuleComplexInternalHom L₂ M ⟶
      ringedSiteModuleComplexInternalHom L₁ M where
  f n := ringedSiteModuleComplexInternalHomPreComponent f n
  comm' i j hij := ringedSiteModuleComplexInternalHomPreComm f i j hij

/-- The degree-`n` component of the canonical map
`\mathcal K^\bullet ⟶ \mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet,
\mathrm{Tot}(\mathcal K^\bullet \otimes_\mathcal O \mathcal L^\bullet))`. -/
noncomputable def ringedSiteModuleComplexTensorTotalizationInternalHomUnitComponent
    (K L : CpxO) (n : ℤ) :
    K.X n ⟶
      ringedSiteModuleComplexInternalHomDegree L
        (HomologicalComplex.tensorObj K L) n :=
  Pi.lift (fun q : ℤ ↦
    MonoidalClosed.curry
      ((β_ (L.X q) (K.X n)).hom ≫
        HomologicalComplex.ιTensorObj K L n q (n + q) rfl))

-- Proof sketch: evaluate both sides after projecting to the `q`-th factor of the internal-Hom
-- product and uncurry. The resulting maps into the `(i + q)`- and `(j + q)`-summands of the
-- total tensor complex agree by the standard total-complex differential formula and the cochain
-- sign convention.
/-- The degreewise components of the tensor-Hom unit assemble to a morphism of cochain
complexes. -/
theorem ringedSiteModuleComplexTensorTotalizationInternalHomUnitComm
    (K L : CpxO) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    ringedSiteModuleComplexTensorTotalizationInternalHomUnitComponent K L i ≫
        ringedSiteModuleComplexInternalHomD L (HomologicalComplex.tensorObj K L) i j =
      K.d i j ≫
        ringedSiteModuleComplexTensorTotalizationInternalHomUnitComponent K L j := sorry

/-- Lemma 21.34.4: for complexes `\mathcal K^\bullet` and `\mathcal L^\bullet` of
`\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, there is a canonical morphism
`\mathcal K^\bullet ⟶ \mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet,
\mathrm{Tot}(\mathcal K^\bullet \otimes_\mathcal O \mathcal L^\bullet))`. In Lean,
`\mathrm{Tot}(\mathcal K^\bullet \otimes_\mathcal O \mathcal L^\bullet)` is
`HomologicalComplex.tensorObj K L`. -/
noncomputable def ringedSiteModuleComplexTensorTotalizationInternalHomUnit
    (K L : CpxO) :
    K ⟶
      ringedSiteModuleComplexInternalHom L
        (HomologicalComplex.tensorObj K L) where
  f n := ringedSiteModuleComplexTensorTotalizationInternalHomUnitComponent K L n
  comm' i j hij :=
    ringedSiteModuleComplexTensorTotalizationInternalHomUnitComm K L i j hij

-- Proof sketch: compare both sides degreewise. Naturality in `K` is postcomposition by the
-- morphism on total tensor complexes induced from `α`, and the component formulas coincide after
-- projecting to each internal-Hom factor.
/-- The canonical tensor-Hom unit is functorial in the left complex. -/
theorem ringedSiteModuleComplexTensorTotalizationInternalHomUnitNaturalLeft
    {K₁ K₂ L : CpxO} (α : K₁ ⟶ K₂) :
    α ≫ ringedSiteModuleComplexTensorTotalizationInternalHomUnit K₂ L =
      ringedSiteModuleComplexTensorTotalizationInternalHomUnit K₁ L ≫
        ringedSiteModuleComplexInternalHomPost
          (HomologicalComplex.tensorHom α (𝟙 L)) := sorry

-- Proof sketch: compare the two routes from `K` to
-- `Hom^\bullet(L₁^\bullet, Tot(K^\bullet ⊗ L₂^\bullet))`. One route first applies the unit for
-- `L₂` and then precomposes by `β`; the other applies the unit for `L₁` and then postcomposes by
-- the induced morphism on total tensor complexes.
/-- The canonical tensor-Hom unit is functorial in the right complex. -/
theorem ringedSiteModuleComplexTensorTotalizationInternalHomUnitNaturalRight
    (K : CpxO) {L₁ L₂ : CpxO} (β : L₁ ⟶ L₂) :
    ringedSiteModuleComplexTensorTotalizationInternalHomUnit K L₂ ≫
        ringedSiteModuleComplexInternalHomPre β =
      ringedSiteModuleComplexTensorTotalizationInternalHomUnit K L₁ ≫
        ringedSiteModuleComplexInternalHomPost
          (HomologicalComplex.tensorHom (𝟙 K) β) := sorry

end

end SheafOfModules.RingedSite
