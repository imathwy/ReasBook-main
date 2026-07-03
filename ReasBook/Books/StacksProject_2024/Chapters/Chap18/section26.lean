import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_26_1 (from Chap18) -/
open CategoryTheory MonoidalCategory

noncomputable section

universe u

variable {C : Type u} [Category.{u} C]
variable {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})

local infixr:70 " ⊗ " => moduleTensor

/-
Domain-style sampling for Lemma 18.26.1:
- primary domain: sheafification of presheaves of modules over a fixed sheaf of commutative rings,
  together with the induced tensor comparison;
- sampled owner declarations:
  `moduleSheafification`,
  `moduleTensor`,
  `PresheafOfModules.sheafificationAdjunction`,
  `PresheafOfModules.Monoidal.tensorHom`;
- best owner abstraction:
  the source-facing owner is the canonical tensor/sheafification comparison attached to the
  sheafification functor `moduleSheafification 𝒪`, with the isomorphism surface obtained as
  `asIso` of that comparison;
- primitive data:
  a sheaf of commutative rings `𝒪` and two presheaves of `𝒪`-modules `ℱ`, `𝒢`;
- derived API:
  the comparison morphism, its `IsIso` instance, and the resulting tensor/sheafification
  isomorphism.

Layer triage:
- `source-facing`: the canonical identification
  `ℱ^# ⊗ 𝒢^# ≅ (ℱ ⊗ 𝒢)^#`;
- `core/canonical`: `moduleSheafification 𝒪`, `moduleTensor`, and
  `PresheafOfModules.sheafificationAdjunction`;
- `bridge/view`: the comparison morphism whose inverse is the source-facing isomorphism. -/

-- Proof sketch: adjoint transpose the tensor of the two unit morphisms into the tensor of the
-- sheafifications, then follow with the sheafification unit for the presheaf tensor of the two
-- underlying sheaves.
/-- The canonical comparison morphism from the sheafification of a presheaf tensor product to the
tensor product of the individual sheafifications. -/
noncomputable def moduleSheafificationTensorComparison
    (ℱ 𝒢 : PresheafOfModules (ringSheaf J 𝒪).obj) :
    (moduleSheafification 𝒪).obj (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢) ⟶
      (moduleSheafification 𝒪).obj ℱ ⊗ (moduleSheafification 𝒪).obj 𝒢 :=
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J 𝒪).obj)
  let unitToSheafification
      (ℋ : PresheafOfModules (ringSheaf J 𝒪).obj) :
      ℋ ⟶ (SheafOfModules.forget (ringSheaf J 𝒪)).obj ((moduleSheafification 𝒪).obj ℋ) := by
    simpa [moduleSheafification] using adj.unit.app ℋ
  let tensorUnit :
      PresheafOfModules.Monoidal.tensorObj
          ((moduleSheafification 𝒪).obj ℱ).val
          ((moduleSheafification 𝒪).obj 𝒢).val ⟶
        (SheafOfModules.forget (ringSheaf J 𝒪)).obj
          (((moduleSheafification 𝒪).obj ℱ) ⊗ ((moduleSheafification 𝒪).obj 𝒢)) := by
    simpa [moduleTensor, moduleSheafification] using
      adj.unit.app
        (PresheafOfModules.Monoidal.tensorObj
          ((moduleSheafification 𝒪).obj ℱ).val
          ((moduleSheafification 𝒪).obj 𝒢).val)
  (adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢)
      (((moduleSheafification 𝒪).obj ℱ) ⊗ ((moduleSheafification 𝒪).obj 𝒢))).symm
    (PresheafOfModules.Monoidal.tensorHom
        (unitToSheafification ℱ)
        (unitToSheafification 𝒢) ≫
      tensorUnit)

/-- The canonical tensor/sheafification comparison morphism is an isomorphism. -/
instance moduleSheafificationTensorComparison_isIso
    (ℱ 𝒢 : PresheafOfModules (ringSheaf J 𝒪).obj) :
    IsIso (moduleSheafificationTensorComparison 𝒪 ℱ 𝒢) := by
  sorry

/-- Lemma 18.26.1: for presheaves of `\mathcal O`-modules `ℱ` and `𝒢`, the tensor product of
their sheafifications is canonically isomorphic to the sheafification of their presheaf tensor
product. -/
noncomputable abbrev moduleSheafificationTensorIso
    (ℱ 𝒢 : PresheafOfModules (ringSheaf J 𝒪).obj) :
    (moduleSheafification 𝒪).obj ℱ ⊗ (moduleSheafification 𝒪).obj 𝒢 ≅
      (moduleSheafification 𝒪).obj (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢) :=
  (asIso (moduleSheafificationTensorComparison 𝒪 ℱ 𝒢)).symm

/-! ### Lemma_18_26_2 (from Chap18) -/
open CategoryTheory MonoidalCategory
open Functor.OplaxMonoidal

noncomputable section

universe u

section

variable {C : Type u} [SmallCategory C]
variable {D : Type u} [SmallCategory D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable {F : D ⥤ C}
variable [Functor.IsContinuous F JD JC]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪C : Sheaf JC CommRingCat.{u}} {𝒪D : Sheaf JD CommRingCat.{u}}
local notation "ModD" => ringedSiteModuleCategory JD 𝒪D
local notation "ModC" => ringedSiteModuleCategory JC 𝒪C
variable
  (φ :
    ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪D) ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JD JC).obj
        ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪C))
variable [(SheafOfModules.pushforward φ).IsRightAdjoint]
variable [MonoidalCategory (SheafOfModules ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪D))]
variable [MonoidalCategory (SheafOfModules ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪C))]
variable [(SheafOfModules.pushforward φ).LaxMonoidal]

local notation "fStar" => SheafOfModules.pullback φ

local instance : (SheafOfModules.pullback φ).OplaxMonoidal :=
  (SheafOfModules.pullbackPushforwardAdjunction φ).leftAdjointOplaxMonoidal

/- Domain-style sampling for Lemma 18.26.2:
- primary domain: pullback of sheaves of modules along a morphism of ringed topoi, viewed as a
  monoidal comparison between inverse image and tensor product;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `Functor.OplaxMonoidal.δ`,
  `Adjunction.leftAdjointOplaxMonoidal`;
- best owner abstraction: the canonical adjunction-induced oplax monoidal structure on the
  pullback functor `fStar`, so the source-facing comparison is the owner morphism
  `δ fStar ℱ 𝒢`;
- primitive data: the ringed-site module categories `ModD` and `ModC`, the canonical pullback
  functor `SheafOfModules.pullback φ`, its adjunction with `SheafOfModules.pushforward φ`, and
  the ambient lax monoidal structure on the pushforward;
- derived API: the source-facing comparison is exactly the owner morphism `δ fStar ℱ 𝒢`, and its
  invertibility is exposed directly as an `IsIso` instance on that owner morphism rather than by
  a parallel local theorem.

Source/core/bridge triage:
- `source-facing`: the claim that the pullback-tensor comparison for module sheaves is invertible;
- `core/canonical`: the owner functor `SheafOfModules.pullback φ` together with the canonical
  adjunction-induced oplax tensor map `Functor.OplaxMonoidal.δ`;
- `bridge/view`: downstream use of `asIso (δ fStar ℱ 𝒢)` when the source wording wants the
  comparison written as an isomorphism. -/

variable (ℱ 𝒢 : ModD)

/- Lemma 18.26.2: the canonical pullback-tensor comparison morphism
`f^*(\mathcal F \otimes \mathcal G) \to f^*\mathcal F ⊗ f^*\mathcal G`,
namely `δ fStar ℱ 𝒢`, is an isomorphism. In the canonical owner API this is the direct
`IsIso` instance attached to the comparison morphism itself, with downstream isomorphism data
recovered as `asIso (δ fStar ℱ 𝒢)`. -/
instance : IsIso (δ fStar ℱ 𝒢) := by
  sorry

end

/-! ### Lemma_18_26_3 (from Chap18) -/
open CategoryTheory Limits
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ V : Over U, HasWeakSheafify ((J.over U).over V) AddCommGrpCat]
variable [∀ U : C, ∀ V : Over U, ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ V : Over U, ((J.over U).over V).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]

/-- The tensor product of two module sheaves, viewed in `ringedSiteModuleCategory J 𝒪`. -/
private abbrev tensorModule (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪) :
    ringedSiteModuleCategory J 𝒪 :=
  ℱ ⊗ 𝒢

-- Proof sketch: choose a covering on which both sheaves become free, tensor the local free models,
-- and use the local criterion for local freeness to descend back to the original ringed site.
/-- Lemma 18.26.3 (1): if `\mathcal F` and `\mathcal G` are locally free
`\mathcal O`-modules on a ringed site, then `\mathcal F \otimes_{\mathcal O} \mathcal G`
is locally free. -/
theorem isLocallyFree_ringedSiteModuleTensor
    (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪)
    [IsLocallyFree ℱ] [IsLocallyFree 𝒢] :
    IsLocallyFree (tensorModule ℱ 𝒢) := sorry

-- Proof sketch: after refining to a common covering where both sheaves are finite free, the local
-- tensor product is again finite free; then apply the locality criterion for finite local freeness.
/-- Lemma 18.26.3 (2): if `\mathcal F` and `\mathcal G` are finite locally free
`\mathcal O`-modules on a ringed site, then `\mathcal F \otimes_{\mathcal O} \mathcal G`
is finite locally free. -/
theorem isFiniteLocallyFree_ringedSiteModuleTensor
    (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪)
    [IsFiniteLocallyFree ℱ] [IsFiniteLocallyFree 𝒢] :
    IsFiniteLocallyFree (tensorModule ℱ 𝒢) := sorry

-- Proof sketch: local generating sections for `\mathcal F` and `\mathcal G` produce local
-- generating sections for the tensor product by taking pairwise tensors on a common refinement.
/-- Lemma 18.26.3 (3): if `\mathcal F` and `\mathcal G` are locally generated by sections, then
`\mathcal F \otimes_{\mathcal O} \mathcal G` is locally generated by sections. -/
theorem isLocallyGeneratedBySections_ringedSiteModuleTensor
    (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪)
    [IsLocallyGeneratedBySections ℱ] [IsLocallyGeneratedBySections 𝒢] :
    IsLocallyGeneratedBySections (tensorModule ℱ 𝒢) := sorry

-- Proof sketch: finite type means local finite generation, and the tensor product of two finite
-- generating families yields a finite generating family after refining the covering.
/-- Lemma 18.26.3 (4): if `\mathcal F` and `\mathcal G` are of finite type, then
`\mathcal F \otimes_{\mathcal O} \mathcal G` is of finite type. -/
theorem isFiniteType_ringedSiteModuleTensor
    (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪)
    [ℱ.IsFiniteType] [𝒢.IsFiniteType] :
    (tensorModule ℱ 𝒢).IsFiniteType := sorry

-- Proof sketch: choose local presentations for both factors, tensor those presentations on a
-- common covering, and use the local characterization of quasi-coherent sheaves.
/-- Lemma 18.26.3 (5): if `\mathcal F` and `\mathcal G` are quasi-coherent, then
`\mathcal F \otimes_{\mathcal O} \mathcal G` is quasi-coherent. -/
theorem isQuasicoherent_ringedSiteModuleTensor
    (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪)
    [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] :
    (tensorModule ℱ 𝒢).IsQuasicoherent := sorry

-- Proof sketch: finite local presentations tensor to finite local presentations on a common
-- refinement, so finite presentation is preserved by the tensor product.
/-- Lemma 18.26.3 (6): if `\mathcal F` and `\mathcal G` are of finite presentation, then
`\mathcal F \otimes_{\mathcal O} \mathcal G` is of finite presentation. -/
theorem isFinitePresentation_ringedSiteModuleTensor
    (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪)
    [ℱ.IsFinitePresentation] [𝒢.IsFinitePresentation] :
    (tensorModule ℱ 𝒢).IsFinitePresentation := sorry

-- Proof sketch: tensor a finite presentation of `\mathcal F` with the coherent sheaf
-- `\mathcal G`, use finite presentation to control relations, and use coherence of
-- `\mathcal G` to keep the relevant kernels of finite type.
/-- Lemma 18.26.3 (7): if `\mathcal F` is of finite presentation and `\mathcal G` is coherent,
then `\mathcal F \otimes_{\mathcal O} \mathcal G` is coherent. -/
theorem isCoherent_ringedSiteModuleTensor_of_isFinitePresentation_left
    (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪)
    [ℱ.IsFinitePresentation] [IsCoherent 𝒢] :
    IsCoherent (tensorModule ℱ 𝒢) := sorry

-- Proof sketch: combine the preceding finite-presentation-plus-coherent argument with the fact
-- that a coherent sheaf is of finite type, applying it symmetrically to both tensor factors.
/-- Lemma 18.26.3 (8): if `\mathcal F` and `\mathcal G` are coherent, then
`\mathcal F \otimes_{\mathcal O} \mathcal G` is coherent. -/
theorem isCoherent_ringedSiteModuleTensor
    (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪)
    [IsCoherent ℱ] [IsCoherent 𝒢] :
    IsCoherent (tensorModule ℱ 𝒢) := sorry

end SheafOfModules.RingedSite
