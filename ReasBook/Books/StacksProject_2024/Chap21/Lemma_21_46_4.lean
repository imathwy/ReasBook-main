import Mathlib
import stacks_project.Chap18.Definition_18_28_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

/-- Reinterpret a module sheaf written using `sheafCompose` as a module over `ringSheaf J 𝒪`. -/
private abbrev asRingedSiteModule
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {𝒪 : Sheaf J CommRingCat.{u}}
    (M : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)) :
    SheafOfModules (ringSheaf J 𝒪) :=
  M

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the ringed
site `(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The underlying `RingCat`-valued structure map attached to a site-presented morphism of ringed
sites out of `(\mathcal C, \mathcal O)`. -/
private abbrev ringedSiteUnderlyingStructureMap
    {D : Type u} [Category.{u} D] {JD : GrothendieckTopology D}
    [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (F : C ⥤ D) [Functor.IsContinuous F J JD]
    {𝒪' : Sheaf JD CommRingCat.{u}}
    (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J JD).obj 𝒪') :
    (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪 ⟶
      (F.sheafPushforwardContinuous RingCat J JD).obj
        ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪') :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map φ

variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]
variable [hAbelian : Abelian (RingedSiteModules 𝒪)]
variable [CategoryWithHomology (RingedSiteModules 𝒪)]
variable [MonoidalCategory (DerivedCategory (RingedSiteModules 𝒪))]
variable [(curriedTensor (RingedSiteModules 𝒪)).Additive]
variable [∀ M : RingedSiteModules 𝒪, ((curriedTensor (RingedSiteModules 𝒪)).obj M).Additive]

local notation "Mod" => RingedSiteModules 𝒪
local notation "DMod" => DerivedCategory Mod

local instance instPreadditiveRingedSiteModules : Preadditive Mod :=
  hAbelian.toPreadditive

/-- An object of `D(\mathcal O)` has tor-amplitude in `[a, \infty)` when derived tensoring with
any degree-zero `\mathcal O`-module has vanishing homology in every degree `< a`. -/
def HasTorAmplitudeGE (E : DMod) (a : ℤ) : Prop :=
  ∀ (ℱ : Mod) (i : ℤ), i < a →
    IsZero ((DerivedCategory.homologyFunctor Mod i).obj
      (E ⊗ ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj ℱ)))

/-- An object of `D(\mathcal O)` admits a representative by a K-flat cochain complex of flat
`\mathcal O`-modules concentrated in degrees `\ge a`. -/
def HasKFlatFlatRepresentativeGE (E : DMod) (a : ℤ) : Prop :=
  ∃ K : CochainComplex Mod ℤ,
    K.IsStrictlyGE a ∧
      (∀ ⦃F : CochainComplex Mod ℤ⦄ [_h : HomologicalComplex.HasTensor F K], F.Acyclic →
        (HomologicalComplex.tensorObj F K).Acyclic) ∧
      (∀ i : ℤ, IsFlat 𝒪 (asRingedSiteModule (K.X i))) ∧
      Nonempty (E ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient Mod (up ℤ)).obj K))

-- Proof sketch: this is the defining homology-vanishing condition for tor-amplitude in
-- `[a,\infty)` written out explicitly.
/-- Unfolding `HasTorAmplitudeGE` says that
`H^i(E \otimes_{\mathcal O}^{\mathbf L} \mathcal F[0]) = 0` for every `i < a`. -/
theorem hasTorAmplitudeGE_iff
    (E : DMod) (a : ℤ) :
    HasTorAmplitudeGE E a ↔
      ∀ (ℱ : Mod) (i : ℤ), i < a →
        IsZero ((DerivedCategory.homologyFunctor Mod i).obj
          (E ⊗ ((DerivedCategory.singleFunctor Mod (0 : ℤ)).obj ℱ))) := sorry

-- Proof sketch: if `E` is represented by a K-flat complex of flat modules supported in degrees
-- `\ge a`, then derived tensoring with any degree-zero module is computed termwise and has no
-- homology below `a`. Conversely, start from a K-flat flat representative of `E`, use the
-- tor-amplitude hypothesis together with Lemma `21.46.2` to identify the new degree-`a` cokernel
-- as flat, and replace the complex by its brutal truncation `\tau_{\ge a}`.
/-- Lemma 21.46.4: an object `E` of `D(\mathcal O)` has tor-amplitude in `[a, \infty)` if and
only if it is isomorphic in `D(\mathcal O)` to a K-flat cochain complex `\mathcal E^\bullet` of
flat `\mathcal O`-modules with `\mathcal E^i = 0` for `i < a`. -/
theorem hasTorAmplitudeGE_iff_hasKFlatFlatRepresentativeGE
    (E : DMod) (a : ℤ) :
    HasTorAmplitudeGE E a ↔ HasKFlatFlatRepresentativeGE E a := sorry

/-- The module category on the target ringed site of a site-presented morphism. -/
private abbrev TargetRingedSiteModules
    {D : Type u} [Category.{u} D] {JD : GrothendieckTopology D}
    [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪' : Sheaf JD CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪')

/-- The pulled-back cochain complex along a site-presented morphism of ringed sites. -/
private abbrev pullbackRingedSiteComplex
    {D : Type u} [Category.{u} D] {JD : GrothendieckTopology D}
    [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasSheafify JD AddCommGrpCat.{u}]
    [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {𝒪' : Sheaf JD CommRingCat.{u}}
    (F : C ⥤ D) [Functor.IsContinuous F J JD]
    (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J JD).obj 𝒪')
    (K : CochainComplex Mod ℤ) :
    CochainComplex (TargetRingedSiteModules 𝒪') ℤ :=
  ((SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)).mapHomologicalComplex
    (up ℤ)).obj K

-- Proof sketch: choose the truncation representative from the previous theorem. The proof of
-- Lemma `21.18.1` shows that pullback preserves K-flatness and termwise flatness for the ambient
-- K-flat flat resolution, and Lemmas `21.17.8` and `21.17.7` show that the same truncation
-- argument remains valid after pullback.
/-- A tor-amplitude-`[a,\infty)` object admits a K-flat flat representative in degrees `\ge a`
whose pullback along any site-presented morphism of ringed sites is again K-flat with flat terms.
-/
theorem exists_pullbackStableKFlatFlatRepresentativeGE_of_hasTorAmplitudeGE
    (E : DMod) (a : ℤ) (hE : HasTorAmplitudeGE E a) :
    ∃ K : CochainComplex Mod ℤ,
      K.IsStrictlyGE a ∧
        (∀ ⦃F : CochainComplex Mod ℤ⦄ [_h : HomologicalComplex.HasTensor F K], F.Acyclic →
          (HomologicalComplex.tensorObj F K).Acyclic) ∧
        (∀ i : ℤ, IsFlat 𝒪 (asRingedSiteModule (K.X i))) ∧
        Nonempty (E ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient Mod (up ℤ)).obj K)) ∧
        ∀ {D : Type u} [Category.{u} D] {JD : GrothendieckTopology D}
          [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
          [HasSheafify JD AddCommGrpCat.{u}]
          [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
          {𝒪' : Sheaf JD CommRingCat.{u}}
          [MonoidalCategory (TargetRingedSiteModules 𝒪')]
          (F : C ⥤ D) [Functor.IsContinuous F J JD]
          (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J JD).obj 𝒪')
          [MonoidalPreadditive (TargetRingedSiteModules 𝒪')]
          [(curriedTensor (TargetRingedSiteModules 𝒪')).Additive]
          [∀ M : TargetRingedSiteModules 𝒪',
            ((curriedTensor (TargetRingedSiteModules 𝒪')).obj M).Additive]
          [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
          [(SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)
            ).PreservesZeroMorphisms],
            (∀ ⦃F' :
                CochainComplex (TargetRingedSiteModules 𝒪') ℤ⦄
                [_h :
                  HomologicalComplex.HasTensor F' (pullbackRingedSiteComplex F φ K)],
                F'.Acyclic →
                  (HomologicalComplex.tensorObj F' (pullbackRingedSiteComplex F φ K)).Acyclic) ∧
            ∀ n : ℤ,
              IsFlat 𝒪'
                (asRingedSiteModule
                  ((SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)).obj
                    (K.X n))) := sorry

end

end SheafOfModules.RingedSite
