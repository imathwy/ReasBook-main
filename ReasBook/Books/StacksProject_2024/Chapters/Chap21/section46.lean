import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_21_46_1 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false
set_option linter.unusedSectionVars false

namespace SheafOfModules.RingedSite

section

variable (X : RingedSite.{u, v})

local notation "Mod" => RingedSite.Hom.ModuleCat X
local notation "DMod" => RingedSite.Hom.ModuleDerived X
local notation "H" => DerivedCategory.homologyFunctor Mod
local notation "single0" => DerivedCategory.singleFunctor Mod (0 : ℤ)

variable [Abelian Mod]
variable [CategoryWithHomology Mod]
variable (hMon : MonoidalCategoryStruct DMod)

local instance instMonoidalCategoryStructDMod : MonoidalCategoryStruct DMod := hMon

private abbrev tensorSingle0 (E : DMod) (ℱ : Mod) : DMod :=
  E ⊗ ((single0).obj ℱ)

/- Domain-style sampling for Definition 21.46.1:
- primary domain: tor-amplitude and local tor dimension in the derived category of modules on a
  ringed site;
- sampled owner declarations:
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`,
  `RingedSite.localization`,
  `RingedSite.Hom.localizedRestrictionDerived`,
  `RingedSite.ofCommRingSheaf`;
- best owner abstraction: the source-facing predicates `HasTorAmplitudeIn`,
  `HasFiniteTorDimension`, `LocallyHasFiniteTorDimension`, and `ModuleHasTorDimensionLE` depend
  only on the ambient ringed site `X`, so their owner-level parameters should be `ModuleCat X`,
  `ModuleDerived X`, `X.siteTopology.Cover`, and `X.localization U` rather than a chosen site
  presentation `(C, J, 𝒪)`;
- primitive data: an object of `D(\mathcal O_X)`, interval bounds, and degree-zero module inputs;
- derived API: the finite-tor-dimension and module-level specializations, plus the localized
  specialization below.

Source/core/bridge triage:
- `source-facing`: the tor-amplitude, finite-tor-dimension, and module tor-dimension predicates;
- `core/canonical`: `RingedSite.Hom.ModuleCat`, `RingedSite.Hom.ModuleDerived`, and, for the local
  variant below, `RingedSite.localization` and `RingedSite.Hom.localizedRestrictionDerived`;
- `bridge/view`: a site presentation `X = RingedSite.ofCommRingSheaf J 𝒪`, which should specialize
  the ambient-owner formulation rather than own a parallel local-finite-tor-dimension API. -/

/-- Definition 21.46.1 (1): an object `E` of `D(\mathcal O_X)` has tor-amplitude in `[a, b]` if
for every `\mathcal O_X`-module `\mathcal F`, the derived tensor product
`E \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F[0]` has vanishing homology outside `[a, b]`. -/
def HasTorAmplitudeIn (E : DMod) (a b : ℤ) : Prop :=
  ∀ (ℱ : Mod) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((H i).obj (tensorSingle0 X E ℱ))

-- Proof sketch: unfold `HasTorAmplitudeIn`; it is exactly the defining homology-vanishing
-- condition for `E \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F[0]` outside the interval
-- `[a, b]`.
/-- An object of `D(\mathcal O_X)` has tor-amplitude in `[a, b]` exactly when derived tensoring
with every degree-zero `\mathcal O_X`-module has vanishing homology outside `[a, b]`. -/
theorem hasTorAmplitudeIn_iff (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn X E a b ↔
      ∀ (ℱ : Mod) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((H i).obj (tensorSingle0 X E ℱ)) :=
  Iff.rfl

/-- Definition 21.46.1 (2): an object of `D(\mathcal O_X)` has finite tor dimension if it has
tor-amplitude in some interval `[a, b]`. -/
def HasFiniteTorDimension (E : DMod) : Prop :=
  ∃ a b : ℤ, HasTorAmplitudeIn X E a b

-- Proof sketch: unfold `HasFiniteTorDimension`; this is definitionally the existence of a
-- tor-amplitude interval.
/-- An object of `D(\mathcal O_X)` has finite tor dimension exactly when it has tor-amplitude in
some interval `[a, b]`. -/
theorem hasFiniteTorDimension_iff (E : DMod) :
    HasFiniteTorDimension X E ↔ ∃ a b : ℤ, HasTorAmplitudeIn X E a b :=
  Iff.rfl

/-- Definition 21.46.1 (4): an `\mathcal O_X`-module `\mathcal F` has tor dimension at most `d`
if its degree-zero derived object `\mathcal F[0]` has tor-amplitude in `[-d, 0]`. -/
def ModuleHasTorDimensionLE (ℱ : Mod) (d : ℕ) : Prop :=
  HasTorAmplitudeIn X ((single0).obj ℱ) (-((d : ℤ))) 0

-- Proof sketch: unfold `ModuleHasTorDimensionLE`; it is exactly the tor-amplitude condition for
-- the degree-zero derived object `\mathcal F[0]` with bounds `[-d, 0]`.
/-- An `\mathcal O_X`-module has tor dimension at most `d` exactly when its degree-zero derived
object has tor-amplitude in `[-d, 0]`. -/
theorem moduleHasTorDimensionLE_iff (ℱ : Mod) (d : ℕ) :
    ModuleHasTorDimensionLE X ℱ d ↔
      HasTorAmplitudeIn X ((single0).obj ℱ) (-((d : ℤ))) 0 :=
  Iff.rfl

end

section

variable (X : RingedSite.{u, v})

local notation "DMod" => RingedSite.Hom.ModuleDerived X

variable [Abelian (RingedSite.Hom.ModuleCat X)]
variable [CategoryWithHomology (RingedSite.Hom.ModuleCat X)]
variable [∀ U : X, Abelian (RingedSite.Hom.ModuleCat (X.localization U))]
variable [∀ U : X, CategoryWithHomology (RingedSite.Hom.ModuleCat (X.localization U))]
variable [∀ U : X, MonoidalCategoryStruct (RingedSite.Hom.ModuleDerived (X.localization U))]
variable [∀ U : X, (RingedSite.Hom.localizedRestriction X U).Additive]
variable [∀ U : X, PreservesFiniteLimits (RingedSite.Hom.localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (RingedSite.Hom.localizedRestriction X U)]

/-- Definition 21.46.1 (3): an object `E` of `D(\mathcal O)` locally has finite tor dimension if
for every object `U` there is a covering of `U` on whose members the restriction of `E` has
finite tor dimension. -/
def LocallyHasFiniteTorDimension (E : DMod) : Prop :=
  ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    HasFiniteTorDimension (X.localization I.Y)
      ((RingedSite.Hom.localizedRestrictionDerived X I.Y).obj E)

-- Proof sketch: unfold `LocallyHasFiniteTorDimension`; this is exactly the coveringwise
-- restriction condition saying that each object admits a cover on whose members the restricted
-- derived object has finite tor dimension.
/-- An object of `D(\mathcal O)` locally has finite tor dimension exactly when each object of the
site admits a covering on whose members the restriction has finite tor dimension. -/
theorem locallyHasFiniteTorDimension_iff (E : DMod) :
    LocallyHasFiniteTorDimension X E ↔
      ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
        HasFiniteTorDimension (X.localization I.Y)
          ((RingedSite.Hom.localizedRestrictionDerived X I.Y).obj E) :=
  Iff.rfl

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_46_2 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the given
ringed site. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => RingedSiteModules 𝒪

variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]
variable [(curriedTensor (RingedSiteModules 𝒪)).Additive]
variable [∀ M : RingedSiteModules 𝒪, ((curriedTensor (RingedSiteModules 𝒪)).obj M).Additive]
variable [∀ (K L : CochainComplex (RingedSiteModules 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSiteModules 𝒪))]

-- Proof sketch: because `E` is bounded above with flat terms, Lemma `21.17.8` makes `E` K-flat,
-- so tensoring `E` with any `\mathcal O`-module computes derived tensoring with `Q(E)`. The
-- tor-amplitude hypothesis forces exactness in degree `a - 1` after tensoring with any module,
-- hence the tail ending in `cokernel(d^{a - 1})` is a flat resolution. Therefore `Tor₁` of this
-- cokernel with every module vanishes, and Lemma `21.17.15` yields flatness.
/-- Lemma 21.46.2: if `E^•` is a bounded above complex of flat `\mathcal O`-modules on a ringed
site and tensoring it with any degree-zero `\mathcal O`-module is exact outside `[a, b]`, then
the cokernel of the differential `E^{a - 1} ⟶ E^a` is a flat `\mathcal O`-module. -/
theorem isFlat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeIn
    (E : CochainComplex Mod ℤ) (a b : ℤ)
    (hbounded : IsBoundedAbove E)
    (hFlat : ∀ n : ℤ, IsFlat 𝒪 (E.X n))
    (hTor :
      ∀ (ℱ : Mod) (i : ℤ), i ∉ Set.Icc a b →
        (HomologicalComplex.tensorObj E
            ((HomologicalComplex.single Mod (ComplexShape.up ℤ) 0).obj ℱ)).ExactAt i) :
    IsFlat 𝒪 (cokernel (E.dFrom (a - 1))) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_46_3 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable [Abelian (RingedSiteModules 𝒪)]
variable [CategoryWithHomology (RingedSiteModules 𝒪)]
variable [MonoidalCategory (DerivedCategory (RingedSiteModules 𝒪))]

local notation "Mod" => RingedSiteModules 𝒪
local notation "DMod" => DerivedCategory (RingedSiteModules 𝒪)

/-- An object of `D(\mathcal O)` admits a representative by a cochain complex of flat
`\mathcal O`-modules concentrated in degrees `[a, b]`. -/
def HasFlatRepresentativeInRange (E : DMod) (a b : ℤ) : Prop :=
  ∃ K : CochainComplex Mod ℤ,
    K.IsStrictlyGE a ∧
      K.IsStrictlyLE b ∧
      (∀ i : ℤ,
        IsFlat 𝒪
          (show SheafOfModules (ringSheaf J 𝒪) from K.X i)) ∧
      Nonempty (E ≅ DerivedCategory.Q.obj K)

-- Proof sketch: if `E` is represented by such a flat complex, derived tensor products are computed
-- termwise, so tor-amplitude is immediate from the degree support. Conversely, start from a
-- K-flat replacement with flat terms as in Lemma `21.17.11`, trim the complex from above using
-- vanishing of the top cohomology and flat-kernel preservation from Lemma `18.28.10`, and then
-- truncate below `a`; Lemma `21.46.2` gives flatness in the new degree `a` term.
/-- Lemma 21.46.3: an object `E` of `D(\mathcal O)` has tor-amplitude in `[a, b]` if and only if
it is isomorphic in `D(\mathcal O)` to a cochain complex `\mathcal E^\bullet` of flat
`\mathcal O`-modules with `\mathcal E^i = 0` for `i ∉ [a, b]`. -/
theorem hasTorAmplitudeIn_iff_hasFlatRepresentativeInRange
    (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔ HasFlatRepresentativeInRange E a b := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_46_4 (from Chap21) -/
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

/-! ### Lemma_21_46_5 (from Chap21) -/
open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪C : Sheaf JC CommRingCat.{u}} {𝒪D : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪C ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)
variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]

variable [Abelian (RingedSiteModules JC 𝒪C)]
variable [CategoryWithHomology (RingedSiteModules JC 𝒪C)]
variable [MonoidalCategory (RingedSiteModules JC 𝒪C)]
variable [MonoidalPreadditive (RingedSiteModules JC 𝒪C)]
variable [MonoidalCategory (DerivedCategory (RingedSiteModules JC 𝒪C))]

variable [Abelian (RingedSiteModules JD 𝒪D)]
variable [CategoryWithHomology (RingedSiteModules JD 𝒪D)]
variable [MonoidalCategory (RingedSiteModules JD 𝒪D)]
variable [MonoidalPreadditive (RingedSiteModules JD 𝒪D)]
variable [MonoidalCategory (DerivedCategory (RingedSiteModules JD 𝒪D))]

variable [(pullbackFunctor F φ).Additive]

-- Proof sketch: represent `E` by a flat complex concentrated in degrees `[a, b]` using
-- Lemma `21.46.3`, pull that complex back termwise along `F`, and use Lemma `18.39.1` to keep
-- the terms flat after pullback. The pulled-back complex is still concentrated in `[a, b]`, so
-- Lemma `21.46.3` again identifies `Lf^*E` as having tor-amplitude in `[a, b]`.
/-- Lemma 21.46.5: for the site-presented morphism of ringed sites determined by `F` and `φ`, if
`E` has tor-amplitude in `[a, b]`, then its derived pullback `Lf^*E` also has tor-amplitude in
`[a, b]`. -/
theorem leftDerivedPullback_hasTorAmplitudeIn
    (E : DerivedCategory (RingedSiteModules JC 𝒪C)) (a b : ℤ) (hE : HasTorAmplitudeIn E a b) :
    HasTorAmplitudeIn ((leftDerivedPullback F φ).obj E) a b := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_46_6 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Lemma 21.46.6:
- primary domain: tor-amplitude in the derived category of modules on a ringed site, viewed as an
  object property with distinguished-triangle closure;
- sampled owner declarations:
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`,
  `CategoryTheory.hasTorAmplitudeIn_obj₃_of_distinguishedTriangle`,
  `CategoryTheory.hasTorAmplitudeIn_obj₂_of_distinguishedTriangle`,
  `CategoryTheory.hasTorAmplitudeIn_obj₁_of_distinguishedTriangle`;
- best owner abstraction: the source-facing owner is `HasTorAmplitudeIn` on
  `DerivedCategory (ringedSiteModuleCategory J 𝒪)`, while this file provides the three
  distinguished-triangle bridge lemmas for that owner in the ringed-site setting;
- primitive data: the ambient derived category `D(\mathcal O)`, a distinguished triangle in it,
  and the tor-amplitude hypotheses on the relevant vertices;
- derived API: the tor-amplitude conclusion for the remaining vertex.

Source/core/bridge triage:
- `source-facing`: the three textbook closure statements for tor-amplitude in a distinguished
  triangle;
- `core/canonical`: the owner predicate `HasTorAmplitudeIn`;
- `bridge/view`: these `obj₁`/`obj₂`/`obj₃_of_distinguishedTriangle` consequences.

The previous version carried `[HasSheafify J AddCommGrpCat]` and
`[J.WEqualsLocallyBijective AddCommGrpCat]` through the public theorem surface even though neither
the ambient category nor the owner predicate depends on them. This refinement removes those
proof-only assumptions from the API.
-/
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (DerivedCategory (ringedSiteModuleCategory J 𝒪))]

variable {a b : ℤ}

-- Proof sketch: apply the derived tensor functor with an arbitrary degree-zero `\mathcal O`-module
-- to the distinguished triangle, use preservation of distinguished triangles, and read off the
-- vanishing range for the third term from the resulting long exact homology sequence.
/-- Lemma 21.46.6 (1): in a distinguished triangle in `D(\mathcal O)`, if the first term has
tor-amplitude in `[a + 1, b + 1]` and the second term has tor-amplitude in `[a, b]`, then the
third term has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_obj₃_of_distinguishedTriangle
    (T : Triangle (DerivedCategory (ringedSiteModuleCategory J 𝒪)))
    (hT : T ∈ distTriang (DerivedCategory (ringedSiteModuleCategory J 𝒪)))
    (h₁ : HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1))
    (h₂ : HasTorAmplitudeIn T.obj₂ a b) :
    HasTorAmplitudeIn T.obj₃ a b := sorry

-- Proof sketch: apply the derived tensor functor with an arbitrary degree-zero `\mathcal O`-module
-- to the distinguished triangle and use the long exact homology sequence together with
-- two-out-of-three for vanishing outside `[a, b]`.
/-- Lemma 21.46.6 (2): in a distinguished triangle in `D(\mathcal O)`, if the first and third
terms have tor-amplitude in `[a, b]`, then the second term has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_obj₂_of_distinguishedTriangle
    (T : Triangle (DerivedCategory (ringedSiteModuleCategory J 𝒪)))
    (hT : T ∈ distTriang (DerivedCategory (ringedSiteModuleCategory J 𝒪)))
    (h₁ : HasTorAmplitudeIn T.obj₁ a b)
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₂ a b := sorry

-- Proof sketch: rotate the distinguished triangle and reduce to the first closure statement,
-- which shifts the tor-amplitude interval on the first vertex by one.
/-- Lemma 21.46.6 (3): in a distinguished triangle in `D(\mathcal O)`, if the second term has
tor-amplitude in `[a + 1, b + 1]` and the third term has tor-amplitude in `[a, b]`, then the
first term has tor-amplitude in `[a + 1, b + 1]`. -/
theorem hasTorAmplitudeIn_obj₁_of_distinguishedTriangle
    (T : Triangle (DerivedCategory (ringedSiteModuleCategory J 𝒪)))
    (hT : T ∈ distTriang (DerivedCategory (ringedSiteModuleCategory J 𝒪)))
    (h₂ : HasTorAmplitudeIn T.obj₂ (a + 1) (b + 1))
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_46_7 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped RingedSiteDerivedTensor

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

/- Domain-style sampling for Lemma 21.46.7:
- primary domain: tor-amplitude in `D(\mathcal O)` under the derived tensor product on a ringed
  site;
- sampled owner declarations:
  `RingedSiteModules`,
  `SheafOfModules.RingedSite.derivedTensorProduct`,
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`,
  `AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_derivedTensorProduct`;
- best owner abstraction: the ambient owner is `RingedSiteModules J 𝒪`, the source-facing
  predicate is `HasTorAmplitudeIn` on `DerivedCategory (RingedSiteModules J 𝒪)`, and the tensor
  owner is the canonical derived tensor product notation `K ⊗^L L`;
- primitive data: the objects `K`, `L` of `D(\mathcal O)` and their tor-amplitude bounds;
- derived API: the induced tor-amplitude bound for `K ⊗^L L`.

Source/core/bridge triage:
- `source-facing`: the tor-amplitude bound for the tensor product on the ringed site;
- `core/canonical`: `HasTorAmplitudeIn` together with `derivedTensorProduct`;
- `bridge/view`: this theorem, which records closure of the source-facing predicate under the
  canonical tensor owner.

The previous file restated the definition of tor-amplitude inline. This refinement removes that
duplicate wheel and states the lemma directly with the chapter owner abstractions.
-/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [hAbelian : Abelian (RingedSiteModules J 𝒪)]
variable [CategoryWithHomology (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (DerivedCategory (RingedSiteModules J 𝒪))]
variable [HasCountableCoproducts (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteModules J 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules J 𝒪)]
variable [HasColimits (RingedSiteModules J 𝒪)]
variable [(curriedTensor (RingedSiteModules J 𝒪)).Additive]
variable [∀ M : RingedSiteModules J 𝒪, ((curriedTensor (RingedSiteModules J 𝒪)).obj M).Additive]
variable [∀ (K L : CochainComplex (RingedSiteModules J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSiteModules J 𝒪))]

local notation "Mod" => RingedSiteModules J 𝒪
local notation "DMod" => DerivedCategory Mod

local instance instPreadditiveMod : Preadditive Mod :=
  hAbelian.toPreadditive

variable {a b c d : ℤ}

-- Proof sketch: test the tor-amplitude conditions for `K` and `L` against an arbitrary
-- degree-zero module, reassociate the iterated derived tensor product, and combine the intervals
-- `[a, b]` and `[c, d]` via the Tor spectral sequence.
/-- Lemma 21.46.7: if `K` has tor-amplitude in `[a, b]` and `L` has tor-amplitude in `[c, d]`,
then `K \otimes_{\mathcal O}^{\mathbf L} L` has tor-amplitude in `[a + c, b + d]`. -/
theorem hasTorAmplitudeIn_tensor
    (K L : DMod)
    (hK : HasTorAmplitudeIn K a b)
    (hL : HasTorAmplitudeIn L c d) :
    HasTorAmplitudeIn (K ⊗^L L) (a + c) (b + d) := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_46_8 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "DMod" => DerivedCategory Mod

variable [Abelian (ringedSiteModuleCategory J 𝒪)]
variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (DerivedCategory (ringedSiteModuleCategory J 𝒪))]

variable {a b : ℤ}

local notation "TorAmp" => fun E : DMod ↦ HasTorAmplitudeIn E a b

private instance isZero_isStableUnderRetracts (D : Type*) [Category D] :
    ObjectProperty.IsStableUnderRetracts (fun X : D ↦ IsZero X) where
  of_retract h hY := by
    refine ⟨?_, ?_⟩
    · intro Z
      refine ⟨⟨h.i ≫ hY.to_ Z⟩, ?_⟩
      intro f
      calc
        f = 𝟙 _ ≫ f := by simp
        _ = (h.i ≫ h.r) ≫ f := by rw [h.retract]
        _ = h.i ≫ (h.r ≫ f) := by simp
        _ = h.i ≫ hY.to_ Z := by
          exact congrArg (h.i ≫ ·) (hY.eq_of_src _ _)
    · intro Z
      refine ⟨⟨hY.from_ Z ≫ h.r⟩, ?_⟩
      intro f
      calc
        f = f ≫ 𝟙 _ := by simp
        _ = f ≫ (h.i ≫ h.r) := by rw [h.retract]
        _ = (f ≫ h.i) ≫ h.r := by simp
        _ = hY.from_ Z ≫ h.r := by
          exact congrArg (· ≫ h.r) (hY.eq_of_tgt _ _)

/- Domain-style sampling for Lemma 21.46.8:
- primary domain: retract-stable object properties in monoidal derived categories, specialized to
  tor-amplitude on `D(\mathcal O)`;
- sampled owner declarations:
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.prop_of_retract`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `Limits.IsZero`,
  `Retract.map`;
- best owner abstraction: the object property `TorAmp` on `D(\mathcal O)`, with retract-stability
  as the core owner-level API and the two direct-summand consequences as derived API; the
  pointwise `IsZero` condition in the definition is itself treated as a retract-stable object
  property on the target category;
- primitive vs. derived:
  primitive data are the source-facing tor-amplitude predicate `HasTorAmplitudeIn E a b`;
  the retract-stability instance and the left/right biproduct lemmas are derived consequences;
- source/core/bridge triage:
  `source-facing`: the two textbook direct-summand lemmas;
  `core/canonical`: `ObjectProperty.IsStableUnderRetracts TorAmp`;
  `bridge/view`: transport of a retract through tensoring with `ℱ[0]`, then through the homology
    functor, and finally through the generic retract-stability owner for `IsZero`.

This file therefore exposes the retract-stability instance once and derives the two source-facing
biproduct lemmas directly from the generic owner API. Inside the owner proof, both the mapped
retract and the zero-object conclusion are handled through owner-level retract transport rather
than by rebuilding the `IsZero` witness by hand. -/

/-- Objects of `D(\mathcal O)` with tor-amplitude in `[a, b]` are stable under retracts/direct
summands. -/
instance hasTorAmplitudeIn_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts TorAmp where
  of_retract h hE := by
    rw [hasTorAmplitudeIn_iff] at hE ⊢
    intro ℱ i hi
    let S := (DerivedCategory.singleFunctor Mod (0 : ℤ)).obj ℱ
    exact prop_of_retract (fun X : AddCommGrpCat.{max u v} ↦ IsZero X)
      (h.map (tensorRight S ⋙ DerivedCategory.homologyFunctor Mod i))
      (hE ℱ i hi)

-- Proof sketch: tor-amplitude in `[a, b]` is treated as the object property `TorAmp` on
-- `D(\mathcal O)`. Once this property is known to be stable under retracts, the left summand of
-- `K ⊞ L` is obtained from the canonical retract `K ↪ K ⊞ L ↠ K`, so the conclusion is the
-- generic owner lemma `of_biprod_left`.
/-- Lemma 21.46.8: if `K ⊞ L` has tor-amplitude in `[a, b]`, then `K` has tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_left_of_biprod
    (K L : DMod) (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn K a b :=
  of_biprod_left TorAmp hKL

-- Proof sketch: use the same retract-stability owner `TorAmp`; the right summand is a retract of
-- `K ⊞ L` via the canonical maps `L ↪ K ⊞ L ↠ L`, so `of_biprod_right` gives the conclusion
-- immediately.
/-- If `K ⊞ L` has tor-amplitude in `[a, b]`, then `L` has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_right_of_biprod
    (K L : DMod) (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn L a b :=
  of_biprod_right TorAmp hKL

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_46_9 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪
local notation "Mod" => RingedSite.Hom.ModuleCat X
local notation "DMod" => DerivedCategory Mod

variable [Abelian Mod]
variable [CategoryWithHomology Mod]

local instance instHasDerivedCategoryMod : HasDerivedCategory Mod :=
  HasDerivedCategory.standard Mod

/- Domain-style sampling for Lemma 21.46.9:
- primary domain: bounded-above and tor-amplitude bounds for derived reduction along the quotient
  family `\mathcal O / \mathcal I^n`;
- sampled owner declarations:
  `CategoryTheory.DerivedCategory.IsLE`,
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`,
  `ringedSiteModuleCategory`;
- best owner abstraction:
  the bounded-above owner datum here is the existence of an upper bound `∃ b, IsLE b`, while the
  stronger source-facing conclusion still records a single explicit uniform cohomological bound
  `(quotientBaseChange n).IsLE b`;
  tor-amplitude is already owned by `HasTorAmplitudeIn`;
- primitive data:
  the family `quotientBaseChange`, the bounded-above owner hypothesis on the mod-`I` stage, and
  the interval endpoints `a`, `b`;
- derived API:
  the source-facing propagation statements from the mod-`I` stage to all quotient-power stages.

Source/core/bridge triage:
- `source-facing`: the two propagation theorems matching Lemma 21.46.9;
  - `core/canonical`: `DerivedCategory.IsLE` and `HasTorAmplitudeIn`;
- `bridge/view`: this file, which states the source propagation results directly in terms of those
  owner predicates rather than duplicating their entrywise homology tests.
-/

/- Lemma 21.46.9 (1): let `idealQuotient n` model the ambient `\mathcal O`-module
`\mathcal O / \mathcal I^n` for `n ≥ 1`. If `K \otimes_{\mathcal O}^{\mathbf L}
(\mathcal O / \mathcal I)` is bounded above, then the family
`K \otimes_{\mathcal O}^{\mathbf L} (\mathcal O / \mathcal I^n)` is uniformly bounded above for
all `n ≥ 1`. -/
theorem derivedTensor_idealQuotientPowers_uniformly_boundedAbove
    (quotientBaseChange : ℕ → DMod)
    (h₁ : ∃ b : ℤ, (quotientBaseChange 1).IsLE b) :
    ∃ b : ℤ, ∀ n : ℕ, 1 ≤ n → (quotientBaseChange n).IsLE b
  := by
    sorry

section QuotientPowerTorAmplitude

variable (quotientSheaf : ℕ → Sheaf J CommRingCat.{max u v})

private abbrev quotientRingedSite (n : ℕ) : RingedSite :=
  RingedSite.ofCommRingSheaf J (quotientSheaf n)

private abbrev quotientModuleCat (n : ℕ) :=
  RingedSite.Hom.ModuleCat (quotientRingedSite quotientSheaf n)

private abbrev quotientDerived (n : ℕ) :=
  RingedSite.Hom.ModuleDerived (quotientRingedSite quotientSheaf n)

variable [hAbelianModQ : ∀ n : ℕ, Abelian (quotientModuleCat quotientSheaf n)]
variable [hCategoryWithHomologyModQ : ∀ n : ℕ, CategoryWithHomology (quotientModuleCat quotientSheaf n)]
variable [hMonoidalDModQ : ∀ n : ℕ, MonoidalCategory (quotientDerived quotientSheaf n)]

local instance instAbelianModQ (n : ℕ) :
    Abelian (quotientModuleCat quotientSheaf n) :=
  hAbelianModQ n

local instance instCategoryWithHomologyModQ (n : ℕ) :
    CategoryWithHomology (quotientModuleCat quotientSheaf n) :=
  hCategoryWithHomologyModQ n

local instance instMonoidalDerivedModQ (n : ℕ) :
    MonoidalCategory (quotientDerived quotientSheaf n) :=
  hMonoidalDModQ n

local instance instHasDerivedCategoryModQ (n : ℕ) :
    HasDerivedCategory (quotientModuleCat quotientSheaf n) :=
  HasDerivedCategory.standard (quotientModuleCat quotientSheaf n)

/- Lemma 21.46.9 (2): let `quotientSheaf n` model the quotient ringed site
`\mathcal O / \mathcal I^n` for `n ≥ 1`, and let `quotientBaseChange n` model
`K \otimes_{\mathcal O}^{\mathbf L} (\mathcal O / \mathcal I^n)` as an object of
`D(\mathcal O / \mathcal I^n)`. If the mod-`I` stage has tor-amplitude in `[a, b]`, then every
quotient-power stage has tor-amplitude in `[a, b]`. -/
theorem derivedTensor_idealQuotientPowers_hasTorAmplitudeIn
    (quotientBaseChange :
      ∀ n : ℕ, RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J (quotientSheaf n)))
    (a b : ℤ)
    (h₁ : HasTorAmplitudeIn
      (RingedSite.ofCommRingSheaf J (quotientSheaf 1))
      (quotientBaseChange 1) a b) :
    ∀ n : ℕ, 1 ≤ n →
      HasTorAmplitudeIn (RingedSite.ofCommRingSheaf J (quotientSheaf n))
        (quotientBaseChange n) a b
  := by
    sorry

end QuotientPowerTorAmplitude

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_46_10 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [LocallySmall.{u} C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/-- A sheaf of commutative rings on a site, regarded as a `RingCat`-valued sheaf. -/
private abbrev ringedSiteRingSheaf
    (𝒪 : Sheaf J CommRingCat.{u}) :
    Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules
    (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules (ringedSiteRingSheaf 𝒪)

variable [Abelian (RingedSiteModules 𝒪)]
variable [CategoryWithHomology (RingedSiteModules 𝒪)]
variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]
variable [MonoidalCategory (DerivedCategory (RingedSiteModules 𝒪))]

local notation "DMod" => DerivedCategory (RingedSiteModules 𝒪)

/-- The commutative stalk ring `\mathcal O_p` at a point `p` of the ringed site. -/
private abbrev pointCommPresheafStalk
    (𝒪 : Sheaf J CommRingCat.{u})
    (p : GrothendieckTopology.Point.{u} J) :
    CommRingCat.{u} :=
  (p.presheafFiber : (Cᵒᵖ ⥤ CommRingCat.{u}) ⥤ CommRingCat.{u}).obj 𝒪.obj

/-- The forgotten `RingCat` stalk of `\mathcal O` identifies canonically with the commutative
stalk ring `\mathcal O_p`. -/
private abbrev pointStalkRingEquivPointCommPresheafStalk
    (p : GrothendieckTopology.Point.{u} J) :
    ↑(CategoryTheory.point_stalk_ring p (ringedSiteRingSheaf 𝒪)) ≃+*
      ↑(pointCommPresheafStalk 𝒪 p) :=
  ((p.presheafFiberCompIso (forget₂ CommRingCat RingCat)).app 𝒪.obj).ringCatIsoToRingEquiv

/-- The stalk functor on `\mathcal O`-modules at `p`, retargeted to modules over the commutative
stalk ring `\mathcal O_p`. -/
private abbrev pointModuleFunctor
    (p : GrothendieckTopology.Point.{u} J) :
    RingedSiteModules 𝒪 ⥤ ModuleCat (pointCommPresheafStalk 𝒪 p) :=
  CategoryTheory.point_sheaf_module_stalk_functor p (ringedSiteRingSheaf 𝒪) ⋙
    ModuleCat.restrictScalars (pointStalkRingEquivPointCommPresheafStalk p).symm.toRingHom

-- Proof sketch: `CategoryTheory.point_sheaf_module_stalk_functor` is exact by Lemma `18.36.3`,
-- and restriction of scalars along the canonical ring equivalence between the forgotten stalk ring
-- and the commutative stalk ring preserves exact sequences.
/-- The point-stalk functor on `\mathcal O`-modules is exact. -/
private theorem pointModuleFunctor_exact
    (p : GrothendieckTopology.Point.{u} J) :
    exactFunctor (RingedSiteModules 𝒪) (ModuleCat (pointCommPresheafStalk 𝒪 p))
      (pointModuleFunctor p) := sorry

/-- The exact-functor package attached to the point-stalk functor on `\mathcal O`-modules. -/
private abbrev pointModuleExactFunctor
    (p : GrothendieckTopology.Point.{u} J) :
    RingedSiteModules 𝒪 ⥤ₑ ModuleCat (pointCommPresheafStalk 𝒪 p) :=
  let F : RingedSiteModules 𝒪 ⥤ ModuleCat (pointCommPresheafStalk 𝒪 p) := pointModuleFunctor p
  let _ : PreservesFiniteLimits F :=
    ((CategoryTheory.exactFunctor_iff F).mp (pointModuleFunctor_exact p)).1
  let _ : PreservesFiniteColimits F :=
    ((CategoryTheory.exactFunctor_iff F).mp (pointModuleFunctor_exact p)).2
  ExactFunctor.of F

-- Proof sketch: both the site-theoretic stalk functor and restriction of scalars are additive,
-- so the exact point-stalk functor is additive as well.
/-- The exact point-stalk functor on `\mathcal O`-modules is additive. -/
private theorem pointModuleExactFunctor_additive
    (p : GrothendieckTopology.Point.{u} J) :
    let F : RingedSiteModules 𝒪 ⥤ ModuleCat (pointCommPresheafStalk 𝒪 p) := pointModuleFunctor p
    F.Additive := sorry

/-- The derived point-stalk functor `E ↦ E_p` from `D(\mathcal O)` to `D(\mathcal O_p)`. -/
private abbrev pointStalkDerived
    (p : GrothendieckTopology.Point.{u} J) :
    DMod ⥤ DerivedCategory (ModuleCat (pointCommPresheafStalk 𝒪 p)) :=
  let F :
      RingedSiteModules 𝒪 ⥤ ModuleCat (pointCommPresheafStalk 𝒪 p) := pointModuleFunctor p
  let _ : F.Additive :=
    show F.Additive from pointModuleExactFunctor_additive p
  let _ : PreservesFiniteLimits F :=
    ((CategoryTheory.exactFunctor_iff F).mp (pointModuleFunctor_exact p)).1
  let _ : PreservesFiniteColimits F :=
    ((CategoryTheory.exactFunctor_iff F).mp (pointModuleFunctor_exact p)).2
  F.mapDerivedCategory

-- Proof sketch: regard the point stalk as the exact stalk functor on `\mathcal O`-modules and
-- apply the pullback-style tor-amplitude preservation statement from Lemma `21.46.5` to this
-- pointwise realization of `E_p`.
/-- If `E` has tor-amplitude in `[a, b]`, then the derived point stalk `E_p` has tor-amplitude in
`[a, b]` over the stalk ring `\mathcal O_p`. -/
theorem hasTorAmplitudeIn_pointStalkDerived
    (E : DMod) (a b : ℤ) (hE : HasTorAmplitudeIn E a b)
    (p : GrothendieckTopology.Point.{u} J) :
    CategoryTheory.HasTorAmplitudeIn ((pointStalkDerived p).obj E) a b := sorry

-- Proof sketch: the forward implication is `hasTorAmplitudeIn_pointStalkDerived`. For the
-- converse, test the defining homology-vanishing condition for `HasTorAmplitudeIn E a b` against an
-- arbitrary `\mathcal O`-module; after passing to every point stalk, the corresponding stalkwise
-- homology vanishes by the pointwise tor-amplitude hypothesis, and Lemma `18.14.4` lets one
-- conclude globally when the site has enough points.
/-- Lemma 21.46.10: if the ringed site `(\mathcal C, \mathcal O)` has enough points, then an
object `E` of `D(\mathcal O)` has tor-amplitude in `[a, b]` if and only if, for every point `p`
of the site, the derived point stalk `E_p` of `E` has tor-amplitude in `[a, b]` over
`\mathcal O_p`. -/
theorem hasTorAmplitudeIn_iff_forall_pointStalkDerived_of_hasEnoughPoints
    [GrothendieckTopology.HasEnoughPoints.{u} J]
    (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∀ p : GrothendieckTopology.Point.{u} J,
        CategoryTheory.HasTorAmplitudeIn ((pointStalkDerived p).obj E) a b := sorry

end

end SheafOfModules.RingedSite
