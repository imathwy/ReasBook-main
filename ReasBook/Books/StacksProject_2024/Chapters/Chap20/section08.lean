import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_8_1 (from Chap20) -/
open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.8.1:
- primary domain: restriction maps on sections of an injective `\mathcal O_X`-module over nested
  opens of a ringed space;
- sampled owner declarations:
  `injective_module_restriction_surjective_of_mono`,
  `moduleSheafRestrictionToOpen`,
  `moduleSheafExtensionByZeroAdjunction`,
  `TopCat.Sheaf.IsFlasque`;
- best owner abstraction: the general site-level owner
  `injective_module_restriction_surjective_of_mono`, with the ringed-space restriction functor as
  the geometric specialization and flasqueness only as a later derived consequence;
- primitive data: an injective object `ℐ : (RingedSpace.Modules X)` and an inclusion `U' ≤ U`, equivalently
  the canonical monomorphism `homOfLE hU'U : U' ⟶ U`;
- derived API: surjectivity of the section restriction map `ℐ(U) → ℐ(U')`.

Source/core/bridge triage:
- `source-facing`: the explicit surjectivity statement on nested opens from the textbook;
- `core/canonical`: the project-level site theorem
  `injective_module_restriction_surjective_of_mono`;
- `bridge/view`: specialize that theorem to the site of opens of the ringed space and the mono
  `homOfLE hU'U`.

This file keeps the source-facing statement as the main public entry, but its proof should now be a
thin specialization of the canonical site-level owner rather than a parallel local argument. -/

variable {X : RingedSpace.{u}} {U' U : Opens X}

-- Proof sketch: this is the ringed-space specialization of the project's general site-level owner
-- `injective_module_restriction_surjective_of_mono`, applied to the canonical mono
-- `homOfLE hU'U : U' ⟶ U`.
/-- Lemma 20.8.1: if `\mathcal I` is an injective `\mathcal O_X`-module and `U' \subseteq U` are
open subsets of `X`, then the restriction map `\mathcal I(U) \to \mathcal I(U')` is surjective.
-/
theorem module_sections_restriction_surjective_of_injective
    (ℐ : (RingedSpace.Modules X)) (hℐ : Injective ℐ) (hU'U : U' ≤ U) :
    Function.Surjective (ℐ.val.map (homOfLE hU'U).op) :=
  injective_module_restriction_surjective_of_mono (homOfLE hU'U) ℐ hℐ

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_8_2_Mayer_Vietoris (from Chap20) -/
open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Mayer-Vietoris in sheaf cohomology on ringed spaces:
- primary domain: sheaf cohomology of `\mathcal O_X`-modules on a ringed space, specialized from
  the site-theoretic Mayer-Vietoris owner API;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.toSheaf`,
  `Opens.mayerVietorisSquare`,
  `GrothendieckTopology.MayerVietorisSquare.sequence`;
- best owner abstraction: the core Mayer-Vietoris owner is the site-theoretic
  `GrothendieckTopology.MayerVietorisSquare`, while the ringed-space specialization should keep the
  module datum as `ℱ : (RingedSpace.Modules X)` and derive the underlying additive sheaf via
  `SheafOfModules.toSheaf`;
- primitive-vs-derived split:
  primitive data are the ringed space `X`, opens `U,V`, the covering equation `hUV`, the module
  `ℱ : (RingedSpace.Modules X)`, and the degree data;
  the additive sheaf, the Mayer-Vietoris square of opens, and the cohomology maps are derived API
  and should not be reintroduced as parallel owner declarations.

Source/core/bridge triage:
- `source-facing`: the Mayer-Vietoris six-term segment for a cover `X = U ∪ V`;
- `core/canonical`: `Opens.mayerVietorisSquare U V` and its site-theoretic cohomology sequence;
- `bridge/view`: the identification of the union object `U ⊔ V` with `⊤` via `hUV`, and passage
  from an `\mathcal O_X`-module to its underlying additive sheaf. -/

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

private noncomputable abbrev moduleToAddSheaf :
    (RingedSpace.Modules X) ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))

private abbrev mvSquare (U V : Opens X) :=
  Opens.mayerVietorisSquare U V

/-- The morphism on degree-`n` cohomology induced by a morphism of `\mathcal O_X`-modules,
evaluated on an open subset `U`. -/
private abbrev ringedSpaceModuleCohomologyMap
    {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢) (n : ℕ) (U : Opens X) :
    (moduleToAddSheaf.obj ℱ).H' n U ⟶ (moduleToAddSheaf.obj 𝒢).H' n U :=
  ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
      (moduleToAddSheaf.map φ)).app (op U)

private noncomputable abbrev ringedSpaceModuleMayerVietorisUnionSequence
    (U V : Opens X) (ℱ : (RingedSpace.Modules X)) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  (mvSquare U V).sequence (moduleToAddSheaf.obj ℱ) n₀ n₁ h

/-- The canonical Mayer-Vietoris six-term cohomology segment attached to a cover `X = U ∪ V`. -/
noncomputable def ringedSpaceModuleMayerVietorisSequence
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : (RingedSpace.Modules X))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  let F := moduleToAddSheaf.obj ℱ
  let S := mvSquare U V
  ComposableArrows.mk₅
    ((F.cohomologyPresheaf n₀).map (eqToHom hUV).op ≫ S.toBiprod F n₀)
    (S.fromBiprod F n₀)
    (S.δ F n₀ n₁ h ≫ (F.cohomologyPresheaf n₁).map (eqToHom hUV.symm).op)
    ((F.cohomologyPresheaf n₁).map (eqToHom hUV).op ≫ S.toBiprod F n₁)
    (S.fromBiprod F n₁)

private noncomputable def ringedSpaceModuleMayerVietorisSequenceIso
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : (RingedSpace.Modules X))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ringedSpaceModuleMayerVietorisSequence U V hUV ℱ n₀ n₁ h ≅
      ringedSpaceModuleMayerVietorisUnionSequence U V ℱ n₀ n₁ h :=
  let F := moduleToAddSheaf.obj ℱ
  let e₀ := (F.cohomologyPresheaf n₀).mapIso (eqToIso hUV).op
  let e₃ := (F.cohomologyPresheaf n₁).mapIso (eqToIso hUV).op
  ComposableArrows.isoMk₅ e₀ (Iso.refl _) (Iso.refl _) e₃ (Iso.refl _) (Iso.refl _)
    (by sorry)
    (by sorry)
    (by sorry)
    (by sorry)
    (by sorry)

-- Proof sketch: specialize the canonical site-theoretic Mayer-Vietoris exact sequence to the
-- underlying abelian sheaf of the `\mathcal O_X`-module `ℱ`, with the Mayer-Vietoris square of
-- the opens `U` and `V`; the hypothesis `hUV` identifies the union open `U ⊔ V` with `X`.
/-- Lemma 20.8.2 (Mayer-Vietoris): if a ringed space `X` is covered by two opens `U` and `V`,
then for every `\mathcal O_X`-module `\mathcal F` and every `n₀ + 1 = n₁`, the canonical
Mayer-Vietoris segment
`H^{n₀}(X, \mathcal F) ⟶ H^{n₀}(U, \mathcal F) ⊞ H^{n₀}(V, \mathcal F) ⟶
H^{n₀}(U ∩ V, \mathcal F) ⟶ H^{n₁}(X, \mathcal F) ⟶
H^{n₁}(U, \mathcal F) ⊞ H^{n₁}(V, \mathcal F) ⟶ H^{n₁}(U ∩ V, \mathcal F)`
is exact. -/
theorem ringedSpaceModule_mayerVietoris_sequence_exact
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (ℱ : (RingedSpace.Modules X))
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (ringedSpaceModuleMayerVietorisSequence U V hUV ℱ n₀ n₁ h).Exact := by
  refine exact_of_iso (ringedSpaceModuleMayerVietorisSequenceIso U V hUV ℱ n₀ n₁ h) ?_
  simpa [ringedSpaceModuleMayerVietorisUnionSequence, mvSquare] using
    (mvSquare U V).sequence_exact (moduleToAddSheaf.obj ℱ) n₀ n₁ h

private theorem ringedSpaceModuleCohomologyMap_toBiprod_natural
    (U V : Opens X) {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢) (n : ℕ) :
    (mvSquare U V).toBiprod (moduleToAddSheaf.obj ℱ) n ≫
        biprod.map (ringedSpaceModuleCohomologyMap φ n U)
          (ringedSpaceModuleCohomologyMap φ n V) =
      ringedSpaceModuleCohomologyMap φ n (U ⊔ V) ≫
        (mvSquare U V).toBiprod (moduleToAddSheaf.obj 𝒢) n := sorry

private theorem ringedSpaceModuleCohomologyMap_fromBiprod_natural
    (U V : Opens X) {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢) (n : ℕ) :
    (mvSquare U V).fromBiprod (moduleToAddSheaf.obj ℱ) n ≫
        ringedSpaceModuleCohomologyMap φ n (U ⊓ V) =
      biprod.map (ringedSpaceModuleCohomologyMap φ n U)
          (ringedSpaceModuleCohomologyMap φ n V) ≫
        (mvSquare U V).fromBiprod (moduleToAddSheaf.obj 𝒢) n := sorry

private theorem ringedSpaceModuleCohomologyMap_δ_natural
    (U V : Opens X) {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (mvSquare U V).δ (moduleToAddSheaf.obj ℱ) n₀ n₁ h ≫
        ringedSpaceModuleCohomologyMap φ n₁ (U ⊔ V) =
      ringedSpaceModuleCohomologyMap φ n₀ (U ⊓ V) ≫
        (mvSquare U V).δ (moduleToAddSheaf.obj 𝒢) n₀ n₁ h := sorry

private noncomputable def ringedSpaceModuleMayerVietorisUnionSequenceMap
    (U V : Opens X) {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ringedSpaceModuleMayerVietorisUnionSequence U V ℱ n₀ n₁ h ⟶
      ringedSpaceModuleMayerVietorisUnionSequence U V 𝒢 n₀ n₁ h :=
  ComposableArrows.homMk₅
    (ringedSpaceModuleCohomologyMap φ n₀ (U ⊔ V))
    (biprod.map (ringedSpaceModuleCohomologyMap φ n₀ U)
      (ringedSpaceModuleCohomologyMap φ n₀ V))
    (ringedSpaceModuleCohomologyMap φ n₀ (U ⊓ V))
    (ringedSpaceModuleCohomologyMap φ n₁ (U ⊔ V))
    (biprod.map (ringedSpaceModuleCohomologyMap φ n₁ U)
      (ringedSpaceModuleCohomologyMap φ n₁ V))
    (ringedSpaceModuleCohomologyMap φ n₁ (U ⊓ V))
    (ringedSpaceModuleCohomologyMap_toBiprod_natural U V φ n₀)
    (ringedSpaceModuleCohomologyMap_fromBiprod_natural U V φ n₀)
    (ringedSpaceModuleCohomologyMap_δ_natural U V φ n₀ n₁ h)
    (ringedSpaceModuleCohomologyMap_toBiprod_natural U V φ n₁)
    (ringedSpaceModuleCohomologyMap_fromBiprod_natural U V φ n₁)

/-- The morphism of Mayer-Vietoris sequences induced by a morphism of `\mathcal O_X`-modules. -/
noncomputable def ringedSpaceModuleMayerVietorisSequenceMap
    (U V : Opens X) (hUV : U ⊔ V = ⊤) {ℱ 𝒢 : (RingedSpace.Modules X)} (φ : ℱ ⟶ 𝒢)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ringedSpaceModuleMayerVietorisSequence U V hUV ℱ n₀ n₁ h ⟶
      ringedSpaceModuleMayerVietorisSequence U V hUV 𝒢 n₀ n₁ h :=
  (ringedSpaceModuleMayerVietorisSequenceIso U V hUV ℱ n₀ n₁ h).hom ≫
    ringedSpaceModuleMayerVietorisUnionSequenceMap U V φ n₀ n₁ h ≫
      (ringedSpaceModuleMayerVietorisSequenceIso U V hUV 𝒢 n₀ n₁ h).inv

end AlgebraicGeometry

/-! ### Lemma_20_8_3_Relative_Mayer_Vietoris (from Chap20) -/
open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The structure-sheaf morphism `\mathcal O_Y ⟶ f_* \mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev ringedSpaceCommRingSheafPushforwardMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a morphism of ringed spaces after forgetting commutativity. -/
noncomputable abbrev ringedSpacePushforwardStructureSheafHom
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    ringedSpaceRingCatSheaf Y ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (ringedSpaceRingCatSheaf X) :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology Y)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).map
      (ringedSpaceCommRingSheafPushforwardMap f)

/-- The direct-image functor on `\mathcal O_X`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev ringedSpaceModulePushforward
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    SheafOfModules (ringedSpaceRingCatSheaf X) ⥤
      SheafOfModules (ringedSpaceRingCatSheaf Y) :=
  SheafOfModules.pushforward (ringedSpacePushforwardStructureSheafHom f)

/-- The restriction of an `\mathcal O_X`-module to an open subspace. -/
abbrev restrictedRingedSpaceModule {X : RingedSpace.{u}}
    (U : Opens X.carrier) (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :=
  (moduleSheafRestrictionToOpen U (ringedSpaceRingCatSheaf X)).obj ℱ

/-- Pushforward of modules from an open subspace back to the ambient ringed space. -/
noncomputable abbrev ringedSpaceModulePushforwardFromOpen
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj
        (ringedSpaceRingCatSheaf X)) ⥤
      SheafOfModules (ringedSpaceRingCatSheaf X) :=
  SheafOfModules.pushforward
    (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
      (ringedSpaceRingCatSheaf X)))

/-- The composite direct image `a_*` obtained by first pushing forward from an open subspace to
`X` and then along `f : X ⟶ Y`. -/
abbrev ringedSpaceModulePushforwardAlongOpen
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (U : Opens X.carrier) :=
  ringedSpaceModulePushforwardFromOpen U ⋙ ringedSpaceModulePushforward f

/-- The biproduct of the two open-subspace direct images appearing in relative Mayer-Vietoris. -/
abbrev relativeMayerVietorisMiddleTerm
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (U V : Opens X.carrier)
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :=
  ((ringedSpaceModulePushforwardAlongOpen f U).obj (restrictedRingedSpaceModule U ℱ)) ⊞
    ((ringedSpaceModulePushforwardAlongOpen f V).obj (restrictedRingedSpaceModule V ℱ))

/-- The direct-image term coming from the intersection `U ∩ V` in relative Mayer-Vietoris. -/
abbrev relativeMayerVietorisIntersectionTerm
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (U V : Opens X.carrier)
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :=
  (ringedSpaceModulePushforwardAlongOpen f (U ⊓ V)).obj
    (restrictedRingedSpaceModule (U ⊓ V) ℱ)

/-- The map on the left term induced by a morphism of `\mathcal O_X`-modules. -/
abbrev relativeMayerVietorisLeftMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    {ℱ 𝒢 : SheafOfModules (ringedSpaceRingCatSheaf X)} (φ : ℱ ⟶ 𝒢) :=
  (ringedSpaceModulePushforward f).map φ

/-- The map on the middle biproduct term induced by a morphism of `\mathcal O_X`-modules. -/
abbrev relativeMayerVietorisMiddleMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (U V : Opens X.carrier)
    {ℱ 𝒢 : SheafOfModules (ringedSpaceRingCatSheaf X)} (φ : ℱ ⟶ 𝒢) :=
  biprod.map
    ((ringedSpaceModulePushforwardAlongOpen f U).map
      ((moduleSheafRestrictionToOpen U (ringedSpaceRingCatSheaf X)).map φ))
    ((ringedSpaceModulePushforwardAlongOpen f V).map
      ((moduleSheafRestrictionToOpen V (ringedSpaceRingCatSheaf X)).map φ))

/-- The map on the intersection term induced by a morphism of `\mathcal O_X`-modules. -/
abbrev relativeMayerVietorisIntersectionMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (U V : Opens X.carrier)
    {ℱ 𝒢 : SheafOfModules (ringedSpaceRingCatSheaf X)} (φ : ℱ ⟶ 𝒢) :=
  (ringedSpaceModulePushforwardAlongOpen f (U ⊓ V)).map
    ((moduleSheafRestrictionToOpen (U ⊓ V) (ringedSpaceRingCatSheaf X)).map φ)

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(ringedSpaceModulePushforward f).Additive]
variable [HasInjectiveResolutions (SheafOfModules (ringedSpaceRingCatSheaf X))]

-- Proof sketch: start from the standard short exact sequence
-- `0 ⟶ ℱ ⟶ j_{U,*}(ℱ|_U) ⊞ j_{V,*}(ℱ|_V) ⟶ j_{U∩V,*}(ℱ|_{U∩V}) ⟶ 0`
-- on `X`, apply the left exact functor `f_*`, and take the first connecting morphism in the
-- associated long exact sequence of right derived functors.
/-- Lemma 20.8.3 (Relative Mayer-Vietoris): if `f : X ⟶ Y` is a morphism of ringed spaces and
`X = U ∪ V`, then for every `\mathcal O_X`-module `\mathcal F` there is an initial exact segment
`0 ⟶ f_* \mathcal F ⟶ a_*(\mathcal F|_U) ⊞ b_*(\mathcal F|_V) ⟶
c_*(\mathcal F|_{U \cap V}) ⟶ R^1 f_* \mathcal F`
of the relative Mayer-Vietoris long exact sequence. -/
theorem ringedSpaceModule_relativeMayerVietoris
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (ℱ : SheafOfModules (ringedSpaceRingCatSheaf X)) :
    ∃ α : (ringedSpaceModulePushforward f).obj ℱ ⟶ relativeMayerVietorisMiddleTerm f U V ℱ,
      ∃ β : relativeMayerVietorisMiddleTerm f U V ℱ ⟶
          relativeMayerVietorisIntersectionTerm f U V ℱ,
        ∃ δ : relativeMayerVietorisIntersectionTerm f U V ℱ ⟶
            ((ringedSpaceModulePushforward f).rightDerived 1).obj ℱ,
          Mono α ∧ (ComposableArrows.mk₃ α β δ).Exact := sorry

-- Proof sketch: choose relative Mayer-Vietoris segments for `ℱ` and `𝒢` from the previous
-- theorem, then use the naturality of restriction, of the biproduct maps, and of the connecting
-- morphism in the right-derived long exact sequence to obtain commuting squares.
/-- A morphism of `\mathcal O_X`-modules induces a compatible morphism between suitable choices of
the initial relative Mayer-Vietoris segments. -/
theorem ringedSpaceModule_relativeMayerVietoris_functorial
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    {ℱ 𝒢 : SheafOfModules (ringedSpaceRingCatSheaf X)} (φ : ℱ ⟶ 𝒢) :
    ∃ αℱ : (ringedSpaceModulePushforward f).obj ℱ ⟶ relativeMayerVietorisMiddleTerm f U V ℱ,
      ∃ βℱ : relativeMayerVietorisMiddleTerm f U V ℱ ⟶
          relativeMayerVietorisIntersectionTerm f U V ℱ,
        ∃ δℱ : relativeMayerVietorisIntersectionTerm f U V ℱ ⟶
            ((ringedSpaceModulePushforward f).rightDerived 1).obj ℱ,
          ∃ α𝒢 : (ringedSpaceModulePushforward f).obj 𝒢 ⟶ relativeMayerVietorisMiddleTerm f U V 𝒢,
            ∃ β𝒢 : relativeMayerVietorisMiddleTerm f U V 𝒢 ⟶
                relativeMayerVietorisIntersectionTerm f U V 𝒢,
              ∃ δ𝒢 : relativeMayerVietorisIntersectionTerm f U V 𝒢 ⟶
                  ((ringedSpaceModulePushforward f).rightDerived 1).obj 𝒢,
                Mono αℱ ∧ (ComposableArrows.mk₃ αℱ βℱ δℱ).Exact ∧
                  Mono α𝒢 ∧ (ComposableArrows.mk₃ α𝒢 β𝒢 δ𝒢).Exact ∧
                  relativeMayerVietorisLeftMap f φ ≫ α𝒢 =
                    αℱ ≫ relativeMayerVietorisMiddleMap f U V φ ∧
                  relativeMayerVietorisMiddleMap f U V φ ≫ β𝒢 =
                    βℱ ≫ relativeMayerVietorisIntersectionMap f U V φ ∧
                  relativeMayerVietorisIntersectionMap f U V φ ≫ δ𝒢 =
                    δℱ ≫ ((ringedSpaceModulePushforward f).rightDerived 1).map φ := sorry

end AlgebraicGeometry
