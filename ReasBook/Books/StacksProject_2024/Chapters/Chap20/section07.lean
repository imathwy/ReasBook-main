import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_7_1 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.7.1:
- primary domain: restriction of sheaves of modules to an open subspace of a ringed space and the
  induced comparison on sheaf cohomology;
- sampled owner declarations:
  `moduleSheafExtensionByZeroAdjunction`,
  `moduleSheafExtensionByZeroFromOpen_exact`,
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`,
  `openHypercohomology_isomorphic_restricted`;
- best owner abstraction: the restriction/extension-by-zero adjunction together with the ambient
  hypercohomology comparison on the open subspace;
- primitive data: a ringed space `X`, an open subset `U`, and a module sheaf `ℱ : (RingedSpace.Modules X)`;
- derived API: preservation of injective objects under restriction to `U`, and the degree-`p`
  cohomology comparison between sections over `U` and global sections of `ℱ|_U`.

Source/core/bridge triage:
- `source-facing`: the two textbook statements about restricting injective `\mathcal O_X`-modules
  and comparing cohomology on `U` with cohomology of the restricted module on `X|_U`;
- `core/canonical`: `moduleSheafExtensionByZeroAdjunction`,
  `moduleSheafExtensionByZeroFromOpen_exact`,
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`, and
  `openHypercohomology_isomorphic_restricted`;
- `bridge/view`: this file, which should remain a thin specialization to ordinary sheaf
  cohomology of a single `\mathcal O_X`-module rather than rebuilding the adjunction or derived
  comparison APIs locally. -/

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

/-- Lemma 20.7.1 (1): restriction of `\mathcal O_X`-modules to an open subspace preserves
injective objects, so an injective `\mathcal O_X`-module restricts to an injective
`\mathcal O_U`-module. -/
-- Proof sketch: by Lemma `6.31.8`, restriction to `U` is right adjoint to extension by zero
-- along the open immersion `j : U ↪ X`; the left adjoint is exact by Lemma `20.32.1`, hence it
-- preserves monomorphisms, and the standard adjunction criterion shows that the right adjoint
-- preserves injective objects.
instance moduleRestrictionToOpen_preservesInjectiveObjects :
    (moduleRestrictionToOpen X U).PreservesInjectiveObjects := by
  letI : PreservesFiniteLimits (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) :=
    ((CategoryTheory.exactFunctor_iff (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X))).mp
      (moduleSheafExtensionByZeroFromOpen_exact (X := X) U)).1
  letI : (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)).PreservesMonomorphisms :=
    inferInstance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (moduleSheafExtensionByZeroAdjunction U (RingedSpace.ringCatSheaf X))

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology U) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})]

/-- Lemma 20.7.1 (2): for a sheaf of `\mathcal O_X`-modules `\mathcal F`, the cohomology of the
open subspace `U` computed on `X` is canonically isomorphic to the cohomology of the restricted
`\mathcal O_U`-module `\mathcal F|_U`. -/
-- Proof sketch: this is the single-sheaf source-facing specialization of the canonical
-- hypercohomology comparison `openHypercohomology_isomorphic_restricted` from Lemma `20.32.2`.
-- On a module sheaf concentrated in degree `0`, both sides compute the same degree-`p`
-- cohomology groups as the textbook statement.
theorem ringedSpaceModuleCohomologyOnOpen_isomorphic_to_restricted
    (ℱ : (RingedSpace.Modules X)) (p : ℕ) :
    IsIsomorphic ((moduleUnderlyingSheaf ℱ).H' p U)
      (((SheafOfModules.toSheaf
          ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))).obj
          ((moduleRestrictionToOpen X U).obj ℱ)).H' p (⊤ : Opens U)) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_7_2 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 20.7.2:
- primary domain: sheaf cohomology of `\mathcal O_X`-modules on the opens site of a ringed space;
- sampled owner declarations:
  `GrothendieckTopology.Cover`,
  `GrothendieckTopology.Cover.Arrow`,
  `SheafOfModules.toSheaf`,
  `_root_.exists_cover_restrict_eq_zero_of_positive_cohomology_class`;
- best owner abstraction: the core owner is the general ringed-site theorem
  `_root_.exists_cover_restrict_eq_zero_of_positive_cohomology_class`, specialized here to the
  opens-site ringed space `(RingedSpace.ringCatSheaf X)`;
- primitive-vs-derived split:
  primitive data are the ringed space `X`, the module `ℱ : (RingedSpace.Modules X)`, the open
  `U : Opens X.carrier`, and the cohomology class `ξ`;
  the underlying additive sheaf and the restriction maps on cohomology are derived canonically by
  `SheafOfModules.toSheaf`;
- source/core/bridge triage:
  `source-facing`: local vanishing of a positive-degree cohomology class after refining by a
  cover of `U`;
  `core/canonical`: `_root_.exists_cover_restrict_eq_zero_of_positive_cohomology_class`;
  `bridge/view`: this ringed-space specialization along `(RingedSpace.ringCatSheaf X)`.
-/

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

local notation "JX" => Opens.grothendieckTopology X.carrier

-- Proof sketch: represent `ξ` by a cocycle in an injective resolution of `ℱ`. In positive degree
-- exactness identifies this cocycle locally with a coboundary, so after refining to a suitable
-- cover of `U` in the opens site its restrictions vanish in cohomology on every cover arrow.
/-- Lemma 20.7.2: every positive-degree cohomology class of a sheaf of `\mathcal O_X`-modules on
an open subspace `U` becomes zero after restricting to a suitable open covering of `U`. -/
lemma exists_cover_restrict_eq_zero_of_positive_cohomology_class
    (ℱ : (RingedSpace.Modules X)) {U : Opens X.carrier} {n : ℕ} (hn : 0 < n)
    (ξ : ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ).H' n U) :
    ∃ T : JX.Cover U, ∀ I : T.Arrow,
      ((((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ).cohomologyPresheaf n).map I.f.op) ξ = 0 :=
    by
  simpa [JX] using
    (_root_.exists_cover_restrict_eq_zero_of_positive_cohomology_class
      (𝒪 := (RingedSpace.ringCatSheaf X)) ℱ hn ξ)

end AlgebraicGeometry

/-! ### Lemma_20_7_3 (from Chap20) -/
namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 20.7.3:
- primary domain: higher direct images of `\mathcal O_X`-modules and the underlying abelian
  sheaves obtained by forgetting module structure;
- sampled declarations in this domain:
  `SheafOfModules.toSheaf`,
  `ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf`,
  `higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology`,
  `RingedSpace.higherDirectImageModule_underlyingSheaf_isomorphic_higherDirectImageAbelianSheaf`;
- best owner abstraction: the canonical owner for the present statement is the ringed-site theorem
  `higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology`;
- primitive-vs-derived split:
  the primitive data are the continuous functor between sites, the structure-sheaf map, the module
  sheaf, and the cohomological degree appearing in that owner theorem;
  the ringed-space language of opens, inverse-image opens, and `R^i f_*` is derived bridge API
  obtained by specializing the owner to the opens site of a ringed space.

Source/core/bridge triage:
- `source-facing`: the ringed-space statement that the underlying abelian sheaf of
  `R^i f_* \mathcal F` is the sheafification of `V ↦ H^i(f^{-1}(V), \mathcal F)`;
- `core/canonical`: `higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology`;
- `bridge/view`: later ringed-space declarations such as
  `RingedSpace.higherDirectImageModule_underlyingSheaf_isomorphic_higherDirectImageAbelianSheaf`,
  which compare the module-valued higher direct image with the abelian-sheaf one after this owner
  theorem has already identified the abelian-sheaf target.

This item introduces no new owner-level data, so the correct refinement is to recall the canonical
owner theorem directly instead of keeping a parallel ringed-space wrapper.
-/

open RingedSite.Hom

/- Lemma 20.7.3: for a morphism of ringed spaces `f : X ⟶ Y` and an `\mathcal O_X`-module
`\mathcal F`, the higher direct image sheaf `R^i f_* \mathcal F` is the sheaf associated to the
presheaf `V ↦ H^i(f^{-1}(V), \mathcal F)` on `Y`, with restriction maps induced by the standard
cohomology restriction morphisms. In the project API this is the ringed-space specialization of
the canonical ringed-site owner theorem below. -/
recall higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology

end AlgebraicGeometry

/-! ### Lemma_20_7_4 (from Chap20) -/
open CategoryTheory TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The `RingCat`-valued structure sheaf on an open subspace agrees with restricting the
ambient `RingCat`-valued structure sheaf to that open. -/
-- Proof sketch: unfold the open-subspace structure sheaf as pullback of the ambient
-- `CommRingCat`-valued structure sheaf, then commute the forgetful functor
-- `CommRingCat ⥤ RingCat` with this pullback.
private theorem restrict_ringCatSheaf_eq
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding) =
      (TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj ((RingedSpace.ringCatSheaf X)) := sorry

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- The image of the restriction of `f` to `f ⁻¹(V)` lands in the open subspace `V`. -/
-- Proof sketch: a point of `f ⁻¹(V)` is, by definition, a point of `X` whose image under `f`
-- lies in `V`, so the composite `f^{-1}(V) ⟶ X ⟶ Y` factors through the inclusion `V ↪ Y`.
private theorem restrictedMorphism_range_subset (V : Opens Y.carrier) :
    Set.range
        (((X.ofRestrict ((Opens.map f.hom.base).obj V).isOpenEmbedding) ≫ f).hom.base) ⊆
      Set.range (Y.ofRestrict V.isOpenEmbedding).hom.base := sorry

/-- The restriction `g : f^{-1}(V) ⟶ V` of a morphism of ringed spaces `f : X ⟶ Y` to an open
subspace `V ⊆ Y`. -/
noncomputable def restrictedMorphismToOpen (V : Opens Y.carrier) :
    X.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding :=
  InducedCategory.homMk
    (PresheafedSpace.IsOpenImmersion.lift
      (Y.ofRestrict V.isOpenEmbedding).hom
      (((X.ofRestrict ((Opens.map f.hom.base).obj V).isOpenEmbedding) ≫ f).hom)
      (restrictedMorphism_range_subset f V))

/-- The restriction of an `\mathcal O_X`-module to the open subspace `f^{-1}(V)`, transported to
the module category attached to the restricted ringed space. -/
noncomputable def restrictedModuleOnPreimageOpen
    (V : Opens Y.carrier) (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X))) :
    SheafOfModules
      (RingedSpace.ringCatSheaf (X.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding)) :=
  Eq.mp
    (congrArg SheafOfModules
      (restrict_ringCatSheaf_eq ((Opens.map f.hom.base).obj V)).symm)
    ((moduleSheafRestrictionToOpen ((Opens.map f.hom.base).obj V)
      ((RingedSpace.ringCatSheaf X))).obj ℱ)

/-- The higher direct image for the restricted morphism `g : f^{-1}(V) ⟶ V`, transported back to
the standard category of modules over the restricted ambient structure sheaf on `V`. -/
noncomputable def restrictedHigherDirectImageOnOpen
    (V : Opens Y.carrier)
    (p : ℕ)
    (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X)))
    [(RingedSpace.Hom.pushforward (restrictedMorphismToOpen f V)).Additive]
    [HasInjectiveResolutions
      (SheafOfModules
        (RingedSpace.ringCatSheaf (X.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding)))] :
    SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} V.inclusion').obj
      ((RingedSpace.ringCatSheaf Y))) :=
  Eq.mp
    (congrArg SheafOfModules
      (restrict_ringCatSheaf_eq V))
    (((RingedSpace.Hom.pushforward (restrictedMorphismToOpen f V)).rightDerived p).obj
      (restrictedModuleOnPreimageOpen f V ℱ))

variable [(RingedSpace.Hom.pushforward f).Additive]
variable [HasInjectiveResolutions (SheafOfModules ((RingedSpace.ringCatSheaf X)))]

/-- Lemma 20.7.4: for `g : f^{-1}(V) ⟶ V` obtained by restricting a morphism of ringed spaces
`f : X ⟶ Y` to an open subset `V ⊆ Y`, the restriction of `R^p f_* \mathcal F` to `V` is
canonically isomorphic to `R^p g_* (\mathcal F|_{f^{-1}(V)})`. -/
-- Proof sketch: apply Lemma `20.7.3` to both `f` and the restricted morphism `g`, and use
-- Lemma `20.7.1` to identify the cohomology groups on opens of `V` with the cohomology groups of
-- the restricted module on the corresponding opens of `f^{-1}(V)`, yielding the required
-- isomorphism class.
theorem ringedSpaceModulePushforward_rightDerived_restrict_isomorphic
    (p : ℕ)
    (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X)))
    (V : Opens Y.carrier)
    [(RingedSpace.Hom.pushforward (restrictedMorphismToOpen f V)).Additive]
    [HasInjectiveResolutions
      (SheafOfModules
        (RingedSpace.ringCatSheaf (X.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding)))] :
    IsIsomorphic
      ((moduleSheafRestrictionToOpen V ((RingedSpace.ringCatSheaf Y))).obj
        (((RingedSpace.Hom.pushforward f).rightDerived p).obj ℱ))
      (restrictedHigherDirectImageOnOpen f V p ℱ) := sorry

end AlgebraicGeometry

/-! ### Remark_20_7_5 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The underlying abelian sheaf of an `\mathcal O_X`-module on a ringed space. -/
private abbrev ringedSpaceModuleUnderlyingSheaf {X : RingedSpace.{u}}
    (F : SheafOfModules (ringedSpaceRingCatSheaf X)) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj F

-- Proof sketch: the sheafification functor on presheaves of `\mathcal O_X`-modules is exact and
-- the derived-functor description from Lemma `20.11.4` identifies the higher right derived
-- functors of the inclusion with the cohomology presheaves. This yields the restatement of Lemma
-- `20.7.2` used in the remark: the sheafification of the positive cohomology presheaf is zero.
/-- Remark 20.7.5: for a ringed space `(X, \mathcal O_X)`, the sheafification of the positive
cohomology presheaf `\underline H^p(\mathcal F)` of an `\mathcal O_X`-module vanishes; this is
the derived-functor reformulation underlying the alternative proof of Lemma `20.7.2`. -/
theorem positive_cohomologyPresheaf_sheafification_isZero
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : SheafOfModules (ringedSpaceRingCatSheaf X)) {p : ℕ} (hp : 0 < p) :
    IsZero
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((ringedSpaceModuleUnderlyingSheaf F).cohomologyPresheaf p)) := sorry

end AlgebraicGeometry
