import Mathlib
import StacksProject_2024.Chap17.Definition_17_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory TopologicalSpace
open CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

attribute [local instance] CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback

/- Domain-style sampling for Lemma 17.14.3:
- primary domain: local freeness of module sheaves on ringed spaces and its stability under the
  canonical pullback functor;
- inspected owner declarations:
  `SheafOfModules.IsLocallyFree`,
  `RingedSpace.Hom.pullback`,
  `SheafOfModules.RingedSite.pullback_isLocallyFree`,
  `RingedSpace.Modules`;
- best owner abstraction: the Chapter 18 owner theorem
  `SheafOfModules.RingedSite.pullback_isLocallyFree`, specialized to the pullback owner `f^*`
  on `RingedSpace.Modules`; at the moment that owner theorem lives in a file whose current source
  rebuild fails, so the present file isolates the remaining gap to the exact missing
  specialization step;
- primitive data: a ringed-space morphism `f : X ⟶ Y` and a locally free module sheaf
  `𝒢 : Y.Modules`;
- derived API: the thin ringed-space bridge theorem below, exposed at the `RingedSpace.Hom`
  owner layer without a parallel local helper wrapper.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that pulling back a locally free module on a ringed space
  again gives a locally free module;
- `core/canonical`: `RingedSpace.Modules`, `RingedSpace.Hom.pullback`,
  `SheafOfModules.IsLocallyFree`, and the intended Chapter 18 owner theorem
  `SheafOfModules.RingedSite.pullback_isLocallyFree`;
- `bridge/view`: the ringed-space specialization below, attached directly to the
  `RingedSpace.Hom` pullback layer. -/

variable {X Y : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y

/-- Helper for Lemma 17.14.3: the open subset `f^{-1}(V)` of `X` attached to an open
`V ⊆ Y`. -/
private abbrev preimageOpen (f : X ⟶ Y) (V : Opens Y) : Opens X :=
  (Opens.map f.hom.base).obj V

/-- Helper for Lemma 17.14.3: the composite from the restricted source
`X|_{f^{-1}(V)}` to `Y` lands in the restricted target `Y|_V`. -/
private theorem preimageOpen_range_subset
    (f : X ⟶ Y) (V : Opens Y) :
    Set.range
        ((((X.ofRestrict (preimageOpen f V).isOpenEmbedding).hom ≫ f.hom)).base) ⊆
      Set.range ((Y.ofRestrict V.isOpenEmbedding).hom.base) := by
  rintro y ⟨x, rfl⟩
  -- Proof comment: a point of `f^{-1}(V)` maps to a point of `V` by definition of the preimage
  -- open.
  exact ⟨⟨f.hom.base x.1, x.2⟩, rfl⟩

/-- Helper for Lemma 17.14.3: a morphism of restricted ringed spaces from
`X|_{f^{-1}(V)}` to `Y|_V` induced by `f`. -/
private noncomputable def pullbackToPreimageOpenMorphism
    (f : X ⟶ Y) (V : Opens Y) :
    X.restrict (preimageOpen f V).isOpenEmbedding ⟶
      Y.restrict V.isOpenEmbedding :=
  ⟨PresheafedSpace.IsOpenImmersion.lift
    (Y.ofRestrict V.isOpenEmbedding).hom
    ((X.ofRestrict (preimageOpen f V).isOpenEmbedding).hom ≫ f.hom)
    (preimageOpen_range_subset f V)⟩

/-- Helper for Lemma 17.14.3: the restricted morphism to `Y|_V` factors the composite
`X|_{f^{-1}(V)} ⟶ X ⟶ Y`. -/
private theorem pullbackToPreimageOpen_fac
    (f : X ⟶ Y) (V : Opens Y) :
    pullbackToPreimageOpenMorphism f V ≫ (Y.ofRestrict V.isOpenEmbedding).hom =
      (X.ofRestrict (preimageOpen f V).isOpenEmbedding).hom ≫ f := by
  -- Proof comment: the restricted morphism was defined using the universal-property lift through
  -- the open immersion `Y|_V ⟶ Y`, so the required factorization is exactly `lift_fac`.
  apply LocallyRingedSpace.Hom.ext'
  simpa [pullbackToPreimageOpenMorphism] using
    PresheafedSpace.IsOpenImmersion.lift_fac
      (Y.ofRestrict V.isOpenEmbedding).hom
      ((X.ofRestrict (preimageOpen f V).isOpenEmbedding).hom ≫ f.hom)
      (preimageOpen_range_subset f V)

/-- Helper for Lemma 17.14.3: pulling back the restriction `𝒢.over V` along the induced morphism
from `X|_{f^{-1}(V)}` agrees with restricting the ambient pullback `f^*𝒢` to `f^{-1}(V)`. -/
private theorem pullbackOverPreimageComparison
    (f : X ⟶ Y) (𝒢 : ModY) (V : Opens Y) :
    (RingedSpace.Hom.pullback (pullbackToPreimageOpenMorphism f V)).obj (𝒢.over V) ≅
      ((RingedSpace.Hom.pullback f).obj 𝒢).over (preimageOpen f V) := by
  let U := preimageOpen f V
  let iU : X.restrict U.isOpenEmbedding ⟶ X := (X.ofRestrict U.isOpenEmbedding).hom
  let iV : Y.restrict V.isOpenEmbedding ⟶ Y := (Y.ofRestrict V.isOpenEmbedding).hom
  let g : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding :=
    pullbackToPreimageOpenMorphism f V
  have leftIso :
      (RingedSpace.Hom.pullback g).obj (𝒢.over V) ≅
        (RingedSpace.Hom.pullback (g ≫ iV)).obj 𝒢 := by
    -- Proof comment: rewrite the iterated pullback `g^*(iV^*𝒢)` as pullback along the composite
    -- `g ≫ iV`.
    simpa [g, iV, SheafOfModules.over, RingedSpace.Hom.pullback] using
      (SheafOfModules.pullbackComp
        (RingedSpace.Hom.toRingCatSheafHom g)
        (RingedSpace.Hom.toRingCatSheafHom iV)).app 𝒢
  have rightIso :
      (((RingedSpace.Hom.pullback f).obj 𝒢).over U) ≅
        (RingedSpace.Hom.pullback (iU ≫ f)).obj 𝒢 := by
    -- Proof comment: the restriction of `f^*𝒢` to `U` is the pullback along `iU ≫ f`.
    simpa [U, iU, SheafOfModules.over, RingedSpace.Hom.pullback] using
      (SheafOfModules.pullbackComp
        (RingedSpace.Hom.toRingCatSheafHom iU)
        (RingedSpace.Hom.toRingCatSheafHom f)).app 𝒢
  have hfac :
      g ≫ iV = iU ≫ f := by
    simpa [U, iU, iV, g] using pullbackToPreimageOpen_fac (f := f) (V := V)
  have hfacRingCat :
      RingedSpace.Hom.toRingCatSheafHom (g ≫ iV) =
        RingedSpace.Hom.toRingCatSheafHom (iU ≫ f) :=
    congrArg RingedSpace.Hom.toRingCatSheafHom hfac
  have compIso :
      (RingedSpace.Hom.pullback (g ≫ iV)).obj 𝒢 ≅
        (RingedSpace.Hom.pullback (iU ≫ f)).obj 𝒢 :=
    (SheafOfModules.pullbackCongr hfacRingCat).app 𝒢
  -- Proof comment: after normalizing both sides to pullback along the same composite morphism,
  -- only the factorization equality `g ≫ iV = iU ≫ f` remains.
  exact leftIso ≪≫ compIso ≪≫ rightIso.symm

/-- Helper for Lemma 17.14.3: a free trivialization of `𝒢` on `V` should pull back to a free
trivialization on the preimage open `f^{-1}(V)`. -/
private theorem pullbackIsoFreeOnPreimage
    (f : X ⟶ Y) (𝒢 : ModY) {V : Opens Y} {I : Type u}
    (e : 𝒢.over V ≅
      (SheafOfModules.free.{u} I :
        SheafOfModules ((RingedSpace.ringCatSheaf Y).over V))) :
    Nonempty
      (((RingedSpace.Hom.pullback f).obj 𝒢).over (preimageOpen f V) ≅
        (SheafOfModules.free.{u} I :
          SheafOfModules
            ((RingedSpace.ringCatSheaf X).over (preimageOpen f V)))) := by
  let U := preimageOpen f V
  let g : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding :=
    pullbackToPreimageOpenMorphism f V
  let e' :
      (RingedSpace.Hom.pullback g).obj (𝒢.over V) ≅
        (SheafOfModules.free.{u} I :
          SheafOfModules ((RingedSpace.ringCatSheaf X).over U)) :=
    (RingedSpace.Hom.pullback g).mapIso e ≪≫
      SheafOfModules.pullbackObjFreeIso
        (RingedSpace.Hom.toRingCatSheafHom g) I
  -- Proof comment: first identify the restricted pullback with the pullback along the induced
  -- morphism `g : X|_{f^{-1}(V)} ⟶ Y|_V`, then pull back the chosen free trivialization on `V`.
  exact ⟨(pullbackOverPreimageComparison (f := f) (𝒢 := 𝒢) V).symm ≪≫ e'⟩

namespace RingedSpace.Hom

/-- Helper for Lemma 17.14.3: the remaining task is the opens-site specialization asserting that
pullback along a morphism of ringed spaces preserves the Chapter 17 point-neighborhood local
freeness predicate. -/
private theorem pullback_isLocallyFree_site_specialization
    (f : X ⟶ Y) (𝒢 : ModY) [𝒢.IsLocallyFree] :
    ((f^*).obj 𝒢).IsLocallyFree := by
  refine ⟨?_⟩
  intro x
  -- Proof comment: choose a free trivialization of `𝒢` around `f(x)` and then pull it back to the
  -- preimage open neighborhood of `x`.
  rcases SheafOfModules.IsLocallyFree.exists_open_neighborhood_iso_free
      (ℱ := 𝒢) (f.hom.base x) with
    ⟨V, hxV, I, hI⟩
  have hxpre : x ∈ preimageOpen f V := by
    simpa [preimageOpen] using hxV
  rcases pullbackIsoFreeOnPreimage
      (f := f) (𝒢 := 𝒢) (V := V) (I := I) (e := Classical.choice hI) with
    ⟨epre⟩
  exact ⟨preimageOpen f V, hxpre, I, ⟨epre⟩⟩

-- Proof sketch: once the site-level specialization above is available again, the public
-- ringed-space statement is just that owner-layer specialization.
/-- Lemma 17.14.3: for a morphism of ringed spaces
`f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)`, the pullback of a locally free
`\mathcal O_Y`-module is a locally free `\mathcal O_X`-module. -/
@[stacks 01C8]
theorem pullback_isLocallyFree
    (f : X ⟶ Y) (𝒢 : Y.Modules) [𝒢.IsLocallyFree] :
    ((f^*).obj 𝒢).IsLocallyFree :=
  pullback_isLocallyFree_site_specialization f 𝒢

end RingedSpace.Hom

end AlgebraicGeometry
