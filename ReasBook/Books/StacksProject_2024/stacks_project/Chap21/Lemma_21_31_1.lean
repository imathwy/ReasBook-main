import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import StacksProject_2024.Chap05.Lemma_5_3_4
import StacksProject_2024.Chap21.Definition_21_31_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open CategoryTheory.Limits
open Topology

/- Domain-style sampling for Lemma 21.31.1:
- primary domain: finite limits in the full subcategory `LCCat` of Hausdorff locally compact
  spaces, together with quasi-compactness of pullbacks;
- inspected owner declarations:
  `CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape`,
  `CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks`,
  `TopCat.pullbackIsoProdSubtype`,
  `TopCat.isTerminalPUnit`;
- best owner abstraction: the ambient limit-existence statements should be owned by the object
  property `HausdorffLocallyCompactObject` and transferred canonically to the full
  subcategory `LCCat`, while the fiber product itself stays the canonical `pullback`;
- primitive vs derived:
  primitive data are the owner object property `HausdorffLocallyCompactObject : ObjectProperty
  TopCat` and its closure under pullback
  shapes;
  `HasPullbacks`, `HasTerminal`, and `HasFiniteLimits` on `LCCat` are derived owner-level API from
  that closure, and compactness of `pullback f g` is further derived API on the canonical pullback
  object.

Source/core/bridge triage:
- `source-facing`: Lemma 21.31.1, asserting that `LC` has fiber products and a final object, hence
  finite limits, and that fiber products of quasi-compact objects are quasi-compact;
- `core/canonical`: the object property `HausdorffLocallyCompactObject`, the full
  subcategory `LCCat`, and the canonical limit owners `HasPullbacks`, `HasTerminal`,
  `HasFiniteLimits`, and `pullback`;
- `bridge/view`: the explicit TopCat model of a pullback as the closed subtype
  `{(x, y) | f x = g y}` supplied by `TopCat.pullbackIsoProdSubtype`. -/

namespace CategoryTheory

namespace ObjectProperty

/-- The object property defining `LCCat` is closed under isomorphisms. -/
instance hausdorffLocallyCompactObject_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms HausdorffLocallyCompactObject where
  of_iso {X Y} e hX := by
    let h : X ≃ₜ Y := TopCat.homeoOfIso e
    let hs : IsClosedEmbedding h.symm := h.symm.isClosedEmbedding
    letI : T2Space X := hX.1
    letI : LocallyCompactSpace X := hX.2
    exact ⟨h.t2Space, hs.locallyCompactSpace⟩

end ObjectProperty

namespace Limits

private theorem hausdorffLocallyCompact_pullbackSubtype
    {X Y Z : TopCat.{u}} [T2Space X] [LocallyCompactSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [T2Space Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    HausdorffLocallyCompactObject (TopCat.of { p : X × Y // f p.1 = g p.2 }) := by
  let hs : IsClosed { p : X × Y | f p.1 = g p.2 } :=
    isClosed_fiberProduct_subset f.hom.continuous_toFun g.hom.continuous_toFun
  letI : T2Space { p : X × Y | f p.1 = g p.2 } := inferInstance
  letI : LocallyCompactSpace { p : X × Y | f p.1 = g p.2 } := hs.locallyCompactSpace
  change T2Space { p : X × Y | f p.1 = g p.2 } ∧
      LocallyCompactSpace { p : X × Y | f p.1 = g p.2 }
  exact ⟨inferInstance, inferInstance⟩

private theorem hausdorffLocallyCompact_pullback
    {X Y Z : TopCat.{u}} [T2Space X] [LocallyCompactSpace X]
    [T2Space Y] [LocallyCompactSpace Y] [T2Space Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    HausdorffLocallyCompactObject (pullback f g) :=
  HausdorffLocallyCompactObject.prop_of_iso
    (TopCat.pullbackIsoProdSubtype f g).symm
    (hausdorffLocallyCompact_pullbackSubtype f g)

/-- The defining object property of `LC` is closed under pullback-shaped limits in `TopCat`. -/
instance hausdorffLocallyCompactObject_isClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape HausdorffLocallyCompactObject WalkingCospan := by
  refine ObjectProperty.IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  let X := F.obj WalkingCospan.left
  let Y := F.obj WalkingCospan.right
  let Z := F.obj WalkingCospan.one
  let f : X ⟶ Z := F.map WalkingCospan.Hom.inl
  let g : Y ⟶ Z := F.map WalkingCospan.Hom.inr
  letI : T2Space X := (hF WalkingCospan.left).1
  letI : LocallyCompactSpace X := (hF WalkingCospan.left).2
  letI : T2Space Y := (hF WalkingCospan.right).1
  letI : LocallyCompactSpace Y := (hF WalkingCospan.right).2
  letI : T2Space Z := (hF WalkingCospan.one).1
  exact HausdorffLocallyCompactObject.prop_of_iso
    (HasLimit.isoOfNatIso (diagramIsoCospan F)).symm
    (hausdorffLocallyCompact_pullback f g)

end Limits

end CategoryTheory

namespace LCCat

/-- Lemma 21.31.1: the category `LC` has fiber products. -/
@[stacks 09WZ]
instance instHasPullbacks : HasPullbacks LCCat.{u} := by
  infer_instance

/-- Lemma 21.31.1: the category `LC` has a final object. -/
@[stacks 09WZ]
instance instHasTerminal : HasTerminal LCCat.{u} := by
  let T : LCCat.{u} := ⟨TopCat.of PUnit.{u + 1}, ⟨inferInstance, inferInstance⟩⟩
  letI : ∀ X : LCCat.{u}, Unique (X ⟶ T) := fun X ↦
    ⟨⟨ObjectProperty.homMk (TopCat.isTerminalPUnit.from X.obj)⟩, fun f ↦ by
      apply ObjectProperty.hom_ext
      exact TopCat.isTerminalPUnit.hom_ext _ _⟩
  exact hasTerminal_of_unique T

/-- Lemma 21.31.1: since `LC` has a final object and fiber products, it has finite limits. -/
@[stacks 09WZ]
instance instHasFiniteLimits : HasFiniteLimits LCCat.{u} :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

section

variable {X Y Z : LCCat.{u}} [CompactSpace X.obj] [CompactSpace Y.obj] (f : X ⟶ Z) (g : Y ⟶ Z)

/-- Lemma 21.31.1: for morphisms `X ⟶ Z` and `Y ⟶ Z` in `LC`, if `X` and `Y` are quasi-compact,
then the fiber product `X ×[Z] Y` is quasi-compact. -/
@[stacks 09WZ]
instance compactSpace_pullback : CompactSpace (pullback f g).obj := by
  let f' : C(X.obj, Z.obj) := f.hom.hom
  let g' : C(Y.obj, Z.obj) := g.hom.hom
  let hs : IsClosed
      { p : X.obj × Y.obj |
        (ConcreteCategory.hom f.hom) p.1 = (ConcreteCategory.hom g.hom) p.2 } :=
    by simpa [f', g'] using isClosed_fiberProduct_subset f'.continuous g'.continuous
  letI : CompactSpace
      { p : X.obj × Y.obj |
        (ConcreteCategory.hom f.hom) p.1 = (ConcreteCategory.hom g.hom) p.2 } := by
    rw [← isCompact_iff_compactSpace]
    exact hs.isCompact
  let e₁ :
      { p : X.obj × Y.obj |
        (ConcreteCategory.hom f.hom) p.1 = (ConcreteCategory.hom g.hom) p.2 } ≃ₜ
        ↑(pullback f.hom g.hom) :=
    TopCat.homeoOfIso (TopCat.pullbackIsoProdSubtype f.hom g.hom).symm
  let e₂ :
      ↑(pullback f.hom g.hom) ≃ₜ ↑(limit ((cospan f g) ⋙ HausdorffLocallyCompactObject.ι) : TopCat) :=
    TopCat.homeoOfIso
      (HasLimit.isoOfNatIso (cospanCompIso HausdorffLocallyCompactObject.ι f g)).symm
  let e₃ :
      ↑(limit ((cospan f g) ⋙ HausdorffLocallyCompactObject.ι) : TopCat) ≃ₜ
        (pullback f g).obj :=
    TopCat.homeoOfIso (preservesLimitIso HausdorffLocallyCompactObject.ι (cospan f g)).symm
  let e := (e₁.trans e₂).trans e₃
  have hcompact : IsCompact ((e : _ → (pullback f g).obj) '' Set.univ) :=
    isCompact_univ.image e.continuous
  have himage : (e : _ → (pullback f g).obj) '' Set.univ = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      refine ⟨e.symm x, ?_, by simpa using e.apply_symm_apply x⟩
      exact Set.mem_univ _
  rw [himage] at hcompact
  exact isCompact_univ_iff.mp hcompact

end

end LCCat
