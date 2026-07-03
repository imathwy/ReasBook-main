import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_39_1 (from Chap04) -/
universe u v

namespace CategoryTheory

open Groupoid

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Definition 4.39.1:
- primary domain: thin groupoids as the canonical model of setoid `1`-categories;
- sampled owner-level declarations:
  `CategoryTheory.IsGroupoid`,
  `Quiver.IsThin`,
  `CategoryTheory.Groupoid.isThin_iff`,
  `CategoryTheory.Groupoid.isoEquivHom`;
- best owner abstraction: the source notion is exactly the conjunction of the canonical owners
  `[IsGroupoid C] [Quiver.IsThin C]`, so this file should recall those owners and keep only the
  source-facing bridge to trivial automorphisms;
- primitive owner data: invertibility of all morphisms and subsingleton endomorphism types;
- derived API: the automorphism reformulation, obtained by transporting the canonical owner theorem
  `Groupoid.isThin_iff` across `Groupoid.isoEquivHom`.

Source/core/bridge triage:
- `source-facing`: the source wording that a setoid `1`-category has only trivial automorphisms;
- `core/canonical`: `IsGroupoid` and `Quiver.IsThin`;
- `bridge/view`: `isThin_iff_subsingleton_aut`. -/

/- Definition 4.39.1: a setoid `1`-category is expressed in the owner API by the pair of
assumptions `[IsGroupoid C] [Quiver.IsThin C]`. -/
recall IsGroupoid

/- The second owner condition in Definition 4.39.1 is thinness. -/
recall Quiver.IsThin

/-- In a groupoid, thinness is equivalent to requiring each object to have a subsingleton
automorphism type. This is the source-facing reformulation of Definition 4.39.1. -/
theorem isThin_iff_subsingleton_aut [IsGroupoid C] :
    Quiver.IsThin C ↔ ∀ X : C, Subsingleton (Aut X) := by
  letI : Groupoid C := ofIsGroupoid
  refine (isThin_iff C).trans ?_
  constructor
  · intro h X
    exact (isoEquivHom X X).subsingleton_congr.2 (h X)
  · intro h X
    exact (isoEquivHom X X).subsingleton_congr.1 (h X)

end CategoryTheory

/-! ### Definition_4_39_2 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/-
Domain-style sampling for Definition 4.39.2:
- primary domain: categories fibred over a base with fiberwise setoid `1`-category structure;
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `Functor.Fiber`,
  `Quiver.IsThin`,
  `isThin_iff_subsingleton_aut`;
- best owner abstraction: there is no earlier owner in the chapter for “fibred in setoids”, so the
  correct public owner here is the minimal class obtained by adjoining fiberwise thinness to the
  existing owner `IsFibredInGroupoids`;
- primitive data: `IsFibredInGroupoids p` together with `Quiver.IsThin (p.Fiber U)` for each
  `U : C`;
- derived API: the owner-level specification theorem
  `isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_thin`, the source-facing automorphism
  criterion `isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_subsingleton_aut`, instance
  search on each fiber, and the bundled owner
  `FibredInSetoidsOver C` defined downstream.

Source/core/bridge triage:
- `source-facing`: `IsFibredInSetoids p`;
- `core/canonical`: `IsFibredInGroupoids p` and `Quiver.IsThin (p.Fiber U)`;
- `bridge/view`: the automorphism reformulation obtained fiberwise from
  `isThin_iff_subsingleton_aut`. -/

/-- Definition 4.39.2: a category fibred in setoids over `C` is a functor `p : S ⥤ C` that is
fibred in groupoids and whose standard fiber `p.Fiber U` is a setoid `1`-category for every
object `U` of `C`. -/
@[mk_iff isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_thin]
class IsFibredInSetoids (p : S ⥤ C) : Prop extends IsFibredInGroupoids p where
  /-- Each standard fiber of a category fibred in setoids is thin. -/
  fiber_isThin (U : C) : Quiver.IsThin (p.Fiber U)

attribute [instance] IsFibredInSetoids.fiber_isThin

/-- The core owner data for a category fibred in setoids reconstructs the source-facing class. -/
instance (p : S ⥤ C) [IsFibredInGroupoids p] [∀ U : C, Quiver.IsThin (p.Fiber U)] :
    IsFibredInSetoids p :=
  { toIsFibredInGroupoids := inferInstance
    fiber_isThin := inferInstance }

/-- A category fibred in setoids is equivalently a category fibred in groupoids whose every
fiber object has a subsingleton automorphism type. This is the fiberwise source-facing companion
to the owner theorem `isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_thin`, using
Definition `4.39.1` inside the fibers. -/
theorem isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_subsingleton_aut (p : S ⥤ C) :
    IsFibredInSetoids p ↔
      IsFibredInGroupoids p ∧ ∀ (U : C) (x : p.Fiber U), Subsingleton (Aut x) := by
  rw [isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_thin]
  constructor
  · rintro ⟨hp, hthin⟩
    refine ⟨hp, ?_⟩
    intro U x
    let _ : IsGroupoid (p.Fiber U) := inferInstance
    exact (isThin_iff_subsingleton_aut).1 (hthin U) x
  · rintro ⟨hp, hsub⟩
    refine ⟨hp, ?_⟩
    intro U
    let _ : IsGroupoid (p.Fiber U) := inferInstance
    exact (isThin_iff_subsingleton_aut).2 (hsub U)

end CategoryTheory

/-! ### Definition_4_39_3 (from Chap04) -/
universe u v vS w

namespace CategoryTheory

open Bicategory
open ObjectProperty
open BasedFunctor
open scoped Bicategory

/-
Domain-style sampling for Definition 4.39.3:
- primary domain: categories fibred in setoids over a fixed base, viewed as a full sub-`2`-
  category of categories fibred in groupoids.
- inspected owner-level declarations:
  `SubTwoCategory`,
  `IsFibredInSetoids`,
  `FibredInGroupoidsOver`,
  `SubTwoCategory.Hom.toHom`.
- best owner abstraction: the source-facing owner is the full sub-`2`-category of
  `FibredInGroupoidsOver C` cut out by the fibred-in-setoids condition.
- primitive data: a category fibred in groupoids over `C` together with the proof that its
  projection is fibred in setoids.
- derived API: the coercions to the ambient fibred-in-groupoids, fibred-category, category-over,
  and based-category owners; the ambient fibred-in-groupoids morphism view is recovered directly
  from the owner homs `X ⟶ Y`.

Source/core/bridge triage:
- `source-facing`: `FibredInSetoidsOver C`;
- `core/canonical`: `SubTwoCategory`, `FibredInGroupoidsOver`, `IsFibredInSetoids`, and the
  owner homs `X ⟶ Y`;
- `bridge/view`: the forgetful coercions to ambient owners.

Primitive-vs-derived split:
- primitive data: the underlying category fibred in groupoids over `C` together with the proof
  that its projection is fibred in setoids;
- derived API: the inherited strict bicategory structure and the short projections to the ambient
  owner data; morphisms are inherited directly from the ambient fibred-in-groupoids owner. -/

/-- Definition 4.39.3 at the owner level: categories fibred in setoids over `C` form the full
sub-`2`-category of `FibredInGroupoidsOver C` cut out by the fibred-in-setoids condition. -/
abbrev fibredInSetoidsOverSubTwoCategory (C : Type u) [Category.{v} C] :
    SubTwoCategory (FibredInGroupoidsOver C) where
  obj := fun X ↦ IsFibredInSetoids X.p
  hom _ _ := {
    obj := ⊤
    hom := ⊤
    hom_isMultiplicative := inferInstance
  }
  id_mem _ := by trivial
  comp_mem _ _ := by trivial
  whiskerLeft_mem _ _ _ _ := by trivial
  whiskerRight_mem _ _ _ _ := by trivial

variable {C : Type u} [Category.{v} C]

/-- Definition 4.39.3: the objects of the `2`-category of categories fibred in setoids over `C`
are the categories fibred in groupoids over `C` whose projection functor is fibred in setoids;
equivalently, this is the full sub-`2`-category of categories fibred in groupoids over `C` cut
out by the fibred-in-setoids condition. -/
abbrev FibredInSetoidsOver (C : Type u) [Category.{v} C] :=
  (fibredInSetoidsOverSubTwoCategory C).Obj

instance : Bicategory (FibredInSetoidsOver C) :=
  SubTwoCategory.bicategoryObj (fibredInSetoidsOverSubTwoCategory C)

instance : Bicategory.Strict (FibredInSetoidsOver C) :=
  SubTwoCategory.strictObj (fibredInSetoidsOverSubTwoCategory C)

instance fibredInSetoidsOverCategory : Category (FibredInSetoidsOver C) :=
  StrictBicategory.category (FibredInSetoidsOver C)

instance fibredInSetoidsOverHom₂IsMultiplicative (X Y : FibredInSetoidsOver C) :
    ((fibredInSetoidsOverSubTwoCategory C).hom₂ X Y).IsMultiplicative :=
  ((fibredInSetoidsOverSubTwoCategory C).hom X Y).hom_isMultiplicative

instance fibredInSetoidsOverHomInclusionFull (X Y : FibredInSetoidsOver C) :
    (((fibredInSetoidsOverSubTwoCategory C).hom X Y).inclusion).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨ObjectProperty.homMk η, trivial⟩, rfl⟩

namespace FibredInSetoidsOver

/-- Build a bundled category fibred in setoids over `C` from a functor to `C`. -/
abbrev ofFunctor {S : Type w} [Category.{vS} S] (p : S ⥤ C) [IsFibredInSetoids p] :
    FibredInSetoidsOver C :=
  ⟨FibredInGroupoidsOver.ofFunctor p, by
    simpa [FibredInGroupoidsOver.p, FibredInGroupoidsOver.ofFunctor] using
      (inferInstance : IsFibredInSetoids p)⟩

/-- The underlying category fibred in groupoids over `C`. -/
abbrev toFibredInGroupoidsOver (X : FibredInSetoidsOver C) : FibredInGroupoidsOver C :=
  X.obj

/-- The underlying fibred category over `C`. -/
abbrev toFibredCategoryOver (X : FibredInSetoidsOver C) : FibredCategoryOver C :=
  (X.toFibredInGroupoidsOver : FibredCategoryOver C)

/-- The underlying category over `C`. -/
abbrev toCategoryOver (X : FibredInSetoidsOver C) : CategoryOver C :=
  X.toFibredInGroupoidsOver.toCategoryOver

/-- The total category of a bundled category fibred in setoids over `C`. -/
abbrev S (X : FibredInSetoidsOver C) :=
  X.toFibredInGroupoidsOver.S

/-- The projection functor of a bundled category fibred in setoids over `C`. -/
abbrev p (X : FibredInSetoidsOver C) :=
  X.toFibredInGroupoidsOver.p

/-- The defining property of an object of `FibredInSetoidsOver C`: its projection functor is
fibred in setoids. -/
-- Proof sketch: This is the property field of the corresponding object of the full
-- sub-`2`-category.
theorem isFibredInSetoids_p (X : FibredInSetoidsOver C) : IsFibredInSetoids X.p :=
  -- The bundled owner stores exactly the fibred-in-setoids condition on the projection.
  X.property

/-- Forget a bundled category fibred in setoids over `C` to its underlying based category. -/
abbrev toBasedCategory (X : FibredInSetoidsOver C) : BasedCategory C :=
  X.toFibredInGroupoidsOver.toBasedCategory

/-- Compatibility coercion to categories fibred in groupoids over `C`. -/
instance : CoeOut (FibredInSetoidsOver C) (FibredInGroupoidsOver C) where
  coe X := X.toFibredInGroupoidsOver

/-- Compatibility coercion to fibred categories over `C`. -/
instance : CoeOut (FibredInSetoidsOver C) (FibredCategoryOver C) where
  coe X := X.toFibredCategoryOver

/-- Compatibility coercion to the ambient category `Cat/C`. -/
instance : CoeOut (FibredInSetoidsOver C) (CategoryOver C) where
  coe X := X.toCategoryOver

/-- Compatibility coercion to the ambient based-category API. -/
instance : CoeOut (FibredInSetoidsOver C) (BasedCategory C) where
  coe X := X.toBasedCategory

/-- The projection functor of a bundled category fibred in setoids over `C` is fibred in
setoids. -/
instance (X : FibredInSetoidsOver C) : IsFibredInSetoids (FibredInSetoidsOver.p X) :=
  X.property

variable {X Y : FibredInSetoidsOver C}

/-- Regard an ambient morphism of the underlying categories fibred in groupoids over `C` as the
corresponding owner hom in the full sub-`2`-category `FibredInSetoidsOver C`. -/
abbrev ofAmbientHom
    (F : X.toFibredInGroupoidsOver ⟶ Y.toFibredInGroupoidsOver) : X ⟶ Y :=
  { obj := { obj := F, property := trivial } }

/-- Build a morphism of categories fibred in setoids over `C` from a based functor over `C`.
This is the thin owner-level bridge from the ambient `BasedFunctor` API. -/
abbrev ofBasedFunctor
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) : X ⟶ Y :=
  ofAmbientHom (FibredInGroupoidsMor.ofBasedFunctor F)

/-- The underlying based functor of a morphism of categories fibred in setoids over `C`. -/
abbrev toBasedFunctor (F : X ⟶ Y) : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  FibredInGroupoidsMor.toBasedFunctor F.toHom

/- Convert an isomorphism between the ambient morphisms of categories fibred in groupoids into
an isomorphism in the owner hom-category of categories fibred in setoids. -/
noncomputable def ofAmbientIso
    {F G : X ⟶ Y}
    (e : F.toHom ≅ G.toHom) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

/-- Compatibility coercion from owner morphisms to based functors over `C`. -/
instance : CoeOut (X ⟶ Y) (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := toBasedFunctor F

/-- A morphism of categories fibred in setoids over `C` is an equivalence over the base if its
underlying based functor is. -/
abbrev IsEquivalenceOverBase (F : X ⟶ Y) : Prop :=
  BasedFunctor.IsEquivalenceOverBase (toBasedFunctor F)

end FibredInSetoidsOver

variable {C : Type u} [Category.{v} C]

/-- A category fibred in sets over `C` canonically defines a category fibred in setoids over
`C`. -/
instance : CoeTC (FibredInSetsOver C) (FibredInSetoidsOver C) where
  coe X := by
    letI : IsFibredInSetoids X.p := inferInstance
    exact FibredInSetoidsOver.ofFunctor X.p

variable {X Y : FibredInSetoidsOver C}

/-- A morphism of categories fibred in setoids over `C` is canonically viewed as the
corresponding ambient morphism of categories fibred in groupoids over `C`. -/
instance : CoeOut (X ⟶ Y)
    (X.toFibredInGroupoidsOver ⟶ Y.toFibredInGroupoidsOver) where
  coe F := F.toHom

variable (F G : X ⟶ Y)

/- Definition 4.39.3: a `2`-morphism between `1`-morphisms of categories fibred in setoids over
`C` is the inherited morphism in the owner hom-category of the full sub-`2`-category
`fibredInSetoidsOverSubTwoCategory C`. -/
#check (F ⟶ G)

end CategoryTheory

/-! ### Lemma_4_39_4 (from Chap04) -/
universe u v

namespace CategoryTheory

open CategoryTheory.Limits
open CategoryOver
open scoped Bicategory
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {X Y S : FibredInSetoidsOver.{u, v, max u v, v} C}

set_option maxHeartbeats 10000000

/- Domain-style sampling for Lemma 4.39.4:
- primary domain: categories fibred in setoids over a fixed base and their bicategorical
  `2`-fibre products;
- inspected owner-level declarations:
  `IsFibredInSetoids`,
  `FibredInSetoidsOver`,
  `CategoryOver.explicitTwoFibreProductSquare`,
  `CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct`;
- best owner abstraction: the source-facing owner data already lives in the explicit pullback over
  `Cat/C`, so this file should keep only the setoid-valued rebundling and its inherited
  bicategorical universal property.

Primitive-vs-derived split:
- primitive source-facing data: the morphisms `F : X ⟶ S` and `G : Y ⟶ S`;
- derived API: the closure theorem asserting that the explicit pullback projection is again fibred
  in setoids, the rebundled owner `FibredInSetoidsOver.twoFibreProduct`, the canonical square, and
  the inherited finality statement.

Source/core/bridge triage:
- `source-facing`: `FibredInSetoidsOver.twoFibreProductSquare` and
  `FibredInSetoidsOver.twoFibreProduct_isTwoFibreProduct`;
- `core/canonical`: `CategoryOver.explicitTwoFibreProductSquare` and
  `CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct`;
- `bridge/view`: the owner-level rebundling through `FibredInSetoidsOver.ofFunctor`,
  `FibredInSetoidsOver.ofAmbientHom`, and `FibredInSetoidsOver.ofAmbientIso`. -/

/-- Helper for Lemma 4.39.4: the explicit pullback of the underlying based functors of `F` and
`G` over `C`. -/
private noncomputable abbrev explicitTwoFibreProductOver
    (F : X ⟶ S) (G : Y ⟶ S) :
    BasedCategory C :=
  CategoryOver.explicitTwoFibreProduct
    (FibredInSetoidsOver.toBasedFunctor F)
    (FibredInSetoidsOver.toBasedFunctor G)

section FibredCategoryPullback

open FibredCategoryMor

variable {Xf Yf Sf : FibredCategoryOver C}

/-- Helper for Lemma 4.39.4: a morphism of fibred categories sends a strongly cartesian lift over
the chosen base arrow to a strongly cartesian lift over the same base arrow. -/
private theorem map_stronglyCartesian_over_base
    {A B : FibredCategoryOver C} (H : A ⟶ B)
    {U V : C} {a b : A.S} {f : U ⟶ V} {φ : a ⟶ b}
    (hφ : A.p.IsStronglyCartesian f φ) :
    B.p.IsStronglyCartesian f ((toFunctor H).map φ) := by
  -- Rewrite the source lift to the projected base so the owner preservation theorem applies.
  have hφ' : A.p.IsStronglyCartesian (A.p.map φ) φ := by
    letI : A.p.IsStronglyCartesian f φ := hφ
    subst_hom_lift A.p f φ
    simpa using hφ
  have hmap :
      B.p.IsStronglyCartesian (B.p.map ((toFunctor H).map φ)) ((toFunctor H).map φ) :=
    FibredCategoryMor.map_stronglyCartesian H φ hφ'
  -- Then transport the target lift back to the original chosen base arrow `f`.
  have hLift : B.p.IsHomLift f ((toFunctor H).map φ) := by
    letI : A.p.IsHomLift f φ := hφ.toIsHomLift
    exact show B.p.IsHomLift f ((toFunctor H).map φ) from inferInstance
  letI : B.p.IsHomLift f ((toFunctor H).map φ) := hLift
  subst_hom_lift B.p f ((toFunctor H).map φ)
  simpa using hmap

/-- Helper for Lemma 4.39.4: if a morphism is strongly cartesian for one chosen lift of its base
arrow, then it is strongly cartesian for any other chosen lift of the same morphism. -/
private theorem isStronglyCartesian_rebase_of_same_lift
    {𝒮 : Type u} {𝒳 : Type v} [Category 𝒮] [Category 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {a b : 𝒳} {f f' : p.obj a ⟶ p.obj b} (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] [p.IsHomLift f' φ] :
    p.IsStronglyCartesian f' φ := by
  -- Both lift witnesses identify their base arrows with `p.map φ`.
  have hf : f = p.map φ := IsHomLift.eq_of_isHomLift p f φ
  have hf' : f' = p.map φ := IsHomLift.eq_of_isHomLift p f' φ
  subst hf
  subst hf'
  infer_instance

/-- Helper for Lemma 4.39.4: an external lift witness upgrades strong cartesianness back to the
owner-level base map of the same morphism. -/
private theorem isStronglyCartesian_of_external_hom_lift
    {𝒮 : Type u} {𝒳 : Type v} [Category 𝒮] [Category 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] [p.IsHomLift f φ] :
    p.IsStronglyCartesian (p.map φ) φ := by
  -- Normalize the chosen external source and target to the actual owner source and target.
  have ha : p.obj a = R := IsHomLift.domain_eq p f φ
  have hb : p.obj b = S := IsHomLift.codomain_eq p f φ
  subst ha
  subst hb
  exact isStronglyCartesian_rebase_of_same_lift (p := p) (f := f) (f' := p.map φ) φ

/-- Helper for Lemma 4.39.4: the base projection of a morphism in the explicit pullback is its
stored `base` field. -/
private theorem explicitTwoFibreProduct_base_projection_map
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj}
    (φ : P ⟶ Q) :
    (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.map φ = φ.base := by
  rfl

/-- Helper for Lemma 4.39.4: a lift for the projection of the explicit pullback has base arrow
equal to the stored `base` field of the morphism. -/
private theorem explicitTwoFibreProduct_isHomLift_base_eq
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift f φ) :
    φ.base = f := by
  let p := (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p
  have h : f = p.map φ := @IsHomLift.eq_of_isHomLift _ _ _ _ p _ _ f φ hφ
  simpa [p, explicitTwoFibreProduct_base_projection_map F G φ] using h.symm

/-- Helper for Lemma 4.39.4: a lift in the explicit pullback induces the corresponding lift on
the left component over the same base arrow. -/
private theorem explicitTwoFibreProduct_left_isHomLift_of_isHomLift
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift f φ) :
    Xf.p.IsHomLift f φ.a := by
  -- After identifying the outer base with `φ.base`, the stored component lift is exactly over `f`.
  change Xf.toBasedCategory.p.IsHomLift f φ.a
  have hbase : φ.base = f := explicitTwoFibreProduct_isHomLift_base_eq F G φ hφ
  rw [← hbase]
  simpa using (φ.a_over : Xf.p.IsHomLift φ.base φ.a)

/-- Helper for Lemma 4.39.4: a lift in the explicit pullback induces the corresponding lift on
the right component over the same base arrow. -/
private theorem explicitTwoFibreProduct_right_isHomLift_of_isHomLift
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift f φ) :
    Yf.p.IsHomLift f φ.b := by
  -- The same normalization works for the right component.
  change Yf.toBasedCategory.p.IsHomLift f φ.b
  have hbase : φ.base = f := explicitTwoFibreProduct_isHomLift_base_eq F G φ hφ
  rw [← hbase]
  simpa using (φ.b_over : Yf.p.IsHomLift φ.base φ.b)

/-- Helper for Lemma 4.39.4: a morphism in the explicit pullback is strongly cartesian whenever
its left and right components are strongly cartesian over the same base arrow. -/
private theorem explicitTwoFibreProduct_hom_isStronglyCartesian_of_components
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj}
    (φ : P ⟶ Q)
    (ha : Xf.p.IsStronglyCartesian φ.base φ.a)
    (hb : Yf.p.IsStronglyCartesian φ.base φ.b) :
    (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsStronglyCartesian
      φ.base φ := by
  letI : Xf.p.IsStronglyCartesian φ.base φ.a := ha
  letI : Yf.p.IsStronglyCartesian φ.base φ.b := hb
  refine
    { toIsHomLift := by
        change (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift
          ((explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.map φ) φ
        infer_instance
      universal_property' := ?_ }
  intro R g ψ hψ
  letI :
      (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift
        (g ≫ φ.base) ψ := hψ
  have hψa : Xf.p.IsHomLift (g ≫ φ.base) ψ.a := by
    exact explicitTwoFibreProduct_left_isHomLift_of_isHomLift F G (f := g ≫ φ.base) ψ hψ
  have hψb : Yf.p.IsHomLift (g ≫ φ.base) ψ.b := by
    exact explicitTwoFibreProduct_right_isHomLift_of_isHomLift F G (f := g ≫ φ.base) ψ hψ
  -- Factor the left and right components through the chosen strongly cartesian lifts.
  letI : Xf.p.IsHomLift (g ≫ φ.base) ψ.a := hψa
  obtain ⟨χa, hχa, hχa_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property Xf.p φ.base φ.a g (g ≫ φ.base) rfl ψ.a
  have hχa_over : Xf.p.IsHomLift g χa := hχa.1
  have hχa_fac : χa ≫ φ.a = ψ.a := hχa.2
  letI : Yf.p.IsHomLift (g ≫ φ.base) ψ.b := hψb
  obtain ⟨χb, hχb, hχb_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property Yf.p φ.base φ.b g (g ≫ φ.base) rfl ψ.b
  have hχb_over : Yf.p.IsHomLift g χb := hχb.1
  have hχb_fac : χb ≫ φ.b = ψ.b := hχb.2
  have hmap_hb :
      Sf.p.IsStronglyCartesian φ.base ((toFunctor G).map φ.b) :=
    map_stronglyCartesian_over_base G hb
  letI : Sf.p.IsStronglyCartesian φ.base ((toFunctor G).map φ.b) := hmap_hb
  have hleft_over : Sf.p.IsHomLift g ((toFunctor F).map χa ≫ P.comparison) := by
    -- Map the left factorization into `Sf`, then append the vertical comparison of `P`.
    have hFχa : Sf.p.IsHomLift g ((toFunctor F).map χa) := by
      infer_instance
    letI : Sf.p.IsHomLift g ((toFunctor F).map χa) := hFχa
    letI : Sf.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
    exact IsHomLift.comp_lift_id_right' (p := Sf.p) g ((toFunctor F).map χa) P.U P.comparison
  have hright_over : Sf.p.IsHomLift g (R.comparison ≫ (toFunctor G).map χb) := by
    -- Do the same for the right factorization, now precomposing with the vertical comparison of
    -- the source object `R`.
    have hGχb : Sf.p.IsHomLift g ((toFunctor G).map χb) := by
      infer_instance
    letI : Sf.p.IsHomLift g ((toFunctor G).map χb) := hGχb
    letI : Sf.p.IsHomLift (𝟙 R.U) R.comparison := R.comparison_over
    exact
      IsHomLift.comp_lift_id_left' (p := Sf.p) R.U R.comparison g ((toFunctor G).map χb)
  have hcomm_after_comp :
      ((toFunctor F).map χa ≫ P.comparison) ≫ (toFunctor G).map φ.b =
        (R.comparison ≫ (toFunctor G).map χb) ≫ (toFunctor G).map φ.b := by
    -- Both candidate comparison squares become the same after composing with `G.map φ.b`.
    calc
      ((toFunctor F).map χa ≫ P.comparison) ≫ (toFunctor G).map φ.b
          = (toFunctor F).map χa ≫ ((toFunctor F).map φ.a ≫ Q.comparison) := by
              rw [φ.comm.w]
              simp [Category.assoc]
      _ = (toFunctor F).map (χa ≫ φ.a) ≫ Q.comparison := by
            simp [Functor.map_comp, Category.assoc]
      _ = (toFunctor F).map ψ.a ≫ Q.comparison := by
            rw [hχa_fac]
      _ = R.comparison ≫ (toFunctor G).map ψ.b := by
            exact ψ.comm.w
      _ = R.comparison ≫ (toFunctor G).map (χb ≫ φ.b) := by
            rw [hχb_fac]
      _ = (R.comparison ≫ (toFunctor G).map χb) ≫ (toFunctor G).map φ.b := by
            simp [Functor.map_comp, Category.assoc]
  have hcomm :
      (toFunctor F).map χa ≫ P.comparison =
        R.comparison ≫ (toFunctor G).map χb := by
    -- Cancel the mapped strongly cartesian arrow `(toFunctor G).map φ.b`.
    apply Functor.IsStronglyCartesian.ext (p := Sf.p) (f := φ.base) ((toFunctor G).map φ.b) g
    simpa [Category.assoc] using hcomm_after_comp
  let χ : R ⟶ P :=
    { base := g
      a := χa
      a_over := hχa_over
      b := χb
      b_over := hχb_over
      comm := ⟨hcomm⟩ }
  refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
  · -- The assembled morphism factors through `φ` by the chosen component factorizations.
    change (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift
      ((explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.map χ) χ
    infer_instance
  · -- The assembled morphism factors through `φ` by the chosen component factorizations.
    apply ExplicitTwoFibreProductHom.ext
    · simpa [χ] using hχa_fac
    · simpa [χ] using hχb_fac
  · intro χ' hχ'
    rcases hχ' with ⟨hχ'_over, hχ'_fac⟩
    letI :
        (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift
          g χ' := hχ'_over
    have hχ'a : Xf.p.IsHomLift g χ'.a := by
      exact explicitTwoFibreProduct_left_isHomLift_of_isHomLift F G (f := g) χ' hχ'_over
    have hχ'b : Yf.p.IsHomLift g χ'.b := by
      exact explicitTwoFibreProduct_right_isHomLift_of_isHomLift F G (f := g) χ' hχ'_over
    -- Uniqueness is checked componentwise using the universal properties of `φ.a` and `φ.b`.
    apply ExplicitTwoFibreProductHom.ext
    · exact hχa_uniq χ'.a ⟨hχ'a, by simpa using congrArg ExplicitTwoFibreProductHom.a hχ'_fac⟩
    · exact hχb_uniq χ'.b ⟨hχ'b, by simpa using congrArg ExplicitTwoFibreProductHom.b hχ'_fac⟩

/-- Helper for Lemma 4.39.4: the comparison carried by an explicit pullback object is an
isomorphism in the total category of `Sf`. -/
private theorem explicitTwoFibreProduct_comparison_isIso
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj) :
    IsIso P.comparison := by
  -- Forget the fiberwise comparison isomorphism to the total category `Sf`.
  let e : (toFunctor F).obj P.obj.fst.1 ≅ (toFunctor G).obj P.obj.snd.1 :=
    { hom := P.comparison
      inv := P.obj.iso.inv.1
      hom_inv_id := by
        exact congrArg Subtype.val P.obj.iso.hom_inv_id
      inv_hom_id := by
        exact congrArg Subtype.val P.obj.iso.inv_hom_id }
  exact ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- Helper for Lemma 4.39.4: the chosen pullback of the left component of `P` along `f`, viewed
as an object of the standard fiber of `Xf` over the new base. -/
private noncomputable def explicitTwoFibreProduct_left_pullback
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    Xf.p.Fiber V :=
  let _ : HasFibers Xf.p := HasFibers.canonical Xf.p
  let a := HasFibers.pullbackMap (p := Xf.p) f P.obj.fst.2
  Functor.Fiber.mk (IsHomLift.domain_eq Xf.p f a)

/-- Helper for Lemma 4.39.4: the chosen pullback map of the left component of `P` along `f`. -/
private noncomputable def explicitTwoFibreProduct_left_pullback_map
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    (explicitTwoFibreProduct_left_pullback F G P f).1 ⟶ P.obj.fst.1 :=
  let _ : HasFibers Xf.p := HasFibers.canonical Xf.p
  let a := HasFibers.pullbackMap (p := Xf.p) f P.obj.fst.2
  show (explicitTwoFibreProduct_left_pullback F G P f).1 ⟶ P.obj.fst.1 from a

/-- Helper for Lemma 4.39.4: the chosen pullback of the right component of `P` along `f`, viewed
as an object of the standard fiber of `Yf` over the new base. -/
private noncomputable def explicitTwoFibreProduct_right_pullback
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    Yf.p.Fiber V :=
  let _ : HasFibers Yf.p := HasFibers.canonical Yf.p
  let b := HasFibers.pullbackMap (p := Yf.p) f P.obj.snd.2
  Functor.Fiber.mk (IsHomLift.domain_eq Yf.p f b)

/-- Helper for Lemma 4.39.4: the chosen pullback map of the right component of `P` along `f`. -/
private noncomputable def explicitTwoFibreProduct_right_pullback_map
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    (explicitTwoFibreProduct_right_pullback F G P f).1 ⟶ P.obj.snd.1 :=
  let _ : HasFibers Yf.p := HasFibers.canonical Yf.p
  let b := HasFibers.pullbackMap (p := Yf.p) f P.obj.snd.2
  show (explicitTwoFibreProduct_right_pullback F G P f).1 ⟶ P.obj.snd.1 from b

/-- Helper for Lemma 4.39.4: pulling back the two components of an explicit pullback object along
`f` produces the unique comparison isomorphism in the fiber of `Sf` over the new base. -/
private noncomputable def explicitTwoFibreProduct_pulledback_comparison_iso
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    ((toBasedFunctor F).fiberFunctor V).obj
        (explicitTwoFibreProduct_left_pullback F G P f) ≅
      ((toBasedFunctor G).fiberFunctor V).obj
        (explicitTwoFibreProduct_right_pullback F G P f) := by
  let _ : HasFibers Xf.p := HasFibers.canonical Xf.p
  let _ : HasFibers Yf.p := HasFibers.canonical Yf.p
  let a := explicitTwoFibreProduct_left_pullback_map F G P f
  let b := explicitTwoFibreProduct_right_pullback_map F G P f
  -- The chosen pullback maps are strongly cartesian in `Xf` and `Yf`.
  have ha_cart : Xf.p.IsCartesian f a := by
    change Xf.p.IsCartesian f (HasFibers.pullbackMap (p := Xf.p) f P.obj.fst.2)
    infer_instance
  have hb_cart : Yf.p.IsCartesian f b := by
    change Yf.p.IsCartesian f (HasFibers.pullbackMap (p := Yf.p) f P.obj.snd.2)
    infer_instance
  have ha : Xf.p.IsStronglyCartesian f a :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Xf.p f a
  have hb : Yf.p.IsStronglyCartesian f b :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Yf.p f b
  -- Map those strongly cartesian lifts into `Sf`.
  have hFa : Sf.p.IsStronglyCartesian f ((toFunctor F).map a) :=
    map_stronglyCartesian_over_base F ha
  have hGb : Sf.p.IsStronglyCartesian f ((toFunctor G).map b) :=
    map_stronglyCartesian_over_base G hb
  letI : IsIso P.comparison := explicitTwoFibreProduct_comparison_isIso F G P
  letI : Sf.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
  have hcomparison : Sf.p.IsStronglyCartesian (𝟙 P.U) P.comparison :=
    Functor.IsStronglyCartesian.of_isIso Sf.p (𝟙 P.U) P.comparison
  -- Compose `F.map a` with the vertical comparison of `P` to obtain a second lift over `f`.
  have hleft :
      Sf.p.IsStronglyCartesian f ((toFunctor F).map a ≫ P.comparison) := by
    letI : Sf.p.IsStronglyCartesian f ((toFunctor F).map a) := hFa
    letI : Sf.p.IsStronglyCartesian (𝟙 P.U) P.comparison := hcomparison
    simpa using
      (show Sf.p.IsStronglyCartesian (f ≫ 𝟙 P.U)
          ((toFunctor F).map a ≫ P.comparison) from inferInstance)
  letI : Sf.p.IsStronglyCartesian f ((toFunctor G).map b) := hGb
  letI : Sf.p.IsStronglyCartesian f ((toFunctor F).map a ≫ P.comparison) := hleft
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  let e :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso
      Sf.p
      (g := Iso.refl V)
      hf
      ((toFunctor G).map b)
      ((toFunctor F).map a ≫ P.comparison)
  have hhom : Sf.p.IsHomLift (𝟙 V) e.hom := by
    simpa [e] using
      (show Sf.p.IsHomLift (Iso.refl V).hom e.hom from inferInstance)
  have hinv : Sf.p.IsHomLift (𝟙 V) e.inv := by
    simpa [e] using
      (show Sf.p.IsHomLift (Iso.refl V).inv e.inv from inferInstance)
  -- Package the domain comparison back into the standard fiber over `V`.
  refine
    { hom := Functor.Fiber.homMk Sf.p V e.hom
      inv := Functor.Fiber.homMk Sf.p V e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }

/-- Helper for Lemma 4.39.4: every base arrow into an explicit pullback object admits the
canonical pullback morphism obtained by pulling back each component in the two fibred categories. -/
private theorem explicitTwoFibreProduct_exists_isStronglyCartesian
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    ∃ Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj,
      ∃ η : Q ⟶ P,
        Xf.p.IsStronglyCartesian (Xf.p.map η.a) η.a ∧
          Yf.p.IsStronglyCartesian (Yf.p.map η.b) η.b ∧
            (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsStronglyCartesian
              f η := by
  let _ : HasFibers Xf.p := HasFibers.canonical Xf.p
  let _ : HasFibers Yf.p := HasFibers.canonical Yf.p
  let a := explicitTwoFibreProduct_left_pullback_map F G P f
  let b := explicitTwoFibreProduct_right_pullback_map F G P f
  -- Pull back the two components of `P` along `f`.
  let Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj :=
    { U := V
      obj :=
        { fst := explicitTwoFibreProduct_left_pullback F G P f
          snd := explicitTwoFibreProduct_right_pullback F G P f
          iso := explicitTwoFibreProduct_pulledback_comparison_iso F G P f } }
  have ha_over : Xf.p.IsHomLift f a := by
    change Xf.p.IsHomLift f (HasFibers.pullbackMap (p := Xf.p) f P.obj.fst.2)
    infer_instance
  have hb_over : Yf.p.IsHomLift f b := by
    change Yf.p.IsHomLift f (HasFibers.pullbackMap (p := Yf.p) f P.obj.snd.2)
    infer_instance
  have ha_cart : Xf.p.IsCartesian f a := by
    change Xf.p.IsCartesian f (HasFibers.pullbackMap (p := Xf.p) f P.obj.fst.2)
    infer_instance
  have hb_cart : Yf.p.IsCartesian f b := by
    change Yf.p.IsCartesian f (HasFibers.pullbackMap (p := Yf.p) f P.obj.snd.2)
    infer_instance
  have ha : Xf.p.IsStronglyCartesian f a :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Xf.p f a
  have hb : Yf.p.IsStronglyCartesian f b :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Yf.p f b
  have hFa : Sf.p.IsStronglyCartesian f ((toFunctor F).map a) :=
    map_stronglyCartesian_over_base F ha
  have hGb : Sf.p.IsStronglyCartesian f ((toFunctor G).map b) :=
    map_stronglyCartesian_over_base G hb
  letI : IsIso P.comparison := explicitTwoFibreProduct_comparison_isIso F G P
  letI : Sf.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
  have hcomparison : Sf.p.IsStronglyCartesian (𝟙 P.U) P.comparison :=
    Functor.IsStronglyCartesian.of_isIso Sf.p (𝟙 P.U) P.comparison
  have hleft :
      Sf.p.IsStronglyCartesian f ((toFunctor F).map a ≫ P.comparison) := by
    letI : Sf.p.IsStronglyCartesian f ((toFunctor F).map a) := hFa
    letI : Sf.p.IsStronglyCartesian (𝟙 P.U) P.comparison := hcomparison
    simpa using
      (show Sf.p.IsStronglyCartesian (f ≫ 𝟙 P.U)
          ((toFunctor F).map a ≫ P.comparison) from inferInstance)
  letI : Sf.p.IsStronglyCartesian f ((toFunctor G).map b) := hGb
  letI : Sf.p.IsStronglyCartesian f ((toFunctor F).map a ≫ P.comparison) := hleft
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  let e :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso
      Sf.p
      (g := Iso.refl V)
      hf
      ((toFunctor G).map b)
      ((toFunctor F).map a ≫ P.comparison)
  have hfac :
      e.hom ≫ (toFunctor G).map b = (toFunctor F).map a ≫ P.comparison := by
    change
      (Functor.IsStronglyCartesian.domainIsoOfBaseIso
          Sf.p
          hf
          ((toFunctor G).map b)
          ((toFunctor F).map a ≫ P.comparison)).hom ≫
        (toFunctor G).map b =
          (toFunctor F).map a ≫ P.comparison
    exact
      Functor.IsStronglyCartesian.fac
        Sf.p
        f
        ((toFunctor G).map b)
        hf
        ((toFunctor F).map a ≫ P.comparison)
  have hcomm :
      CommSq
        ((toFunctor F).map a)
        Q.comparison
        P.comparison
        ((toFunctor G).map b) := by
    -- The defining square is exactly the comparison furnished by `e`.
    refine ⟨?_⟩
    simpa [Q, explicitTwoFibreProduct_pulledback_comparison_iso] using hfac.symm
  let η : Q ⟶ P :=
    { base := f
      a := a
      a_over := ha_over
      b := b
      b_over := hb_over
      comm := hcomm }
  have hηa : Xf.p.IsStronglyCartesian (Xf.p.map η.a) η.a := by
    letI : Xf.p.IsStronglyCartesian f η.a := ha
    letI : Xf.p.IsHomLift f η.a := ha_over
    exact
      isStronglyCartesian_of_external_hom_lift
        (p := Xf.p) (R := V) (S := P.U) (f := f) η.a
  have hηb : Yf.p.IsStronglyCartesian (Yf.p.map η.b) η.b := by
    letI : Yf.p.IsStronglyCartesian f η.b := hb
    letI : Yf.p.IsHomLift f η.b := hb_over
    exact
      isStronglyCartesian_of_external_hom_lift
        (p := Yf.p) (R := V) (S := P.U) (f := f) η.b
  have hη :
      (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsStronglyCartesian
        f η :=
    explicitTwoFibreProduct_hom_isStronglyCartesian_of_components F G η ha hb
  -- The canonical component pullbacks assemble to the desired strongly cartesian lift.
  exact ⟨Q, η, hηa, hηb, hη⟩

/-- Helper for Lemma 4.39.4: the explicit pullback projection is fibred for morphisms of fibred
categories over `C`. -/
private theorem explicitTwoFibreProductProjection_isFibered
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsFibered := by
  -- Prove fibredness from the textbook pullback construction itself.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro P V f
  obtain ⟨Q, η, _, _, hη⟩ := explicitTwoFibreProduct_exists_isStronglyCartesian F G P f
  exact ⟨Q, η, hη⟩

end FibredCategoryPullback

namespace FibredInSetoidsOver

/-- Helper for Lemma 4.39.4: a morphism in the fibre of the explicit `2`-fibre product over `U`
has left component lying over the identity of `U`. -/
private theorem explicitTwoFibreProduct_fiber_left_over_id
    (F : X ⟶ S) (G : Y ⟶ S)
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProductOver F G).p U}
    (φ : P ⟶ Q) :
    X.p.IsHomLift (𝟙 U) φ.1.a := by
  -- After normalizing the outer fibre equalities, the stored left component is visibly vertical.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  letI : (explicitTwoFibreProductOver F G).p.IsHomLift (𝟙 UP) φ.1 := φ.2
                  have hbase : φ.1.base = 𝟙 UP := by
                    simpa [explicitTwoFibreProductOver] using
                      (IsHomLift.fac' ((explicitTwoFibreProductOver F G).p) (𝟙 UP) φ.1)
                  simpa [hbase, explicitTwoFibreProductOver] using φ.1.a_over

/-- Helper for Lemma 4.39.4: a morphism in the fibre of the explicit `2`-fibre product over `U`
has right component lying over the identity of `U`. -/
private theorem explicitTwoFibreProduct_fiber_right_over_id
    (F : X ⟶ S) (G : Y ⟶ S)
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProductOver F G).p U}
    (φ : P ⟶ Q) :
    Y.p.IsHomLift (𝟙 U) φ.1.b := by
  -- The right component is treated by the same outer-fibre normalization.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  letI : (explicitTwoFibreProductOver F G).p.IsHomLift (𝟙 UP) φ.1 := φ.2
                  have hbase : φ.1.base = 𝟙 UP := by
                    simpa [explicitTwoFibreProductOver] using
                      (IsHomLift.fac' ((explicitTwoFibreProductOver F G).p) (𝟙 UP) φ.1)
                  simpa [hbase, explicitTwoFibreProductOver] using φ.1.b_over

/-- Helper for Lemma 4.39.4: each fibre of the explicit `2`-fibre product projection is thin. -/
private theorem explicitTwoFibreProduct_fiber_isThin
    (F : X ⟶ S) (G : Y ⟶ S) (U : C) :
    Quiver.IsThin ((explicitTwoFibreProductOver F G).p.Fiber U) := by
  intro P Q
  refine ⟨fun φ ψ ↦ ?_⟩
  -- Equality of fibre morphisms is detected on the left and right fibre components.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  apply Functor.Fiber.hom_ext
                  apply ExplicitTwoFibreProductHom.ext
                  · let φfst : Pobj.fst ⟶ Qobj.fst :=
                        ⟨φ.1.a, explicitTwoFibreProduct_fiber_left_over_id F G φ⟩
                    let ψfst : Pobj.fst ⟶ Qobj.fst :=
                        ⟨ψ.1.a, explicitTwoFibreProduct_fiber_left_over_id F G ψ⟩
                    exact congrArg (fun f ↦ f.1) (Subsingleton.elim φfst ψfst)
                  · let φsnd : Pobj.snd ⟶ Qobj.snd :=
                        ⟨φ.1.b, explicitTwoFibreProduct_fiber_right_over_id F G φ⟩
                    let ψsnd : Pobj.snd ⟶ Qobj.snd :=
                        ⟨ψ.1.b, explicitTwoFibreProduct_fiber_right_over_id F G ψ⟩
                    exact congrArg (fun f ↦ f.1) (Subsingleton.elim φsnd ψsnd)

/-- Helper for Lemma 4.39.4: every morphism in a fibre of the explicit pullback projection is an
isomorphism. -/
private theorem explicitTwoFibreProduct_fiber_hom_isIso
    (F : X ⟶ S) (G : Y ⟶ S)
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProductOver F G).p U}
    (φ : P ⟶ Q) : IsIso φ := by
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  let φfst : Pobj.fst ⟶ Qobj.fst :=
                    ⟨φ.1.a, explicitTwoFibreProduct_fiber_left_over_id F G φ⟩
                  let φsnd : Pobj.snd ⟶ Qobj.snd :=
                    ⟨φ.1.b, explicitTwoFibreProduct_fiber_right_over_id F G φ⟩
                  let ψfst : Qobj.fst ⟶ Pobj.fst := inv φfst
                  let ψsnd : Qobj.snd ⟶ Pobj.snd := inv φsnd
                  let eA : Pobj.fst.1 ≅ Qobj.fst.1 :=
                    { hom := φfst.1
                      inv := ψfst.1
                      hom_inv_id := by
                        exact congrArg (fun f ↦ f.1) (Iso.hom_inv_id (asIso φfst))
                      inv_hom_id := by
                        exact congrArg (fun f ↦ f.1) (Iso.inv_hom_id (asIso φfst)) }
                  let eB : Pobj.snd.1 ≅ Qobj.snd.1 :=
                    { hom := φsnd.1
                      inv := ψsnd.1
                      hom_inv_id := by
                        exact congrArg (fun f ↦ f.1) (Iso.hom_inv_id (asIso φsnd))
                      inv_hom_id := by
                        exact congrArg (fun f ↦ f.1) (Iso.inv_hom_id (asIso φsnd)) }
                  let eFA : (FibredInSetoidsOver.toBasedFunctor F).toFunctor.obj Pobj.fst.1 ≅
                      (FibredInSetoidsOver.toBasedFunctor F).toFunctor.obj Qobj.fst.1 :=
                    Functor.mapIso (FibredInSetoidsOver.toBasedFunctor F).toFunctor eA
                  let eGB : (FibredInSetoidsOver.toBasedFunctor G).toFunctor.obj Pobj.snd.1 ≅
                      (FibredInSetoidsOver.toBasedFunctor G).toFunctor.obj Qobj.snd.1 :=
                    Functor.mapIso (FibredInSetoidsOver.toBasedFunctor G).toFunctor eB
                  have hcomm :
                      CommSq ((FibredInSetoidsOver.toBasedFunctor F).toFunctor.map ψfst.1)
                        Qobj.iso.hom.1 Pobj.iso.hom.1
                        ((FibredInSetoidsOver.toBasedFunctor G).toFunctor.map ψsnd.1) := by
                    simpa [eFA, eGB, eA, eB] using
                      (CommSq.horiz_inv (f := eFA) (i := eGB) φ.1.comm)
                  let ψ0 :
                      ({ U := UP, obj := Qobj } : (explicitTwoFibreProductOver F G).obj) ⟶
                        ({ U := UP, obj := Pobj } : (explicitTwoFibreProductOver F G).obj) :=
                    { base := 𝟙 UP
                      a := ψfst.1
                      a_over := ψfst.2
                      b := ψsnd.1
                      b_over := ψsnd.2
                      comm := hcomm }
                  have hψ0 : (explicitTwoFibreProductOver F G).p.IsHomLift (𝟙 UP) ψ0 := by
                    refine IsHomLift.of_fac' (explicitTwoFibreProductOver F G).p (𝟙 UP) ψ0 rfl rfl ?_
                    simpa using (show (explicitTwoFibreProductOver F G).p.map ψ0 = 𝟙 UP by rfl)
                  refine ⟨⟨?_, ?_, ?_⟩⟩
                  · exact
                      @Functor.Fiber.homMk _ _ _ _ (explicitTwoFibreProductOver F G).p UP _ _ ψ0 hψ0
                  · apply Functor.Fiber.hom_ext
                    apply ExplicitTwoFibreProductHom.ext
                    · exact congrArg (fun f ↦ f.1) (Iso.hom_inv_id (asIso φfst))
                    · exact congrArg (fun f ↦ f.1) (Iso.hom_inv_id (asIso φsnd))
                  · apply Functor.Fiber.hom_ext
                    apply ExplicitTwoFibreProductHom.ext
                    · exact congrArg (fun f ↦ f.1) (Iso.inv_hom_id (asIso φfst))
                    · exact congrArg (fun f ↦ f.1) (Iso.inv_hom_id (asIso φsnd))

/-- Helper for Lemma 4.39.4: each fibre of the explicit `2`-fibre product projection is a
groupoid. -/
private theorem explicitTwoFibreProduct_fiber_isGroupoid
    (F : X ⟶ S) (G : Y ⟶ S) (U : C) :
    IsGroupoid ((explicitTwoFibreProductOver F G).p.Fiber U) where
  all_isIso φ := explicitTwoFibreProduct_fiber_hom_isIso F G φ

/-- Lemma 4.39.4: the explicit pullback projection is again fibred in setoids. -/
theorem explicitTwoFibreProductProjection_isFibredInSetoids
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSetoids (explicitTwoFibreProductOver F G).p := by
  letI : (explicitTwoFibreProductOver F G).p.IsFibered :=
    show (explicitTwoFibreProductOver F G).p.IsFibered from
      explicitTwoFibreProductProjection_isFibered
        (F := (show X.toFibredCategoryOver ⟶ S.toFibredCategoryOver from F.toHom))
        (G := (show Y.toFibredCategoryOver ⟶ S.toFibredCategoryOver from G.toHom))
  letI : IsFibredInGroupoids (explicitTwoFibreProductOver F G).p :=
    CategoryTheory.isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (explicitTwoFibreProductOver F G).p inferInstance
      (explicitTwoFibreProduct_fiber_isGroupoid F G)
  letI : ∀ U : C, Quiver.IsThin ((explicitTwoFibreProductOver F G).p.Fiber U) :=
    explicitTwoFibreProduct_fiber_isThin F G
  infer_instance

/-- The explicit pullback projection carries the canonical fibred-in-setoids structure. -/
instance (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSetoids (explicitTwoFibreProductOver F G).p :=
  explicitTwoFibreProductProjection_isFibredInSetoids F G

end FibredInSetoidsOver

end CategoryTheory

/-! ### Lemma_4_39_5 (from Chap04) -/
universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite
open BasedFunctor
open CategoryOfElements

namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/-- The restriction map on isomorphism classes induced by the canonical pullback functor. -/
private noncomputable def fiberIsoClassPresheafMap
    (p : S ⥤ C) [p.IsFibered] {U V : Cᵒᵖ} (f : U ⟶ V) :
    isomorphismClasses.obj (Cat.of (p.Fiber (unop U))) →
      isomorphismClasses.obj (Cat.of (p.Fiber (unop V))) :=
  isomorphismClasses.map ((canonicalPullbackChoice p).pullbackFunctor f.unop).toCatHom

/-- Pullback along an identity morphism acts trivially on isomorphism classes in the fibers. -/
private theorem fiberIsoClassPresheafMap_id
    (p : S ⥤ C) [p.IsFibered] (U : Cᵒᵖ) :
    fiberIsoClassPresheafMap p (𝟙 U) = id := by
  -- Compare the chosen identity pullback object with the original fiber object via the
  -- canonical pullback-identity isomorphism, then pass to isomorphism classes.
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (p.Fiber (unop U)))
        (((canonicalPullbackChoice p).pullbackFunctor (𝟙 (unop U))).obj x) =
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (p.Fiber (unop U))) x
  rw [Quotient.eq'']
  exact ⟨((canonicalPullbackChoice p).pullbackIdIso (unop U)).symm.app x⟩

/-- Pullback on isomorphism classes is contravariantly functorial in the base morphism. -/
private theorem fiberIsoClassPresheafMap_comp
    (p : S ⥤ C) [p.IsFibered] {U V W : Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    fiberIsoClassPresheafMap p (f ≫ g) =
      fiberIsoClassPresheafMap p g ∘
        fiberIsoClassPresheafMap p f := by
  -- Compare the chosen pullback of the composite with the iterated chosen pullback using the
  -- canonical composition isomorphism, then quotient by isomorphism.
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (p.Fiber (unop W)))
        (((canonicalPullbackChoice p).pullbackFunctor (g.unop ≫ f.unop)).obj x) =
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (p.Fiber (unop W)))
        ((((canonicalPullbackChoice p).pullbackFunctor f.unop ⋙
          (canonicalPullbackChoice p).pullbackFunctor g.unop).obj x))
  rw [Quotient.eq'']
  exact ⟨((canonicalPullbackChoice p).pullbackCompIso f.unop g.unop).app x⟩

/-- The presheaf sending `U` to the set of isomorphism classes of objects in the fiber `p⁻¹(U)`.
-/
noncomputable def fiberIsoClassPresheaf
    (p : S ⥤ C) [p.IsFibered] : Presheaf.{u₂} C where
  obj U := isomorphismClasses.obj (Cat.of (p.Fiber (unop U)))
  map f := fiberIsoClassPresheafMap p f
  map_id := fiberIsoClassPresheafMap_id p
  map_comp := fiberIsoClassPresheafMap_comp p

end Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {X : BasedCategory C}

/- Domain-style sampling for Lemma 4.39.5:
- primary domain: categories over a fixed base, compared by based equivalences and by the induced
  maps on isomorphism classes in each fiber;
- sampled owner-level declarations:
  `BasedFunctor.IsEquivalenceOverBase`,
  `BasedFunctor.fiberFunctor`,
  `IsFibredInSetoids`,
  `FibredInSetoidsOver.associatedFibredInSets`,
  `Functor.fiberIsoClassPresheaf`,
  `presheafToFibredInSetsOver`,
  `FibredInSetoidsOver.ofAmbientHom`;
- best owner abstraction: the based functor over `C` for the fiberwise clauses, and the canonical
  associated fibred-in-sets object `FibredInSetoidsOver.associatedFibredInSets` for the
  replacement-by-sets clause; the comparison morphism should expose only the owner hom, with its
  underlying based functor kept as internal bridge data;
- primitive data: bundled categories over `C` and, for the replacement-by-sets clause, the
  underlying based functor from `Z` to the category of elements of `Z.p.fiberIsoClassPresheaf`;
- derived API: the transported setoid condition, the induced bijection on isomorphism classes in
  each fiber, and the canonical comparison with the associated fibred-in-sets model.

Source/core/bridge triage:
- `source-facing`: the first two clauses of the lemma together with the canonical replacement by
  an associated fibred-in-sets object;
- `core/canonical`: `BasedFunctor.IsEquivalenceOverBase`, `BasedFunctor.fiberFunctor`,
  `IsFibredInSetoids`, `Functor.fiberIsoClassPresheaf`, and
  `FibredInSetoidsOver.associatedFibredInSets Z`;
- `bridge/view`: the internal based functor to the category of elements of
  `Z.p.fiberIsoClassPresheaf`, and the induced owner morphism `Z.toFibredInSets`. -/

namespace BasedFunctor

section

/-- In a discrete category, taking isomorphism classes is canonically equivalent to taking
objects. -/
private noncomputable def isoClassesEquivOfIsDiscrete
    (D : Type u₂) [Category.{v₂} D] [IsDiscrete D] :
    isomorphismClasses.obj (Cat.of D) ≃ D :=
  (Equiv.ofBijective
      (fun x : D ↦ Quotient.mk'' x)
      (by
        constructor
        · intro x y hxy
          exact Quotient.exact hxy |>.elim fun i ↦ obj_ext_of_isDiscrete i.hom
        · intro q
          refine Quotient.inductionOn q ?_
          intro x
          exact ⟨x, rfl⟩)).symm

/-- An equivalence over the base induces a bijection on isomorphism classes in each fiber. -/
private theorem fiberIsoClassMap_bijective_of_isEquivalenceOverBase
    {Y : BasedCategory C} (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase) (U : C) :
    Function.Bijective (isomorphismClasses.map (F.fiberFunctor U).toCatHom) := by
  letI : (F.fiberFunctor U).IsEquivalence :=
    BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase F hF U
  let e := (F.fiberFunctor U).asEquivalence
  have hleft :
      Function.LeftInverse
        (isomorphismClasses.map e.inverse.toCatHom)
        (isomorphismClasses.map (F.fiberFunctor U).toCatHom) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    change
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (X.p.Fiber U))
          (e.inverse.obj ((F.fiberFunctor U).obj x)) =
        @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (X.p.Fiber U)) x
    rw [Quotient.eq'']
    exact ⟨e.unitIso.symm.app x⟩
  constructor
  · intro q₁ q₂ hq
    -- Cancel the forward map on the left by applying the inverse equivalence on classes.
    exact hleft.injective hq
  · intro q
    -- Represent any target isomorphism class by an actual fiber object and then pull it back
    -- along the quasi-inverse.
    refine Quotient.inductionOn q ?_
    intro y
    refine ⟨Quotient.mk'' (e.inverse.obj y), ?_⟩
    change
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber U))
          ((F.fiberFunctor U).obj (e.inverse.obj y)) =
        @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Y.p.Fiber U)) y
    rw [Quotient.eq'']
    exact ⟨e.counitIso.app y⟩

/-- If the target is fibred in sets, then its fiber over `U` is canonically identified with the
set of isomorphism classes in the source fiber over `U`. -/
noncomputable def fiberIsoClassesEquivFiber_of_isEquivalenceOverBase
    {Y : BasedCategory C} (F : X ⥤ᵇ Y) (hF : F.IsEquivalenceOverBase)
    [IsFibredInSets Y.p] (U : C) :
    isomorphismClasses.obj (Cat.of (X.p.Fiber U)) ≃ Y.p.Fiber U :=
  (Equiv.ofBijective
      (isomorphismClasses.map (F.fiberFunctor U).toCatHom)
      (fiberIsoClassMap_bijective_of_isEquivalenceOverBase F hF U)).trans
    (isoClassesEquivOfIsDiscrete (Y.p.Fiber U))

end

end BasedFunctor

namespace FibredInSetoidsOver

/-- Lemma 4.39.5: the category fibred in sets associated to `Z`, obtained from the category of
elements of the presheaf of fiberwise isomorphism classes. -/
noncomputable def associatedFibredInSets
    (Z : FibredInSetoidsOver C) :
    FibredInSetsOver C :=
  FibredInSetsOver.ofFunctor ((CategoryOfElements.π Z.p.fiberIsoClassPresheaf).leftOp)

private noncomputable def fiberIsoClassElement
    (Z : FibredInSetoidsOver C) :
    Z.S → (Z.p.fiberIsoClassPresheaf).Elements :=
  fun a ↦
    (Z.p.fiberIsoClassPresheaf).elementsMk (op (Z.p.obj a)) (Quotient.mk'' ⟨a, rfl⟩)

/-- Helper for Lemma 4.39.5: pulling back the isomorphism class of `b` along the base map of
`φ : a ⟶ b` recovers the isomorphism class of `a`. -/
private theorem fiberIsoClassElement_map_eq
    (Z : FibredInSetoidsOver C) {a b : Z.S} (φ : a ⟶ b) :
    (Z.p.fiberIsoClassPresheaf).map (Z.p.map φ).op (Quotient.mk'' ⟨b, rfl⟩) =
      Quotient.mk'' ⟨a, rfl⟩ := by
  -- Compare `φ` with the chosen pullback map of `b` along the same base arrow; cartesian
  -- uniqueness gives an isomorphism between their domains, hence equality of classes.
  let hc := canonicalPullbackChoice Z.p
  letI : Z.p.IsStronglyCartesian (Z.p.map φ) (hc.map (Z.p.map φ) ⟨b, rfl⟩) :=
    hc.isStronglyCartesian (Z.p.map φ) ⟨b, rfl⟩
  change
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber (Z.p.obj a)))
        (((canonicalPullbackChoice Z.p).pullbackFunctor (Z.p.map φ)).obj ⟨b, rfl⟩) =
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber (Z.p.obj a))) ⟨a, rfl⟩
  let e := Functor.IsCartesian.domainUniqueUpToIso Z.p (Z.p.map φ)
    (hc.map (Z.p.map φ) ⟨b, rfl⟩) φ
  have hInvLift : Z.p.IsHomLift (𝟙 (Z.p.obj a)) e.inv := by
    change Z.p.IsHomLift (𝟙 (Z.p.obj a))
      ((Functor.IsCartesian.domainUniqueUpToIso Z.p (Z.p.map φ)
        (hc.map (Z.p.map φ) ⟨b, rfl⟩) φ).inv)
    infer_instance
  have hHomLift : Z.p.IsHomLift (𝟙 (Z.p.obj a)) e.hom := by
    change Z.p.IsHomLift (𝟙 (Z.p.obj a))
      ((Functor.IsCartesian.domainUniqueUpToIso Z.p (Z.p.map φ)
        (hc.map (Z.p.map φ) ⟨b, rfl⟩) φ).hom)
    infer_instance
  let eFiber :
      (((canonicalPullbackChoice Z.p).pullbackFunctor (Z.p.map φ)).obj ⟨b, rfl⟩) ≅
        ⟨a, rfl⟩ :=
    { hom := ⟨e.inv, hInvLift⟩
      inv := ⟨e.hom, hHomLift⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id }
  rw [Quotient.eq'']
  exact ⟨eFiber⟩

private noncomputable def toFibredInSetsBasedFunctor
    (Z : FibredInSetoidsOver C) :
    Z.toBasedCategory ⥤ᵇ Z.associatedFibredInSets.toBasedCategory :=
  { toFunctor :=
      { obj := fun a ↦ op (fiberIsoClassElement Z a)
        map := fun {a b} φ ↦
          Quiver.Hom.op <|
            homMk
              (fiberIsoClassElement Z b)
              (fiberIsoClassElement Z a)
              (Z.p.map φ).op
              (by
                -- The category-of-elements morphism is well defined precisely because the source
                -- morphism transports the class of `b` to the class of `a`.
                simpa using fiberIsoClassElement_map_eq Z φ)
        map_id := by
          intro a
          apply Quiver.Hom.unop_inj
          apply ext (Z.p.fiberIsoClassPresheaf)
          change (Z.p.map (𝟙 a)).op = 𝟙 (op (Z.p.obj a))
          simp
        map_comp := by
          intro a b c φ ψ
          apply Quiver.Hom.unop_inj
          apply ext (Z.p.fiberIsoClassPresheaf)
          change (Z.p.map (φ ≫ ψ)).op = (Z.p.map ψ).op ≫ (Z.p.map φ).op
          simp }
    w := rfl }

/-- The canonical comparison from a category fibred in setoids over `C` to the associated
category fibred in sets `Z.associatedFibredInSets`, given by the category of elements of the
owner presheaf `Z.p.fiberIsoClassPresheaf`. -/
noncomputable abbrev toFibredInSets
    (Z : FibredInSetoidsOver C) :
    Z ⟶ Z.associatedFibredInSets :=
  ofBasedFunctor (toFibredInSetsBasedFunctor Z)

/-- Helper for Lemma 4.39.5: the canonical comparison viewed in the ambient
`FibredInGroupoidsOver` owner. -/
private noncomputable abbrev toFibredInSets_ambientHom
    (Z : FibredInSetoidsOver C) :
    Z.toFibredInGroupoidsOver ⟶ Z.associatedFibredInSets.toFibredInGroupoidsOver :=
  FibredInGroupoidsMor.ofBasedFunctor (toFibredInSetsBasedFunctor Z)

/-- Helper for Lemma 4.39.5: the functor induced on the fiber over `U` by the canonical
comparison `Z.toFibredInSets`. -/
private noncomputable abbrev toFibredInSets_fiberFunctor
    (Z : FibredInSetoidsOver C) (U : C) :=
  (toFibredInSetsBasedFunctor Z).fiberFunctor U

/-- Helper for Lemma 4.39.5: the ambient owner fiber functor of the canonical comparison agrees
definitionally with the local fiber functor used in the quotient-by-isomorphism-classes proof. -/
private theorem toFibredInSets_fiberFunctor_defeq
    (Z : FibredInSetoidsOver C) (U : C) :
    _root_.CategoryTheory.FibredInGroupoidsMor.fiberFunctor
        (toFibredInSets_ambientHom Z) U =
      toFibredInSets_fiberFunctor Z U :=
  rfl

/-- Helper for Lemma 4.39.5: the fiber of the associated fibred-in-sets object over `U` is
identified with the set of isomorphism classes in the source fiber over `U`. -/
private noncomputable def associated_fiber_equiv_iso_classes
    (Z : FibredInSetoidsOver C) (U : C) :
    Z.associatedFibredInSets.p.Fiber U ≃ isomorphismClasses.obj (Cat.of (Z.p.Fiber U)) where
  toFun y := by
    rcases y with ⟨y, hy⟩
    cases h : y.unop with
    | mk U' q =>
        have hyobj : y = op ⟨U', q⟩ := by
          apply Opposite.unop_injective
          simp [h]
        subst y
        have hy' : unop U' = U := by
          simpa [FibredInSetoidsOver.associatedFibredInSets, FibredInSetsOver.ofFunctor,
            FibredInSetsOver.p, FibredInGroupoidsOver.ofFunctor, FibredInGroupoidsOver.p,
            FibredCategoryOver.ofFunctor, FibredCategoryOver.p] using hy
        cases hy'
        simpa using q
  invFun q := ⟨op ((Z.p.fiberIsoClassPresheaf).elementsMk (op U) q), rfl⟩
  left_inv := by
    intro y
    rcases y with ⟨y, hy⟩
    cases h : y.unop with
    | mk U' q =>
        have hyobj : y = op ⟨U', q⟩ := by
          apply Opposite.unop_injective
          simp [h]
        subst y
        have hy' : unop U' = U := by
          simpa [FibredInSetoidsOver.associatedFibredInSets, FibredInSetsOver.ofFunctor,
            FibredInSetsOver.p, FibredInGroupoidsOver.ofFunctor, FibredInGroupoidsOver.p,
            FibredCategoryOver.ofFunctor, FibredCategoryOver.p] using hy
        cases hy'
        rfl
  right_inv := by
    intro q
    rfl

/-- Helper for Lemma 4.39.5: every quotient class is sent back by the inverse equivalence to the
corresponding image object in the associated fiber. -/
private theorem associated_fiber_equiv_iso_classes_symm_obj
    (Z : FibredInSetoidsOver C) (U : C) (x : Z.p.Fiber U) :
    (associated_fiber_equiv_iso_classes Z U).symm (Quotient.mk'' x) =
      (toFibredInSets_fiberFunctor Z U).obj x := by
  rcases x with ⟨x, hx⟩
  cases hx
  rfl

/-- Helper for Lemma 4.39.5: the above fiber equivalence sends the image of a source fiber object
to its isomorphism class. -/
private theorem associated_fiber_equiv_iso_classes_apply_obj
    (Z : FibredInSetoidsOver C) (U : C) (x : Z.p.Fiber U) :
    associated_fiber_equiv_iso_classes Z U ((toFibredInSets_fiberFunctor Z U).obj x) =
      Quotient.mk'' x := by
  have h :=
    congrArg (associated_fiber_equiv_iso_classes Z U)
      (associated_fiber_equiv_iso_classes_symm_obj Z U x)
  simpa using h.symm

/-- Helper for Lemma 4.39.5: every object of the target fiber is represented by the image of some
object of the source fiber. -/
private theorem toFibredInSets_fiberFunctor_obj_preimage
    (Z : FibredInSetoidsOver C) (U : C) (y : Z.associatedFibredInSets.p.Fiber U) :
    ∃ x : Z.p.Fiber U, Nonempty ((toFibredInSets_fiberFunctor Z U).obj x ≅ y) := by
  let e := associated_fiber_equiv_iso_classes Z U
  have hpre :
      ∀ q : isomorphismClasses.obj (Cat.of (Z.p.Fiber U)),
        ∃ x : Z.p.Fiber U, Nonempty ((toFibredInSets_fiberFunctor Z U).obj x ≅ e.symm q) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    refine ⟨x, ?_⟩
    -- A chosen representative lands exactly on the inverse image of its class.
    exact ⟨eqToIso (associated_fiber_equiv_iso_classes_symm_obj Z U x).symm⟩
  simpa using hpre (e y)

/-- Helper for Lemma 4.39.5: if two source-fiber objects have the same image in the associated
fiber, then they define the same isomorphism class in the source fiber. -/
private theorem fiberIsoClass_eq_of_toFibredInSets_obj_eq
    (Z : FibredInSetoidsOver C) (U : C) {x y : Z.p.Fiber U}
    (hxy :
      (toFibredInSets_fiberFunctor Z U).obj x =
        (toFibredInSets_fiberFunctor Z U).obj y) :
    @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber U)) x =
      @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber U)) y := by
  -- Compare the two equal target objects through the explicit quotient description of the target
  -- fiber, which turns object equality into equality of source isomorphism classes.
  have heq :
      (associated_fiber_equiv_iso_classes Z U)
          ((toFibredInSets_fiberFunctor Z U).obj x) =
        (associated_fiber_equiv_iso_classes Z U)
          ((toFibredInSets_fiberFunctor Z U).obj y) := by
    exact congrArg (fun z ↦ associated_fiber_equiv_iso_classes Z U z) hxy
  exact
    (associated_fiber_equiv_iso_classes_apply_obj Z U x).symm.trans
      (heq.trans (associated_fiber_equiv_iso_classes_apply_obj Z U y))

/-- Helper for Lemma 4.39.5: on each fiber, the canonical comparison is an equivalence between
the thin source groupoid and the discrete quotient by isomorphism classes. -/
private theorem toFibredInSets_fiberFunctor_isEquivalence
    (Z : FibredInSetoidsOver C) (U : C) :
    (toFibredInSets_fiberFunctor Z U).IsEquivalence := by
  let F := toFibredInSets_fiberFunctor Z U
  letI : F.Faithful := by
    refine ⟨?_⟩
    intro x y φ ψ hφψ
    -- The source fiber is thin, so there is at most one morphism to compare.
    exact Subsingleton.elim φ ψ
  letI : F.Full := by
    refine ⟨?_⟩
    intro x y φ
    -- Discreteness of the target fiber turns the target morphism into equality of image objects.
    have hobj : F.obj x = F.obj y := obj_ext_of_isDiscrete φ
    have hclass :
        @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber U)) x =
          @Quotient.mk'' _ (CategoryTheory.isIsomorphicSetoid (Z.p.Fiber U)) y :=
      fiberIsoClass_eq_of_toFibredInSets_obj_eq Z U hobj
    rcases Quotient.exact hclass with ⟨i⟩
    refine ⟨i.hom, ?_⟩
    -- The target fiber is also thin, so the lifted morphism is forced to equal `φ`.
    exact Subsingleton.elim _ _
  -- Chosen representatives for quotient classes give objectwise preimages in the target fiber.
  exact
    Functor.fully_faithful_isEquivalence_of_objwise_iso (F := F)
      (fun y ↦ Classical.choose (toFibredInSets_fiberFunctor_obj_preimage Z U y))
      (fun y ↦
        (Classical.choice
          (Classical.choose_spec (toFibredInSets_fiberFunctor_obj_preimage Z U y))).symm)

/-- The canonical comparison from a category fibred in setoids over `C` to its associated
category fibred in sets is an equivalence over the base. -/
-- Route correction: instead of trying to transport fibred-in-setoids structure abstractly across
-- an arbitrary equivalence over the base, we follow the source proof and identify each target
-- fiber with isomorphism classes in the source fiber, then prove the canonical comparison is a
-- fiberwise equivalence.
-- Proof sketch: identify the target with the category of elements of the presheaf of fiberwise
-- isomorphism classes and apply the fiberwise equivalence criterion from the first part of the
-- lemma to the canonical comparison functor `Z.toFibredInSets`.
theorem toFibredInSets_isEquivalenceOverBase
    (Z : FibredInSetoidsOver C) :
    IsEquivalenceOverBase (Z.toFibredInSets) :=
  by
    let F : Z.toFibredInGroupoidsOver ⟶ Z.associatedFibredInSets.toFibredInGroupoidsOver :=
      toFibredInSets_ambientHom Z
    have hFiber :
        ∀ U : C, (_root_.CategoryTheory.FibredInGroupoidsMor.fiberFunctor F U).IsEquivalence := by
      intro U
      -- Rewrite the owner-level fiber functor to the local canonical one and apply the fiberwise
      -- equivalence already proved above.
      simpa [F, toFibredInSets_fiberFunctor_defeq] using
        toFibredInSets_fiberFunctor_isEquivalence Z U
    have hEq : (FibredInGroupoidsMor.G F).IsEquivalence := by
      -- Apply the owner-level fiberwise criterion after proving each fiber functor is an equivalence.
      exact (_root_.CategoryTheory.FibredInGroupoidsMor.isEquivalence_iff_fiberwise (F := F)).2
        hFiber
    -- Upgrade the ambient equivalence to an equivalence over the base category.
    simpa [FibredInSetoidsOver.IsEquivalenceOverBase] using
      _root_.CategoryTheory.FibredInGroupoidsMor.isEquivalenceOverBase_of_isEquivalence (F := F) hEq

end FibredInSetoidsOver

end CategoryTheory
