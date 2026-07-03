import Mathlib
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_38_1 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 4.38.1:
- primary domain: discrete categories;
- inspected owner-level declarations:
  `CategoryTheory.IsDiscrete`,
  `CategoryTheory.obj_ext_of_isDiscrete`,
  `CategoryTheory.isIso_of_isDiscrete`,
  `CategoryTheory.Discrete.isDiscrete`;
- best owner abstraction: `CategoryTheory.IsDiscrete`;
- primitive owner data: `IsDiscrete.subsingleton` and `IsDiscrete.eq_of_hom`;
- derived API: `obj_ext_of_isDiscrete`, `isIso_of_isDiscrete`, and the source wording that every
  morphism is a transported identity, recovered directly from the primitive owner data. -/

/- Definition 4.38.1: a category is discrete exactly when every morphism is an identity morphism
after identifying its source and target. This is the canonical mathlib class
`CategoryTheory.IsDiscrete`. -/
recall IsDiscrete

/- Source/core/bridge triage for Definition 4.38.1:
- core/canonical owner: `CategoryTheory.IsDiscrete`;
- source-facing layer: this item is recall-only, and the textbook wording is recovered directly
  from `IsDiscrete.eq_of_hom` together with subsingleton hom-spaces;
- primitive owner data: `IsDiscrete.subsingleton` and `IsDiscrete.eq_of_hom`;
- derived API: `obj_ext_of_isDiscrete` and the companion bridge theorem below expressing each
  morphism as the transported identity. -/

/- Companion bridge: the textbook assertion that any morphism identifies its source and target is
the owner lemma `obj_ext_of_isDiscrete`. -/
recall obj_ext_of_isDiscrete

/- Companion bridge: in a discrete category every morphism is the identity after transporting
along the canonical equality of its source and target. This matches the source wording directly
without introducing a parallel owner. -/
theorem hom_eq_eqToHom_of_isDiscrete [IsDiscrete C] {X Y : C} (f : X ⟶ Y) :
    f = eqToHom (obj_ext_of_isDiscrete f) :=
  Subsingleton.elim _ _

end CategoryTheory

/-! ### Definition_4_38_2 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/-
Domain-style sampling for Definition 4.38.2:
- primary domain: fibred categories with fiberwise discrete-category structure.
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `Functor.IsFibered`,
  `Functor.Fiber`,
  `IsDiscrete`,
  `isFibredInGroupoids_iff_isFibered_and_fiber_groupoid`,
  `IsFibredInSetoids`.
- best owner abstraction: the source-facing notion here is a fibred-in-groupoids functor whose
  standard fibers are discrete; the public owner should therefore extend the existing chapter
  owner `IsFibredInGroupoids`, while the textbook `p.IsFibered` formulation remains as a
  companion characterization.
- primitive data: `IsFibredInGroupoids p` together with `IsDiscrete (p.Fiber U)` for each base
  object `U`; equivalently, and more primitively on the source side, `p.IsFibered` together with
  `IsDiscrete (p.Fiber U)` for each base object `U`.
- derived API: the owner-level specification theorem
  `isFibredInSets_iff_isFibredInGroupoids_and_fiber_discrete`, instance search on each fiber,
  and downstream setoid-valued specializations.

Source/core/bridge triage:
- `source-facing`: `IsFibredInSets p`.
- `core/canonical`: `IsFibredInGroupoids p`, `Functor.Fiber`, `IsDiscrete`.
- `bridge/view`: the owner-level specification theorem
  `isFibredInSets_iff_isFibredInGroupoids_and_fiber_discrete`, together with the downstream
  coercions to fibred-in-setoids and bundled-over-category APIs. -/

/-- Definition 4.38.2: a category fibred in sets, or a category fibred in discrete categories,
over `C` is a functor `p : S ⥤ C` that is fibred and whose fiber category `p.Fiber U` is discrete
for every object `U` of `C`; equivalently, it is fibred in groupoids with discrete fibers. -/
@[mk_iff isFibredInSets_iff_isFibredInGroupoids_and_fiber_discrete]
class IsFibredInSets (p : S ⥤ C) : Prop extends IsFibredInGroupoids p where
  /-- Each standard fiber of a category fibred in sets is a discrete category. -/
  fiber_isDiscrete (U : C) : IsDiscrete (p.Fiber U)

attribute [instance] IsFibredInSets.fiber_isDiscrete

/-- The owner-level data for a category fibred in sets is exactly fiberedness together with
discrete standard fibers. -/
instance (p : S ⥤ C) [p.IsFibered] [∀ U : C, IsDiscrete (p.Fiber U)] :
    IsFibredInSets p where
  toIsFibredInGroupoids :=
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid p inferInstance fun _ ↦ inferInstance
  fiber_isDiscrete := inferInstance

end CategoryTheory

/-! ### Definition_4_38_3 (from Chap04) -/
universe u v vS w

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

/-
Domain-style sampling for Definition 4.38.3:
- primary domain: categories fibred in sets over a fixed base, viewed as a full sub-`2`-category
  of categories fibred in groupoids.
- inspected owner-level declarations:
  `SubTwoCategory`,
  `SubTwoCategory.Hom.toHom`,
  `SubTwoCategory.Hom`,
  `FibredInGroupoidsOver`,
  `IsFibredInSets`.
- best owner abstraction: the source-facing owner is the full sub-`2`-category of
  `FibredInGroupoidsOver C` cut out by the property `IsFibredInSets X.p`, with inherited
  `1`-morphisms and `2`-morphisms.
- primitive data: a category fibred in groupoids over `C` together with the proof that its
  projection is fibred in sets.
- derived API: the coercions to the ambient fibred-in-groupoids, fibred-category, category-over,
  and based-category owners; the morphism layer is read directly through the ambient owner hom
  `FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver`.

Source/core/bridge triage:
- `source-facing`: `FibredInSetsOver C` together with its owner homs `X ⟶ Y`;
- `core/canonical`: `SubTwoCategory`, `FibredInGroupoidsOver`, `IsFibredInSets`;
- `bridge/view`: the forgetful coercions to ambient owners.

Primitive-vs-derived split:
- primitive data: the underlying category fibred in groupoids over `C` together with the proof
  that its projection is fibred in sets;
- derived API: the inherited strict bicategory structure and the short projections to the ambient
  owner data; the owner morphism bridge is the canonical ambient accessor `F.toHom`, and the
  based-functor API is derived from it. -/

/-- Definition 4.38.3 at the owner level: categories fibred in sets over `C` form the full
sub-`2`-category of `FibredInGroupoidsOver C` cut out by the fibred-in-sets condition. -/
abbrev fibredInSetsOverSubTwoCategory (C : Type u) [Category.{v} C] :
    SubTwoCategory (FibredInGroupoidsOver C) where
  obj := fun X ↦ IsFibredInSets X.p
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

/-- Definition 4.38.3: the objects of the `2`-category of categories fibred in sets over `C` are
the categories over `C` whose projection functor is fibred in sets; equivalently, this is the
full sub-`2`-category of categories fibred in groupoids over `C` cut out by the fibred-in-sets
condition. -/
abbrev FibredInSetsOver (C : Type u) [Category.{v} C] :=
  (fibredInSetsOverSubTwoCategory C).Obj

instance : Bicategory (FibredInSetsOver C) :=
  SubTwoCategory.bicategoryObj (fibredInSetsOverSubTwoCategory C)

instance : Bicategory.Strict (FibredInSetsOver C) :=
  SubTwoCategory.strictObj (fibredInSetsOverSubTwoCategory C)

instance fibredInSetsOverCategory : Category (FibredInSetsOver C) :=
  StrictBicategory.category (FibredInSetsOver C)

instance fibredInSetsOverHom₂IsMultiplicative (X Y : FibredInSetsOver C) :
    ((fibredInSetsOverSubTwoCategory C).hom₂ X Y).IsMultiplicative :=
  ((fibredInSetsOverSubTwoCategory C).hom X Y).hom_isMultiplicative

instance fibredInSetsOverHomInclusionFull (X Y : FibredInSetsOver C) :
    (((fibredInSetsOverSubTwoCategory C).hom X Y).inclusion).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨ObjectProperty.homMk η, trivial⟩, rfl⟩

instance fibredInSetsOverHomWideInclusionFull (X Y : FibredInSetsOver C) :
    (wideSubcategoryInclusion ((fibredInSetsOverSubTwoCategory C).hom₂ X Y)).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨η, trivial⟩, rfl⟩

namespace FibredInSetsOver

/-- Build a bundled category fibred in sets over `C` from a functor to `C`. -/
abbrev ofFunctor {S : Type w} [Category.{vS} S] (p : S ⥤ C) [IsFibredInSets p] :
    FibredInSetsOver C :=
  ⟨FibredInGroupoidsOver.ofFunctor p, by
    simpa [FibredInGroupoidsOver.p, FibredInGroupoidsOver.ofFunctor] using
      (inferInstance : IsFibredInSets p)⟩

/-- The underlying category fibred in groupoids over `C`. -/
abbrev toFibredInGroupoidsOver (X : FibredInSetsOver C) : FibredInGroupoidsOver C :=
  X.obj

/-- The underlying fibred category over `C`. -/
abbrev toFibredCategoryOver (X : FibredInSetsOver C) : FibredCategoryOver C :=
  (X.toFibredInGroupoidsOver : FibredCategoryOver C)

/-- The underlying category over `C`. -/
abbrev toCategoryOver (X : FibredInSetsOver C) : CategoryOver C :=
  X.toFibredInGroupoidsOver.toCategoryOver

/-- The total category of a bundled category fibred in sets over `C`. -/
abbrev S (X : FibredInSetsOver C) :=
  X.toFibredInGroupoidsOver.S

/-- The projection functor of a bundled category fibred in sets over `C`. -/
abbrev p (X : FibredInSetsOver C) :=
  X.toFibredInGroupoidsOver.p

/-- The defining property of an object of `FibredInSetsOver C`: its projection functor is
fibred in sets. -/
-- Proof sketch: This is the property field of the corresponding object of the full
-- sub-`2`-category.
theorem isFibredInSets_p (X : FibredInSetsOver C) : IsFibredInSets X.p :=
  X.property

/-- Forget a bundled category fibred in sets over `C` to its underlying based category. -/
abbrev toBasedCategory (X : FibredInSetsOver C) : BasedCategory C :=
  X.toFibredInGroupoidsOver.toBasedCategory

/-- Compatibility coercion to categories fibred in groupoids over `C`. -/
instance : CoeOut (FibredInSetsOver C) (FibredInGroupoidsOver C) where
  coe X := X.toFibredInGroupoidsOver

/-- Compatibility coercion to fibred categories over `C`. -/
instance : CoeOut (FibredInSetsOver C) (FibredCategoryOver C) where
  coe X := X.toFibredCategoryOver

/-- Compatibility coercion to the ambient category `Cat/C`. -/
instance : CoeOut (FibredInSetsOver C) (CategoryOver C) where
  coe X := X.toCategoryOver

/-- Compatibility coercion to the ambient based-category API. -/
instance : CoeOut (FibredInSetsOver C) (BasedCategory C) where
  coe X := X.toBasedCategory

/-- The projection functor of a bundled category fibred in sets over `C` is fibred in sets. -/
instance (X : FibredInSetsOver C) : IsFibredInSets X.p :=
  X.property

variable {X Y : FibredInSetsOver C}

/-- Regard an ambient morphism of the underlying categories fibred in groupoids over `C` as the
corresponding owner hom in the full sub-`2`-category `FibredInSetsOver C`. -/
abbrev ofAmbientHom
    (F : X.toFibredInGroupoidsOver ⟶ Y.toFibredInGroupoidsOver) : X ⟶ Y :=
  { obj := { obj := F, property := trivial } }

/-- The underlying based functor of a morphism of categories fibred in sets over `C`. -/
abbrev toBasedFunctor (F : X ⟶ Y) : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  FibredInGroupoidsMor.toBasedFunctor F.toHom

/- Convert an isomorphism between the ambient morphisms of categories fibred in groupoids into
an isomorphism in the owner hom-category of categories fibred in sets. -/
noncomputable def ofAmbientIso
    {F G : X ⟶ Y}
    (e : F.toHom ≅ G.toHom) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

/-- The induced functor on the fiber over `U`. -/
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  (toBasedFunctor F).fiberFunctor U

/-- The underlying functor between the total categories. -/
abbrev G (F : X ⟶ Y) : X.S ⥤ Y.S :=
  (toBasedFunctor F).toFunctor

/-- The compatibility of the underlying functor with the base projections. -/
abbrev comm (F : X ⟶ Y) : G F ⋙ Y.p = X.p :=
  (toBasedFunctor F).w

/-- A morphism of categories fibred in sets over `C` is canonically viewed as the corresponding
ambient morphism of categories fibred in groupoids over `C`. -/
instance : CoeOut (X ⟶ Y)
    (X.toFibredInGroupoidsOver ⟶ Y.toFibredInGroupoidsOver) where
  coe F := F.toHom

/-- Compatibility coercion from owner morphisms to based functors over `C`. -/
instance : CoeOut (X ⟶ Y) (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := toBasedFunctor F

end FibredInSetsOver

variable {X Y : FibredInSetsOver C}

variable (F G : X ⟶ Y)

/- Definition 4.38.3: a `2`-morphism between `1`-morphisms of categories fibred in sets over `C`
is the inherited morphism in the owner hom-category of the full sub-`2`-category
`fibredInSetsOverSubTwoCategory C`. -/
#check (F ⟶ G)

end CategoryTheory

/-! ### Lemma_4_38_4 (from Chap04) -/
universe v u u_1

namespace CategoryTheory

open CategoryTheory.Limits
open CategoryOver
open BicategoricalTwoCommutativeSquare
open FibredInSetsOver
open scoped Bicategory
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {X Y S : FibredInSetsOver.{u, v, max u v, v} C}

/-- The explicit ambient `2`-fibre product of the underlying based functors of `F` and `G`. -/
private noncomputable abbrev explicitTwoFibreProductOver
    (F : X ⟶ S) (G : Y ⟶ S) :=
  explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)

/- Domain-style sampling for Lemma 4.38.4:
- primary domain: categories fibred in sets over a fixed base and their explicit `2`-fibre
  products in `Cat/C`;
- inspected owner-level declarations:
  `IsFibredInSets`,
  `FibredInSetsOver`,
  `FibredInSetsOver.ofAmbientHom`,
  `FibredInSetsOver.ofAmbientIso`,
  `FibredInGroupoidsOver.twoFibreProduct`,
  `FibredInGroupoidsOver.twoFibreProductSquare`,
  `FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`,
  `explicitTwoFibreProductProjection_isFibredInGroupoids`;
- best owner abstraction: the source-facing owner lives in `FibredInSetsOver C`, obtained by
  rebundling the ambient chapter owner `FibredInGroupoidsOver.twoFibreProduct`; the explicit
  pullback projection theorem is the closure bridge needed to upgrade the ambient apex from
  groupoids to sets.

Primitive-vs-derived split:
- primitive source-facing data: the morphisms `F : X ⟶ S` and `G : Y ⟶ S`;
- derived API: the fibred-in-sets closure theorem on the explicit pullback projection, together
  with the rebundled owner object `FibredInSetsOver.twoFibreProduct`, the canonical square, and
  the inherited finality theorem.

Source/core/bridge triage:
- `source-facing`: `FibredInSetsOver.twoFibreProductSquare` and
  `FibredInSetsOver.twoFibreProduct_isTwoFibreProduct`;
- `core/canonical`: `FibredInGroupoidsOver.twoFibreProductSquare` and
  `FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`;
- `bridge/view`: `explicitTwoFibreProductProjection_isFibredInSets`, which upgrades the ambient
  explicit pullback projection from the fibred-in-groupoids owner to the fibred-in-sets setting,
  enabling the owner-level rebundling in `FibredInSetsOver C`. -/

/-- Helper for Lemma 4.38.4: the categorical pullback of two discrete categories is again
discrete. -/
private theorem categoricalPullback_isDiscrete_of_sources
    {A : Type u} {B : Type u} {T : Type u}
    [Category.{v} A] [Category.{v} B] [Category.{v} T]
    (L : A ⥤ T) (R : B ⥤ T)
    [IsDiscrete A] [IsDiscrete B] :
    IsDiscrete (L ⊡ R) := by
  refine
    { subsingleton := ?_
      eq_of_hom := ?_ }
  · -- Morphisms are determined by their two components, and both component hom-types are
    -- subsingletons in a discrete source category.
    intro P Q
    refine ⟨fun f g ↦ ?_⟩
    apply CategoricalPullback.hom_ext
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  · -- A pullback morphism forces equality on both source components, and then its compatibility
    -- condition identifies the remaining comparison isomorphism.
    intro P Q f
    cases P with
    | mk a b i =>
        cases Q with
        | mk a' b' i' =>
            have hfst : a = a' := obj_ext_of_isDiscrete f.fst
            have hsnd : b = b' := obj_ext_of_isDiscrete f.snd
            cases hfst
            cases hsnd
            have hleft : f.fst = 𝟙 _ := Subsingleton.elim _ _
            have hright : f.snd = 𝟙 _ := Subsingleton.elim _ _
            have hhom : i.hom = i'.hom := by
              simpa [hleft, hright] using f.w.symm
            have hiso : i = i' := by
              ext
              exact hhom
            cases hiso
            rfl

/-- Helper for Lemma 4.38.4: a morphism in the fibre of the explicit `2`-fibre product over `U`
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

/-- Helper for Lemma 4.38.4: a morphism in the fibre of the explicit `2`-fibre product over `U`
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

/-- Helper for Lemma 4.38.4: each fibre of the explicit `2`-fibre product projection is a
discrete category. -/
private theorem explicitTwoFibreProduct_fiber_isDiscrete
    (F : X ⟶ S) (G : Y ⟶ S) (U : C) :
    IsDiscrete ((explicitTwoFibreProductOver F G).p.Fiber U) := by
  refine
    { subsingleton := ?_
      eq_of_hom := ?_ }
  · -- Two fibre morphisms are equal once their left and right fibre components agree.
    intro P Q
    refine ⟨fun φ ψ ↦ ?_⟩
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
                      exact congrArg (fun f => f.1) (Subsingleton.elim φfst ψfst)
                    · let φsnd : Pobj.snd ⟶ Qobj.snd :=
                        ⟨φ.1.b, explicitTwoFibreProduct_fiber_right_over_id F G φ⟩
                      let ψsnd : Pobj.snd ⟶ Qobj.snd :=
                        ⟨ψ.1.b, explicitTwoFibreProduct_fiber_right_over_id F G ψ⟩
                      exact congrArg (fun f => f.1) (Subsingleton.elim φsnd ψsnd)
  · -- Any fibre morphism identifies the left and right fibre objects, and then the comparison
    -- isomorphism is forced by the pullback compatibility.
    intro P Q φ
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
                    cases Pobj with
                    | mk Pfst Psnd Piso =>
                        cases Qobj with
                        | mk Qfst Qsnd Qiso =>
                            have hfst : Pfst = Qfst := by
                              let φfst : Pfst ⟶ Qfst :=
                                ⟨φ.1.a, explicitTwoFibreProduct_fiber_left_over_id F G φ⟩
                              exact obj_ext_of_isDiscrete φfst
                            have hsnd : Psnd = Qsnd := by
                              let φsnd : Psnd ⟶ Qsnd :=
                                ⟨φ.1.b, explicitTwoFibreProduct_fiber_right_over_id F G φ⟩
                              exact obj_ext_of_isDiscrete φsnd
                            cases hfst
                            cases hsnd
                            have hleft : φ.1.a = 𝟙 _ := by
                              let φα : Pfst ⟶ Pfst :=
                                ⟨φ.1.a, explicitTwoFibreProduct_fiber_left_over_id F G φ⟩
                              exact congrArg (fun f => f.1) (Subsingleton.elim φα (𝟙 Pfst))
                            have hright : φ.1.b = 𝟙 _ := by
                              let φβ : Psnd ⟶ Psnd :=
                                ⟨φ.1.b, explicitTwoFibreProduct_fiber_right_over_id F G φ⟩
                              exact congrArg (fun f => f.1) (Subsingleton.elim φβ (𝟙 Psnd))
                            have hiso_hom : Piso.hom = Qiso.hom := by
                              apply Functor.Fiber.hom_ext
                              simpa [hleft, hright] using φ.1.comm.w.symm
                            have hiso : Piso = Qiso := by
                              ext
                              simpa using
                                congrArg (fun f ↦ Functor.Fiber.fiberInclusion.map f) hiso_hom
                            cases hiso
                            rfl

/-- Helper for Lemma 4.38.4: a morphism of categories fibred in sets over `C` sends a strongly
cartesian lift over a chosen base arrow to a strongly cartesian lift over the same base arrow. -/
private theorem map_stronglyCartesian_over_base
    {A B : FibredInSetsOver.{u, v, max u v, v} C} (H : A ⟶ B)
    {U V : C} {a b : A.S} {f : U ⟶ V} {φ : a ⟶ b}
    (hφ : A.p.IsStronglyCartesian f φ) :
    B.p.IsStronglyCartesian f ((FibredInSetsOver.G H).map φ) := by
  -- Rewrite the source lift to its actual base map so the ambient preservation theorem applies.
  have hφ' : A.p.IsStronglyCartesian (A.p.map φ) φ := by
    letI : A.p.IsStronglyCartesian f φ := hφ
    subst_hom_lift A.p f φ
    simpa using hφ
  have hmap :
      B.p.IsStronglyCartesian (B.p.map ((FibredInSetsOver.G H).map φ))
        ((FibredInSetsOver.G H).map φ) :=
    FibredCategoryMor.map_stronglyCartesian
      (F := FibredInGroupoidsMor.toFibredCategoryMor H.toHom) φ hφ'
  -- Transport the target lift back to the chosen base arrow `f`.
  have hLift : B.p.IsHomLift f ((FibredInSetsOver.G H).map φ) := by
    letI : A.p.IsHomLift f φ := hφ.toIsHomLift
    exact show B.p.IsHomLift f ((FibredInSetsOver.G H).map φ) from inferInstance
  letI : B.p.IsHomLift f ((FibredInSetsOver.G H).map φ) := hLift
  subst_hom_lift B.p f ((FibredInSetsOver.G H).map φ)
  simpa using hmap

/-- Helper for Lemma 4.38.4: if a morphism is strongly cartesian for one chosen lift of its base
arrow, then it is strongly cartesian for any other chosen lift of the same morphism. -/
private theorem isStronglyCartesian_rebase_of_same_lift
    {𝒮 : Type u} {𝒳 : Type u_1} [Category.{v} 𝒮] [Category.{v} 𝒳]
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

/-- Helper for Lemma 4.38.4: an external lift witness upgrades strong cartesianness back to the
owner-level base map of the same morphism. -/
private theorem isStronglyCartesian_of_external_hom_lift
    {𝒮 : Type u} {𝒳 : Type u_1} [Category.{v} 𝒮] [Category.{v} 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {R T : 𝒮} {a b : 𝒳} {f : R ⟶ T} (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] [p.IsHomLift f φ] :
    p.IsStronglyCartesian (p.map φ) φ := by
  -- Normalize the chosen source and target to the actual source and target of `φ`.
  have ha : p.obj a = R := IsHomLift.domain_eq p f φ
  have hb : p.obj b = T := IsHomLift.codomain_eq p f φ
  subst ha
  subst hb
  exact isStronglyCartesian_rebase_of_same_lift (p := p) (f := f) (f' := p.map φ) φ

/-- Helper for Lemma 4.38.4: the base projection of a morphism in the explicit pullback is its
stored `base` field. -/
private theorem explicitTwoFibreProduct_base_projection_map
    (F : X ⟶ S) (G : Y ⟶ S)
    {P Q : (explicitTwoFibreProductOver F G).obj}
    (φ : P ⟶ Q) :
    (explicitTwoFibreProductOver F G).p.map φ = φ.base := by
  rfl

/-- Helper for Lemma 4.38.4: a lift for the projection of the explicit pullback has base arrow
equal to the stored `base` field of the morphism. -/
private theorem explicitTwoFibreProduct_isHomLift_base_eq
    (F : X ⟶ S) (G : Y ⟶ S)
    {P Q : (explicitTwoFibreProductOver F G).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProductOver F G).p.IsHomLift f φ) :
    φ.base = f := by
  let p := (explicitTwoFibreProductOver F G).p
  have h : f = p.map φ := @IsHomLift.eq_of_isHomLift _ _ _ _ p _ _ f φ hφ
  simpa [p, explicitTwoFibreProduct_base_projection_map F G φ] using h.symm

/-- Helper for Lemma 4.38.4: a lift in the explicit pullback induces the corresponding lift on
the left component over the same base arrow. -/
private theorem explicitTwoFibreProduct_left_isHomLift_of_isHomLift
    (F : X ⟶ S) (G : Y ⟶ S)
    {P Q : (explicitTwoFibreProductOver F G).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProductOver F G).p.IsHomLift f φ) :
    X.p.IsHomLift f φ.a := by
  have hbase : φ.base = f := explicitTwoFibreProduct_isHomLift_base_eq F G φ hφ
  rw [← hbase]
  simpa using (φ.a_over : X.p.IsHomLift φ.base φ.a)

/-- Helper for Lemma 4.38.4: a lift in the explicit pullback induces the corresponding lift on
the right component over the same base arrow. -/
private theorem explicitTwoFibreProduct_right_isHomLift_of_isHomLift
    (F : X ⟶ S) (G : Y ⟶ S)
    {P Q : (explicitTwoFibreProductOver F G).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProductOver F G).p.IsHomLift f φ) :
    Y.p.IsHomLift f φ.b := by
  have hbase : φ.base = f := explicitTwoFibreProduct_isHomLift_base_eq F G φ hφ
  rw [← hbase]
  simpa using (φ.b_over : Y.p.IsHomLift φ.base φ.b)

/-- Helper for Lemma 4.38.4: a morphism in the explicit pullback is strongly cartesian whenever
its left and right components are strongly cartesian over the same base arrow. -/
private theorem explicitTwoFibreProduct_hom_isStronglyCartesian_of_components
    (F : X ⟶ S) (G : Y ⟶ S)
    {P Q : (explicitTwoFibreProductOver F G).obj}
    (φ : P ⟶ Q)
    (ha : X.p.IsStronglyCartesian φ.base φ.a)
    (hb : Y.p.IsStronglyCartesian φ.base φ.b) :
    (explicitTwoFibreProductOver F G).p.IsStronglyCartesian φ.base φ := by
  letI : X.p.IsStronglyCartesian φ.base φ.a := ha
  letI : Y.p.IsStronglyCartesian φ.base φ.b := hb
  refine
    { toIsHomLift := by
        change (explicitTwoFibreProductOver F G).p.IsHomLift
          ((explicitTwoFibreProductOver F G).p.map φ) φ
        infer_instance
      universal_property' := ?_ }
  intro R g ψ hψ
  letI : (explicitTwoFibreProductOver F G).p.IsHomLift (g ≫ φ.base) ψ := hψ
  have hψa : X.p.IsHomLift (g ≫ φ.base) ψ.a := by
    exact explicitTwoFibreProduct_left_isHomLift_of_isHomLift F G (f := g ≫ φ.base) ψ hψ
  have hψb : Y.p.IsHomLift (g ≫ φ.base) ψ.b := by
    exact explicitTwoFibreProduct_right_isHomLift_of_isHomLift F G (f := g ≫ φ.base) ψ hψ
  -- Factor the left and right components through the chosen strongly cartesian lifts.
  letI : X.p.IsHomLift (g ≫ φ.base) ψ.a := hψa
  obtain ⟨χa, hχa, hχa_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property X.p φ.base φ.a g (g ≫ φ.base) rfl ψ.a
  have hχa_over : X.p.IsHomLift g χa := hχa.1
  have hχa_fac : χa ≫ φ.a = ψ.a := hχa.2
  letI : Y.p.IsHomLift (g ≫ φ.base) ψ.b := hψb
  obtain ⟨χb, hχb, hχb_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property Y.p φ.base φ.b g (g ≫ φ.base) rfl ψ.b
  have hχb_over : Y.p.IsHomLift g χb := hχb.1
  have hχb_fac : χb ≫ φ.b = ψ.b := hχb.2
  have hmap_hb :
      S.p.IsStronglyCartesian φ.base ((FibredInSetsOver.G G).map φ.b) :=
    map_stronglyCartesian_over_base G hb
  letI : S.p.IsStronglyCartesian φ.base ((FibredInSetsOver.G G).map φ.b) := hmap_hb
  have hleft_over : S.p.IsHomLift g ((FibredInSetsOver.G F).map χa ≫ P.comparison) := by
    -- Map the left factorization into `S`, then append the vertical comparison of `P`.
    have hFχa : S.p.IsHomLift g ((FibredInSetsOver.G F).map χa) := by
      infer_instance
    letI : S.p.IsHomLift g ((FibredInSetsOver.G F).map χa) := hFχa
    letI : S.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
    exact
      IsHomLift.comp_lift_id_right' (p := S.p) g ((FibredInSetsOver.G F).map χa) P.U
        P.comparison
  have hright_over : S.p.IsHomLift g (R.comparison ≫ (FibredInSetsOver.G G).map χb) := by
    -- Do the same for the right factorization, now precomposing with the source comparison.
    have hGχb : S.p.IsHomLift g ((FibredInSetsOver.G G).map χb) := by
      infer_instance
    letI : S.p.IsHomLift g ((FibredInSetsOver.G G).map χb) := hGχb
    letI : S.p.IsHomLift (𝟙 R.U) R.comparison := R.comparison_over
    exact
      IsHomLift.comp_lift_id_left' (p := S.p) R.U R.comparison g
        ((FibredInSetsOver.G G).map χb)
  have hcomm_after_comp :
      ((FibredInSetsOver.G F).map χa ≫ P.comparison) ≫ (FibredInSetsOver.G G).map φ.b =
        (R.comparison ≫ (FibredInSetsOver.G G).map χb) ≫ (FibredInSetsOver.G G).map φ.b := by
    -- Both candidate comparison squares become the same after composing with `G.map φ.b`.
    calc
      ((FibredInSetsOver.G F).map χa ≫ P.comparison) ≫ (FibredInSetsOver.G G).map φ.b
          = (FibredInSetsOver.G F).map χa ≫
              ((FibredInSetsOver.G F).map φ.a ≫ Q.comparison) := by
              rw [φ.comm.w]
              simp [Category.assoc]
      _ = (FibredInSetsOver.G F).map (χa ≫ φ.a) ≫ Q.comparison := by
            simp [Functor.map_comp, Category.assoc]
      _ = (FibredInSetsOver.G F).map ψ.a ≫ Q.comparison := by
            rw [hχa_fac]
      _ = R.comparison ≫ (FibredInSetsOver.G G).map ψ.b := by
            exact ψ.comm.w
      _ = R.comparison ≫ (FibredInSetsOver.G G).map (χb ≫ φ.b) := by
            rw [hχb_fac]
      _ = (R.comparison ≫ (FibredInSetsOver.G G).map χb) ≫
            (FibredInSetsOver.G G).map φ.b := by
            simp [Functor.map_comp, Category.assoc]
  have hcomm :
      (FibredInSetsOver.G F).map χa ≫ P.comparison =
        R.comparison ≫ (FibredInSetsOver.G G).map χb := by
    -- Cancel the mapped strongly cartesian arrow `(G.map φ.b)`.
    apply
      Functor.IsStronglyCartesian.ext (p := S.p) (f := φ.base)
        ((FibredInSetsOver.G G).map φ.b) g
    simpa [Category.assoc] using hcomm_after_comp
  let χ : R ⟶ P :=
    { base := g
      a := χa
      a_over := hχa_over
      b := χb
      b_over := hχb_over
      comm := ⟨hcomm⟩ }
  refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
  · change (explicitTwoFibreProductOver F G).p.IsHomLift
      ((explicitTwoFibreProductOver F G).p.map χ) χ
    infer_instance
  · apply ExplicitTwoFibreProductHom.ext
    · simpa [χ] using hχa_fac
    · simpa [χ] using hχb_fac
  · intro χ' hχ'
    rcases hχ' with ⟨hχ'_over, hχ'_fac⟩
    letI : (explicitTwoFibreProductOver F G).p.IsHomLift g χ' := hχ'_over
    have hχ'a : X.p.IsHomLift g χ'.a := by
      exact explicitTwoFibreProduct_left_isHomLift_of_isHomLift F G (f := g) χ' hχ'_over
    have hχ'b : Y.p.IsHomLift g χ'.b := by
      exact explicitTwoFibreProduct_right_isHomLift_of_isHomLift F G (f := g) χ' hχ'_over
    -- Uniqueness is checked componentwise using the universal properties of `φ.a` and `φ.b`.
    apply ExplicitTwoFibreProductHom.ext
    · exact hχa_uniq χ'.a ⟨hχ'a, by simpa using congrArg ExplicitTwoFibreProductHom.a hχ'_fac⟩
    · exact hχb_uniq χ'.b ⟨hχ'b, by simpa using congrArg ExplicitTwoFibreProductHom.b hχ'_fac⟩

/-- Helper for Lemma 4.38.4: the comparison carried by an explicit pullback object is an
isomorphism in the total category of `S`. -/
private theorem explicitTwoFibreProduct_comparison_isIso
    (F : X ⟶ S) (G : Y ⟶ S)
    (P : (explicitTwoFibreProductOver F G).obj) :
    IsIso P.comparison := by
  let e : (FibredInSetsOver.G F).obj P.obj.fst.1 ≅ (FibredInSetsOver.G G).obj P.obj.snd.1 :=
    { hom := P.comparison
      inv := P.obj.iso.inv.1
      hom_inv_id := by
        exact congrArg Subtype.val P.obj.iso.hom_inv_id
      inv_hom_id := by
        exact congrArg Subtype.val P.obj.iso.inv_hom_id }
  exact ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- Helper for Lemma 4.38.4: the chosen pullback of the left component of `P` along `f`, viewed
as an object of the standard fiber of `X` over the new base. -/
private noncomputable def explicitTwoFibreProduct_left_pullback
    (F : X ⟶ S) (G : Y ⟶ S)
    (P : (explicitTwoFibreProductOver F G).obj)
    {V : C} (f : V ⟶ P.U) :
    X.p.Fiber V :=
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let a := HasFibers.pullbackMap (p := X.p) f P.obj.fst.2
  Functor.Fiber.mk (IsHomLift.domain_eq X.p f a)

/-- Helper for Lemma 4.38.4: the chosen pullback map of the left component of `P` along `f`. -/
private noncomputable def explicitTwoFibreProduct_left_pullback_map
    (F : X ⟶ S) (G : Y ⟶ S)
    (P : (explicitTwoFibreProductOver F G).obj)
    {V : C} (f : V ⟶ P.U) :
    (explicitTwoFibreProduct_left_pullback F G P f).1 ⟶ P.obj.fst.1 :=
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let a := HasFibers.pullbackMap (p := X.p) f P.obj.fst.2
  show (explicitTwoFibreProduct_left_pullback F G P f).1 ⟶ P.obj.fst.1 from a

/-- Helper for Lemma 4.38.4: the chosen pullback of the right component of `P` along `f`, viewed
as an object of the standard fiber of `Y` over the new base. -/
private noncomputable def explicitTwoFibreProduct_right_pullback
    (F : X ⟶ S) (G : Y ⟶ S)
    (P : (explicitTwoFibreProductOver F G).obj)
    {V : C} (f : V ⟶ P.U) :
    Y.p.Fiber V :=
  let _ : HasFibers Y.p := HasFibers.canonical Y.p
  let b := HasFibers.pullbackMap (p := Y.p) f P.obj.snd.2
  Functor.Fiber.mk (IsHomLift.domain_eq Y.p f b)

/-- Helper for Lemma 4.38.4: the chosen pullback map of the right component of `P` along `f`. -/
private noncomputable def explicitTwoFibreProduct_right_pullback_map
    (F : X ⟶ S) (G : Y ⟶ S)
    (P : (explicitTwoFibreProductOver F G).obj)
    {V : C} (f : V ⟶ P.U) :
    (explicitTwoFibreProduct_right_pullback F G P f).1 ⟶ P.obj.snd.1 :=
  let _ : HasFibers Y.p := HasFibers.canonical Y.p
  let b := HasFibers.pullbackMap (p := Y.p) f P.obj.snd.2
  show (explicitTwoFibreProduct_right_pullback F G P f).1 ⟶ P.obj.snd.1 from b

/-- Helper for Lemma 4.38.4: pulling back the two components of an explicit pullback object along
`f` produces the comparison isomorphism in the fiber of `S` over the new base. -/
private noncomputable def explicitTwoFibreProduct_pulledback_comparison_iso
    (F : X ⟶ S) (G : Y ⟶ S)
    (P : (explicitTwoFibreProductOver F G).obj)
    {V : C} (f : V ⟶ P.U) :
    ((FibredInSetsOver.toBasedFunctor F).fiberFunctor V).obj
        (explicitTwoFibreProduct_left_pullback F G P f) ≅
      ((FibredInSetsOver.toBasedFunctor G).fiberFunctor V).obj
        (explicitTwoFibreProduct_right_pullback F G P f) := by
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let _ : HasFibers Y.p := HasFibers.canonical Y.p
  let a := explicitTwoFibreProduct_left_pullback_map F G P f
  let b := explicitTwoFibreProduct_right_pullback_map F G P f
  -- The chosen pullback maps are strongly cartesian in `X` and `Y`.
  have ha_cart : X.p.IsCartesian f a := by
    change X.p.IsCartesian f (HasFibers.pullbackMap (p := X.p) f P.obj.fst.2)
    infer_instance
  have hb_cart : Y.p.IsCartesian f b := by
    change Y.p.IsCartesian f (HasFibers.pullbackMap (p := Y.p) f P.obj.snd.2)
    infer_instance
  have ha : X.p.IsStronglyCartesian f a :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f a
  have hb : Y.p.IsStronglyCartesian f b :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Y.p f b
  -- Map those strongly cartesian lifts into `S`.
  have hFa : S.p.IsStronglyCartesian f ((FibredInSetsOver.G F).map a) :=
    map_stronglyCartesian_over_base F ha
  have hGb : S.p.IsStronglyCartesian f ((FibredInSetsOver.G G).map b) :=
    map_stronglyCartesian_over_base G hb
  letI : IsIso P.comparison := explicitTwoFibreProduct_comparison_isIso F G P
  letI : S.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
  have hcomparison : S.p.IsStronglyCartesian (𝟙 P.U) P.comparison :=
    Functor.IsStronglyCartesian.of_isIso S.p (𝟙 P.U) P.comparison
  -- Compose `F.map a` with the vertical comparison of `P` to obtain a second lift over `f`.
  have hleft :
      S.p.IsStronglyCartesian f ((FibredInSetsOver.G F).map a ≫ P.comparison) := by
    letI : S.p.IsStronglyCartesian f ((FibredInSetsOver.G F).map a) := hFa
    letI : S.p.IsStronglyCartesian (𝟙 P.U) P.comparison := hcomparison
    simpa using
      (show S.p.IsStronglyCartesian (f ≫ 𝟙 P.U)
          ((FibredInSetsOver.G F).map a ≫ P.comparison) from inferInstance)
  letI : S.p.IsStronglyCartesian f ((FibredInSetsOver.G G).map b) := hGb
  letI : S.p.IsStronglyCartesian f ((FibredInSetsOver.G F).map a ≫ P.comparison) := hleft
  let e :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso
      S.p
      (g := Iso.refl V)
      (show f = (Iso.refl V).hom ≫ f by simp)
      ((FibredInSetsOver.G G).map b)
      ((FibredInSetsOver.G F).map a ≫ P.comparison)
  have hhom : S.p.IsHomLift (𝟙 V) e.hom := by
    simpa [e] using
      (show S.p.IsHomLift (Iso.refl V).hom e.hom from inferInstance)
  have hinv : S.p.IsHomLift (𝟙 V) e.inv := by
    simpa [e] using
      (show S.p.IsHomLift (Iso.refl V).inv e.inv from inferInstance)
  -- Package the domain comparison back into the standard fiber over `V`.
  refine
    { hom := Functor.Fiber.homMk S.p V e.hom
      inv := Functor.Fiber.homMk S.p V e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }

/-- Helper for Lemma 4.38.4: every base arrow into an explicit pullback object admits the
canonical pullback morphism obtained by pulling back each component in the two fibred
categories. -/
private theorem explicitTwoFibreProduct_exists_isStronglyCartesian
    (F : X ⟶ S) (G : Y ⟶ S)
    (P : (explicitTwoFibreProductOver F G).obj)
    {V : C} (f : V ⟶ P.U) :
    ∃ Q : (explicitTwoFibreProductOver F G).obj,
      ∃ η : Q ⟶ P,
        X.p.IsStronglyCartesian (X.p.map η.a) η.a ∧
          Y.p.IsStronglyCartesian (Y.p.map η.b) η.b ∧
            (explicitTwoFibreProductOver F G).p.IsStronglyCartesian f η := by
  let _ : HasFibers X.p := HasFibers.canonical X.p
  let _ : HasFibers Y.p := HasFibers.canonical Y.p
  let a := explicitTwoFibreProduct_left_pullback_map F G P f
  let b := explicitTwoFibreProduct_right_pullback_map F G P f
  -- Pull back the two components of `P` along `f`.
  let Q : (explicitTwoFibreProductOver F G).obj :=
    { U := V
      obj :=
        { fst := explicitTwoFibreProduct_left_pullback F G P f
          snd := explicitTwoFibreProduct_right_pullback F G P f
          iso := explicitTwoFibreProduct_pulledback_comparison_iso F G P f } }
  have ha_over : X.p.IsHomLift f a := by
    change X.p.IsHomLift f (HasFibers.pullbackMap (p := X.p) f P.obj.fst.2)
    infer_instance
  have hb_over : Y.p.IsHomLift f b := by
    change Y.p.IsHomLift f (HasFibers.pullbackMap (p := Y.p) f P.obj.snd.2)
    infer_instance
  have ha_cart : X.p.IsCartesian f a := by
    change X.p.IsCartesian f (HasFibers.pullbackMap (p := X.p) f P.obj.fst.2)
    infer_instance
  have hb_cart : Y.p.IsCartesian f b := by
    change Y.p.IsCartesian f (HasFibers.pullbackMap (p := Y.p) f P.obj.snd.2)
    infer_instance
  have ha : X.p.IsStronglyCartesian f a :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian X.p f a
  have hb : Y.p.IsStronglyCartesian f b :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Y.p f b
  have hFa : S.p.IsStronglyCartesian f ((FibredInSetsOver.G F).map a) :=
    map_stronglyCartesian_over_base F ha
  have hGb : S.p.IsStronglyCartesian f ((FibredInSetsOver.G G).map b) :=
    map_stronglyCartesian_over_base G hb
  letI : IsIso P.comparison := explicitTwoFibreProduct_comparison_isIso F G P
  letI : S.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
  have hcomparison : S.p.IsStronglyCartesian (𝟙 P.U) P.comparison :=
    Functor.IsStronglyCartesian.of_isIso S.p (𝟙 P.U) P.comparison
  have hleft :
      S.p.IsStronglyCartesian f ((FibredInSetsOver.G F).map a ≫ P.comparison) := by
    letI : S.p.IsStronglyCartesian f ((FibredInSetsOver.G F).map a) := hFa
    letI : S.p.IsStronglyCartesian (𝟙 P.U) P.comparison := hcomparison
    simpa using
      (show S.p.IsStronglyCartesian (f ≫ 𝟙 P.U)
          ((FibredInSetsOver.G F).map a ≫ P.comparison) from inferInstance)
  letI : S.p.IsStronglyCartesian f ((FibredInSetsOver.G G).map b) := hGb
  letI : S.p.IsStronglyCartesian f ((FibredInSetsOver.G F).map a ≫ P.comparison) := hleft
  have hf_refl : f = (Iso.refl V).hom ≫ f := by
    simp
  let e :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso
      S.p
      (g := Iso.refl V)
      hf_refl
      ((FibredInSetsOver.G G).map b)
      ((FibredInSetsOver.G F).map a ≫ P.comparison)
  have hfac :
      e.hom ≫ (FibredInSetsOver.G G).map b =
        (FibredInSetsOver.G F).map a ≫ P.comparison := by
    dsimp [e]
    exact
      (Functor.IsStronglyCartesian.fac
        S.p
        f
        ((FibredInSetsOver.G G).map b)
        hf_refl
        ((FibredInSetsOver.G F).map a ≫ P.comparison))
  have hcomm :
      CommSq
        ((FibredInSetsOver.G F).map a)
        Q.comparison
        P.comparison
        ((FibredInSetsOver.G G).map b) := by
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
  have hηa : X.p.IsStronglyCartesian (X.p.map η.a) η.a := by
    letI : X.p.IsStronglyCartesian f η.a := ha
    letI : X.p.IsHomLift f η.a := ha_over
    exact
      isStronglyCartesian_of_external_hom_lift
        (p := X.p) (R := V) (T := P.U) (f := f) η.a
  have hηb : Y.p.IsStronglyCartesian (Y.p.map η.b) η.b := by
    letI : Y.p.IsStronglyCartesian f η.b := hb
    letI : Y.p.IsHomLift f η.b := hb_over
    exact
      isStronglyCartesian_of_external_hom_lift
        (p := Y.p) (R := V) (T := P.U) (f := f) η.b
  have hη :
      (explicitTwoFibreProductOver F G).p.IsStronglyCartesian f η :=
    by
      simpa [η] using
        explicitTwoFibreProduct_hom_isStronglyCartesian_of_components F G η ha hb
  -- The canonical component pullbacks assemble to the desired strongly cartesian lift.
  exact ⟨Q, η, hηa, hηb, hη⟩

/-- Helper for Lemma 4.38.4: the explicit pullback projection is fibred once the two input legs
come from categories fibred in sets. -/
private theorem explicitTwoFibreProductProjection_isFibered
    (F : X ⟶ S) (G : Y ⟶ S) :
    (explicitTwoFibreProductOver F G).p.IsFibered := by
  -- Pull back both components of the target object and reassemble the comparison upstairs.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro P V f
  obtain ⟨Q, η, _, _, hη⟩ := explicitTwoFibreProduct_exists_isStronglyCartesian F G P f
  exact ⟨Q, η, hη⟩

/-- Helper for Lemma 4.38.4: a natural isomorphism between the underlying based functors of two
ambient morphisms of categories fibred in groupoids induces an isomorphism of those morphisms. -/
private noncomputable def fibredInGroupoidsIsoOfBasedFunctorIso
    {A B : FibredInGroupoidsOver C} {H K : A ⟶ B}
    (e : FibredInGroupoidsMor.toBasedFunctor H ≅ FibredInGroupoidsMor.toBasedFunctor K) :
    H ≅ K := by
  let e' : FibredInGroupoidsMor.toFibredCategoryMor H ≅
      FibredInGroupoidsMor.toFibredCategoryMor K :=
    CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial
  exact FibredInGroupoidsMor.ofFibredCategoryMorIso e'

/-- Helper for Lemma 4.38.4: a `2`-morphism in `FibredInGroupoidsOver C` forgets to a based
natural transformation between the underlying based functors. -/
private noncomputable def fibredInGroupoidsTwoHomToBasedNatTrans
    {A B : FibredInGroupoidsOver C} {H K : A ⟶ B}
    (η : H ⟶ K) :
    FibredInGroupoidsMor.toBasedFunctor H ⟶ FibredInGroupoidsMor.toBasedFunctor K := by
  simpa [FibredInGroupoidsMor.toBasedFunctor, FibredCategoryMor.toBasedFunctor] using
    η.hom.hom.hom.hom

/-- Helper for Lemma 4.38.4: a based natural transformation between ambient morphisms of
categories fibred in groupoids over `C` canonically lifts to a `2`-morphism. -/
private noncomputable def fibredInGroupoidsTwoHomOfBasedNatTrans
    {A B : FibredInGroupoidsOver C} {H K : A ⟶ B}
    (η : FibredInGroupoidsMor.toBasedFunctor H ⟶ FibredInGroupoidsMor.toBasedFunctor K) :
    H ⟶ K := by
  refine ⟨?_, trivial⟩
  refine ⟨?_, trivial⟩
  exact ⟨by
    simpa [FibredInGroupoidsMor.toBasedFunctor, FibredCategoryMor.toBasedFunctor] using η⟩

/-- Lemma 4.38.4: if `F : X ⟶ S` and `G : Y ⟶ S` are morphisms of categories fibred in sets over
`C`, then the explicit `2`-fibre-product projection from Lemma 4.32.3 is again fibred in sets
over `C`. Hence the `2`-category of categories fibred in sets over `C` has `2`-fibre products
described by the same construction. -/
theorem explicitTwoFibreProductProjection_isFibredInSets
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSets (explicitTwoFibreProductOver F G).p := by
  letI : (explicitTwoFibreProductOver F G).p.IsFibered :=
    explicitTwoFibreProductProjection_isFibered F G
  letI : ∀ U : C, IsDiscrete ((explicitTwoFibreProductOver F G).p.Fiber U) :=
    explicitTwoFibreProduct_fiber_isDiscrete F G
  infer_instance

/-- The explicit `2`-fibre-product projection carries the canonical fibred-in-sets structure. -/
instance (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSets (explicitTwoFibreProductOver F G).p :=
  explicitTwoFibreProductProjection_isFibredInSets F G

namespace FibredInSetsOver

open FibredInGroupoidsMor

/-- Helper for Lemma 4.38.4: the ambient fibred-in-groupoids pullback of `F` and `G`. -/
private noncomputable abbrev ambientTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    FibredInGroupoidsOver C :=
  FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom

/-- The ambient fibred-in-groupoids pullback also satisfies the fibred-in-sets condition. -/
-- Proof sketch: identify the projection of `FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom`
-- with the explicit pullback projection `explicitTwoFibreProductOver F G` and reuse
-- `explicitTwoFibreProductProjection_isFibredInSets`.
private theorem ambientTwoFibreProduct_isFibredInSets
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSets (ambientTwoFibreProduct F G).p := by
  change IsFibredInSets (explicitTwoFibreProductOver F G).p
  exact explicitTwoFibreProductProjection_isFibredInSets F G

/-- The canonical fibred `2`-fibre product of morphisms of categories fibred in sets over `C`. -/
noncomputable abbrev twoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    FibredInSetsOver C :=
  ⟨ambientTwoFibreProduct F G, ambientTwoFibreProduct_isFibredInSets F G⟩

/-- Restrict an ambient fibred-in-groupoids square to the full sub-`2`-category of categories
fibred in sets, once its apex is known to be fibred in sets. -/
private noncomputable abbrev ofFibredInGroupoidsSquare
    {F : X ⟶ S} {G : Y ⟶ S}
    (P : BicategoricalTwoCommutativeSquare F.toHom G.toHom)
    (hsets : IsFibredInSets P.obj.p) :
    BicategoricalTwoCommutativeSquare F G :=
  let T : FibredInSetsOver C := ⟨P.obj, hsets⟩
  let p : T ⟶ X := ofAmbientHom P.p
  let q : T ⟶ Y := ofAmbientHom P.q
  let ψ : p ≫ F ≅ q ≫ G := ofAmbientIso P.ψ
  { obj := T
    p := p
    q := q
    ψ := ψ }

/-- Helper for Lemma 4.38.4: forget a square in `FibredInSetsOver C` to the ambient square in
`FibredInGroupoidsOver C`. -/
private noncomputable abbrev toFibredInGroupoidsSquare
    {F : X ⟶ S} {G : Y ⟶ S}
    (P : BicategoricalTwoCommutativeSquare F G) :
    BicategoricalTwoCommutativeSquare F.toHom G.toHom where
  obj := P.obj.obj
  p := P.p.toHom
  q := P.q.toHom
  ψ :=
    Functor.mapIso (((fibredInSetsOverSubTwoCategory C).hom P.obj S).inclusion) P.ψ

/-- The canonical `2`-commutative square in `FibredInSetsOver C`, formed by the ambient
fibred-in-groupoids pullback square restricted to the full sub-`2`-category of categories
fibred in sets. -/
noncomputable def twoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F G :=
  ofFibredInGroupoidsSquare
    (FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom)
    (ambientTwoFibreProduct_isFibredInSets F G)

/-- Helper for Lemma 4.38.4: forget a morphism into the fibred-in-sets pullback square to the
ambient morphism into the fibred-in-groupoids pullback square. -/
private noncomputable abbrev toAmbientSquareHom
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : P ⟶ twoFibreProductSquare F G) :
    toFibredInGroupoidsSquare P ⟶ FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom where
  hom := u.hom.toHom
  left := u.left.hom.hom
  right := u.right.hom.hom
  comm := by
    -- Forget the owner square equation to the underlying ambient `2`-cells.
    exact congrArg (fun α ↦ α.hom.hom) u.comm

/-- Helper for Lemma 4.38.4: rewrap an ambient morphism into the fibred-in-groupoids pullback
square as a morphism into the owner fibred-in-sets pullback square. -/
private noncomputable abbrev ofAmbientSquareHom
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : toFibredInGroupoidsSquare P ⟶ FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom) :
    P ⟶ twoFibreProductSquare F G := by
  rcases u with ⟨hom, left, right, comm⟩
  refine
    { hom := ofAmbientHom hom
      left := ⟨ObjectProperty.homMk left, trivial⟩
      right := ⟨ObjectProperty.homMk right, trivial⟩
      comm := ?_ }
  -- Rebuild the owner square equation from the ambient equation by extensionality of the two
  -- wrapper layers on `2`-morphisms.
  unfold_projs
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  exact comm

/-- Helper for Lemma 4.38.4: forget a `2`-morphism between owner square morphisms to the
ambient `2`-morphism between the forgotten ambient square morphisms. -/
private noncomputable abbrev toAmbientSquareTwoHom
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : P ⟶ twoFibreProductSquare F G}
    (η : u ⟶ v) :
    toAmbientSquareHom u ⟶ toAmbientSquareHom v where
  hom := η.hom.hom.hom
  left_comm := by
    -- Forgeting the owner `2`-cell equality gives the ambient left compatibility.
    exact congrArg (fun α ↦ α.hom.hom) η.left_comm
  right_comm := by
    -- Forgeting the owner `2`-cell equality gives the ambient right compatibility.
    exact congrArg (fun α ↦ α.hom.hom) η.right_comm

/-- Helper for Lemma 4.38.4: repackage an ambient square `2`-morphism into the canonical ambient
pullback square as an owner-level `2`-morphism into the fibred-in-sets pullback square. -/
private noncomputable def owner_twoHom_of_ambient_square_twoHom
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    {u : P ⟶ twoFibreProductSquare F G}
    {v : toFibredInGroupoidsSquare P ⟶ FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom}
    (η : toAmbientSquareHom u ⟶ v) :
    u ⟶ ofAmbientSquareHom v := by
  refine
    { hom := ⟨ObjectProperty.homMk η.hom, trivial⟩
      left_comm := ?_
      right_comm := ?_ }
  · -- Strip the owner wrappers until only the ambient left compatibility remains.
    unfold_projs
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact η.left_comm
  · -- The right leg is identical after forgetting to the ambient square `2`-morphism.
    unfold_projs
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    exact η.right_comm

/-- Helper for Lemma 4.38.4: forgetting the reconstructed owner `2`-morphism recovers the
original ambient square `2`-morphism. -/
private theorem toAmbient_owner_twoHom_of_ambient_square_twoHom
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    {u : P ⟶ twoFibreProductSquare F G}
    {v : toFibredInGroupoidsSquare P ⟶ FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom}
    (η : toAmbientSquareHom u ⟶ v) :
    toAmbientSquareTwoHom (owner_twoHom_of_ambient_square_twoHom η) = η := by
  apply BicategoricalTwoCommutativeSquare.TwoHom.ext
  rfl

/-- Helper for Lemma 4.38.4: owner square `2`-morphisms into the canonical pullback square are
equal once their forgotten ambient square `2`-morphisms are equal. -/
private theorem owner_twoHom_eq_of_toAmbient_eq
    {F : X ⟶ S} {G : Y ⟶ S}
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : P ⟶ twoFibreProductSquare F G}
    {η θ : u ⟶ v}
    (h : toAmbientSquareTwoHom η = toAmbientSquareTwoHom θ) :
    η = θ := by
  -- Equality in the owner hom-category is detected on the underlying ambient apex `2`-cell.
  apply BicategoricalTwoCommutativeSquare.TwoHom.ext
  repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
  exact congrArg (fun ζ ↦ ζ.hom.hom.hom.hom.hom) h

/-- Helper for Lemma 4.38.4: for any competing square, the hom-category into the owner
fibred-in-sets pullback square has a terminal object obtained by transporting the ambient
terminal object from the fibred-in-groupoids pullback square. -/
private theorem square_hasTerminal
    {F : X ⟶ S} {G : Y ⟶ S}
    (P : BicategoricalTwoCommutativeSquare F G) :
    Limits.HasTerminal (P ⟶ twoFibreProductSquare F G) := by
  let Q := toFibredInGroupoidsSquare P
  let T : BicategoricalTwoCommutativeSquare F.toHom G.toHom :=
    FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom
  letI : Bicategory.IsFinal T := FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct F.toHom G.toHom
  let targetAmbient : Q ⟶ T := ⊤_ (Q ⟶ T)
  let targetOwner : P ⟶ twoFibreProductSquare F G := ofAmbientSquareHom targetAmbient
  let htarget : Limits.IsTerminal targetAmbient := Limits.terminalIsTerminal
  -- Route correction: rebuild only the ambient terminal arrow upstairs, and prove uniqueness by
  -- forgetting any owner `2`-morphism back to the ambient terminal square-hom category.
  exact
    (Limits.IsTerminal.ofUniqueHom (Y := targetOwner)
      (fun u ↦ owner_twoHom_of_ambient_square_twoHom
        (Limits.terminal.from (toAmbientSquareHom u)))
      (fun u η ↦ by
        have htargetOwner :
            toAmbientSquareTwoHom
                (owner_twoHom_of_ambient_square_twoHom
                  (Limits.terminal.from (toAmbientSquareHom u))) =
              Limits.terminal.from (toAmbientSquareHom u) :=
          toAmbient_owner_twoHom_of_ambient_square_twoHom
            (Limits.terminal.from (toAmbientSquareHom u))
        have hηambient :
            toAmbientSquareTwoHom η = Limits.terminal.from (toAmbientSquareHom u) :=
          htarget.hom_ext _ _
        exact owner_twoHom_eq_of_toAmbient_eq (hηambient.trans htargetOwner.symm))).hasTerminal

/-- The canonical square `twoFibreProductSquare F G` is a bicategorical `2`-fibre product in
`FibredInSetsOver C`. -/
theorem twoFibreProduct_isTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) := by
  -- Route correction: abandon the based-category transport layer and instead restrict the already
  -- final ambient fibred-in-groupoids pullback square along the full sub-`2`-category inclusion.
  refine ⟨fun P ↦ ?_⟩
  exact square_hasTerminal P

end FibredInSetsOver

end CategoryTheory

/-! ### Example_4_38_5 (from Chap04) -/
universe w v u

namespace CategoryTheory

open CategoryOfElements Opposite Functor
open Functor.Fiber

/- Domain-style sampling for Example 4.38.5:
- primary domain: categories fibred in sets coming from the category-of-elements construction for
  a `Type`-valued presheaf.
- inspected owner-level declarations:
  `CategoryOfElements.π`,
  `FibredInSetsOver.ofFunctor`,
  `IsFibredInSets`.
- best owner abstraction: the source-facing theorem is the fibred-in-sets instance on the
  canonical projection `((π F).leftOp)`, while the natural downstream owner object is the bundled
  category `FibredInSetsOver C`.
- primitive data: the category-of-elements projection `((π F).leftOp)`.
- derived API: the fibred-in-sets instance; the bundled object is obtained directly via
  `FibredInSetsOver.ofFunctor ((π F).leftOp)`.

Source/core/bridge triage:
- `source-facing`: `presheaf_categoryOfElementsProjection_isFibredInSets`.
- `core/canonical`: `IsFibredInSets ((π F).leftOp)`.
- `bridge/view`: direct bundling by `FibredInSetsOver.ofFunctor ((π F).leftOp)`. -/

section

variable {C : Type u} [Category.{v} C]

-- Proof sketch: identify the textbook category `\mathcal S_F` with `F.Elementsᵒᵖ`; cartesian
-- lifts are induced by pullback along morphisms in the base, and each fiber is discrete because a
-- morphism over an identity is determined by equality of the corresponding elements.

private abbrev presheafCategoryOfElementsObj
    (F : Presheaf.{w} C) {U : C} (a : F.obj (op U)) :
    F.Elementsᵒᵖ :=
  op ⟨op U, a⟩

private abbrev presheafCategoryOfElementsPullbackObj
    (F : Presheaf.{w} C) {U V : C} (f : V ⟶ U) (a : F.obj (op U)) : F.Elementsᵒᵖ :=
  op ⟨op V, F.map f.op a⟩

private abbrev presheafCategoryOfElementsPullbackHom
    (F : Presheaf.{w} C) {U V : C} (f : V ⟶ U) (a : F.obj (op U)) :
    presheafCategoryOfElementsPullbackObj F f a ⟶ presheafCategoryOfElementsObj F a :=
  Quiver.Hom.op <| homMk _ _ f.op rfl

private theorem presheafCategoryOfElementsPullbackHom_isHomLift
    (F : Presheaf.{w} C) {U V : C} (f : V ⟶ U) (a : F.obj (op U)) :
    IsHomLift ((π F).leftOp) f
      (presheafCategoryOfElementsPullbackHom F f a) := by
  refine IsHomLift.of_fac' ((π F).leftOp) f _ rfl rfl ?_
  simp [presheafCategoryOfElementsPullbackHom]

private theorem presheafCategoryOfElementsPullbackHom_isStronglyCartesian
    (F : Presheaf.{w} C) {U V : C} (f : V ⟶ U) (a : F.obj (op U)) :
    IsStronglyCartesian ((π F).leftOp) f
      (presheafCategoryOfElementsPullbackHom F f a) := by
  refine
    { toIsHomLift := presheafCategoryOfElementsPullbackHom_isHomLift F f a
      universal_property' := ?_ }
  intro a' g φ' hφ'
  let hgf : ((π F).leftOp).obj a' ⟶ U := g ≫ f
  have hComp : hgf = ((π F).leftOp).map φ' :=
    @IsHomLift.eq_of_isHomLift _ _ _ _ ((π F).leftOp) _ _ hgf φ' hφ'
  have hVal : φ'.unop.val = f.op ≫ g.op := by
    simpa [hgf] using congrArg Quiver.Hom.op hComp.symm
  refine ⟨Quiver.Hom.op (homMk _ _ g.op ?_), ⟨?_, ?_⟩, ?_⟩
  · simpa [FunctorToTypes.map_comp_apply, hVal] using φ'.unop.property
  · refine IsHomLift.of_fac' ((π F).leftOp) g _ rfl rfl ?_
    simp
  · exact Quiver.Hom.unop_inj <| ext F _ _ <| by
      simpa [presheafCategoryOfElementsPullbackHom] using hVal.symm
  · intro ψ hψ
    exact Quiver.Hom.unop_inj <| ext F _ _ <| by
      have hBase : g = ((π F).leftOp).map ψ :=
        @IsHomLift.eq_of_isHomLift _ _ _ _ ((π F).leftOp) _ _ g ψ hψ.1
      simpa using congrArg Quiver.Hom.op hBase.symm

private theorem presheafCategoryOfElementsFiber_unop_val
    (F : Presheaf.{w} C) {U : C} {x y : ((π F).leftOp).Fiber U}
    (φ : x ⟶ y) :
    (fiberInclusion.map φ).unop.val =
      eqToHom ((congrArg Opposite.op y.2).trans (congrArg Opposite.op x.2).symm) := by
  have hFac :=
    @IsHomLift.fac' _ _ _ _ ((π F).leftOp) _ _ _ _ (𝟙 U)
      (fiberInclusion.map φ) φ.2
  simp at hFac
  simpa using congrArg Quiver.Hom.op hFac

/-- Example 4.38.5: for a presheaf of sets `F : Presheaf.{w} C`, the opposite category of elements
`F.Elementsᵒᵖ` with its canonical projection to `𝒞` is a category fibred in sets. This is the
mathlib-facing form of the textbook construction of `\mathcal S_F`. -/
theorem presheaf_categoryOfElementsProjection_isFibredInSets
    (F : Presheaf.{w} C) :
    IsFibredInSets ((π F).leftOp) := by
  letI : ((π F).leftOp).IsFibered := by
    refine IsFibered.of_exists_isStronglyCartesian ?_
    intro x V f
    refine ⟨presheafCategoryOfElementsPullbackObj F f x.unop.2,
      presheafCategoryOfElementsPullbackHom F f x.unop.2,
      presheafCategoryOfElementsPullbackHom_isStronglyCartesian F f x.unop.2⟩
  letI (U : C) : IsDiscrete (((π F).leftOp).Fiber U) := by
    refine
      { subsingleton := ?_
        eq_of_hom := ?_ }
    · intro x y
      constructor
      intro φ ψ
      apply hom_ext
      exact Quiver.Hom.unop_inj <| ext F _ _ <| by
        simp [presheafCategoryOfElementsFiber_unop_val F φ,
          presheafCategoryOfElementsFiber_unop_val F ψ]
    · intro x y φ
      apply fiberInclusion_obj_inj
      change x.1 = y.1
      apply congrArg Opposite.op
      symm
      refine Elements.ext _ _ ?_ ?_
      · exact (congrArg Opposite.op y.2).trans (congrArg Opposite.op x.2).symm
      · simpa [presheafCategoryOfElementsFiber_unop_val F φ] using
          (fiberInclusion.map φ).unop.property
  infer_instance

instance (F : Presheaf.{w} C) :
    IsFibredInSets ((π F).leftOp) :=
  presheaf_categoryOfElementsProjection_isFibredInSets F

end

end CategoryTheory
