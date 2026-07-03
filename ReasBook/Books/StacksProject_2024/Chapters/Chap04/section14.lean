import Mathlib
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_14_1 (from Chap04) -/
universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Limits

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C]
variable {M : J ⥤ C} {c : Cone M}

/- Domain-style sampling for Definition 4.14.1:
- primary domain: limits of a diagram in category theory.
- inspected owner declarations:
  `IsLimit`,
  `Cone`,
  `HasLimit`,
  `limit.cone`,
  `limit.isLimit`,
  `IsLimit.existsUnique`,
  `IsLimit.ofExistsUnique`.
- best owner abstraction: the textbook notion that a cone on `M` is limiting is already the
  canonical owner predicate `IsLimit`.
- primitive data: a cone `Cone M`.
- derived API: the existence typeclass `HasLimit M`, the chosen limit object `limit M`, the
  projections `limit.π`, the chosen cone `limit.cone M`, the proof that it is limiting
  `limit.isLimit M`, and the universal-property constructor/recognition theorems
  `IsLimit.existsUnique` and `IsLimit.ofExistsUnique`.

Source/core/bridge triage:
- `source-facing`: the textbook predicate that a cone on `M` is a limit cone.
- `core/canonical`: `IsLimit`.
- `bridge/view`: `HasLimit`, `limit`, `limit.π`, `limit.cone`, `limit.isLimit`,
  `IsLimit.existsUnique`, and `IsLimit.ofExistsUnique`. -/

/- Definition 4.14.1: for a diagram `M : J ⥤ C`, the textbook notion that a cone `c : Cone M` is
a limit cone is exactly the canonical owner predicate `IsLimit c`. -/
#check IsLimit c

/- Companion recall: the textbook source data of an object equipped with morphisms to `M.obj i` is
packaged by the canonical cone structure `Cone`. -/
recall Cone

/- Companion recall: existence of a chosen limit for a diagram is expressed by the canonical
typeclass `HasLimit`. -/
recall HasLimit

/- Companion recall: the textbook chosen limit object `lim_I M` is the canonical owner `limit`,
with projections `limit.π`. -/
section

variable [HasLimit M]
recall limit
recall limit.π

/- Companion recall: the canonical chosen limiting cone is `limit.cone M`, and it is limiting by
`limit.isLimit M`. -/
recall limit.cone
recall limit.isLimit

end

/- Companion recall: the unique-factorization clause in the textbook definition is the canonical
theorem `IsLimit.existsUnique`. -/
recall IsLimit.existsUnique

/- Companion recall: the converse direction from the textbook universal property to a limiting
cone is the canonical constructor `IsLimit.ofExistsUnique`. -/
recall IsLimit.ofExistsUnique

end CategoryTheory.Limits

/-! ### Definition_4_14_2 (from Chap04) -/
universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Limits

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C]
variable {M : J ⥤ C} {c : Cocone M}

/- Domain-style sampling for Definition 4.14.2:
- primary domain: colimits of a diagram in category theory.
- inspected owner declarations:
  `IsColimit`,
  `Cocone`,
  `HasColimit`,
  `colimit.cocone`,
  `colimit.isColimit`,
  `IsColimit.existsUnique`,
  `IsColimit.ofExistsUnique`.
- best owner abstraction: the textbook notion that a cocone on `M` is colimiting is already the
  canonical owner witness `IsColimit`.
- primitive data: a cocone `Cocone M`.
- derived API: the existence typeclass `HasColimit M`, the chosen colimit object `colimit M`, the
  coprojections `colimit.ι`, the chosen cocone `colimit.cocone M`, the proof that it is
  colimiting `colimit.isColimit M`, and the universal-property constructor/recognition theorems
  `IsColimit.existsUnique` and `IsColimit.ofExistsUnique`.

Source/core/bridge triage:
- `source-facing`: the textbook notion that a cocone on `M` is a colimit cocone.
- `core/canonical`: the witness `IsColimit`.
- `bridge/view`: `HasColimit`, `colimit`, `colimit.ι`, `colimit.cocone`, `colimit.isColimit`,
  `IsColimit.existsUnique`, and `IsColimit.ofExistsUnique`. -/

/- Definition 4.14.2: for a diagram `M : J ⥤ C`, the textbook notion that a cocone `c : Cocone M`
is a colimit cocone is exactly the canonical owner witness `IsColimit c`. -/
#check IsColimit c

/- Companion recall: the textbook source data of an object equipped with morphisms from each
`M.obj i` is packaged by the cocone structure `Cocone M`. -/
#check Cocone M

/- Companion recall: existence of a chosen colimit for `M` is expressed by `HasColimit M`. -/
#check HasColimit M

section

variable [HasColimit M]

/- Companion recall: under `[HasColimit M]`, the textbook object `colim_I M` is the canonical
chosen colimit object `colimit M`, with coprojections `colimit.ι`. -/
#check (colimit M : C)
recall colimit.ι

/- Companion recall: the canonical chosen colimiting cocone is `colimit.cocone M`, and it is
colimiting by `colimit.isColimit M`. -/
#check (colimit.cocone M : Cocone M)
recall colimit.isColimit

end

/- Companion recall: the unique-factorization clause in the textbook definition is the canonical
theorem `IsColimit.existsUnique`. -/
recall IsColimit.existsUnique

/- Companion recall: the converse direction is the canonical constructor
`IsColimit.ofExistsUnique`. -/
recall IsColimit.ofExistsUnique

end CategoryTheory.Limits

/-! ### Remark_4_14_3 (from Chap04) -/
namespace CategoryTheory

/-
Domain-style sampling for Remark 4.14.3:
- primary domain: category-theoretic size conventions for diagram shapes in limits and colimits
- sampled canonical declarations:
  `SmallCategory`,
  `HasLimitsOfShape`,
  `HasColimitsOfShape`
- best owner abstraction: `SmallCategory`; the limit/colimit classes consume the small indexing
  category rather than replacing it with a new owner
- primitive data: the small category structure on the indexing type
- derived API: the shape-indexed limit and colimit classes

Source/core/bridge triage:
- source-facing: the textbook convention that the indexing category for a limit or colimit is
  small
- core/canonical: `SmallCategory`
- bridge/view: `HasLimitsOfShape` and `HasColimitsOfShape` as downstream users of the size
  convention, not new abstractions for it
-/
/- Remark 4.14.3: the size convention on indexing categories for limits and colimits is the
canonical category structure abbreviation `SmallCategory`. -/
recall SmallCategory

end CategoryTheory

/-! ### Remark_4_14_4 (from Chap04) -/
universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Limits

variable {I : Type u₁} [Category.{v₁} I]
variable {C : Type u₂} [Category.{v₂} C]

/- Domain-style sampling for Remark 4.14.4:
- `limit.homIso'` and `colimit.homIso'` are the canonical owner equivalences for the Hom-formulas
  of limits and colimits.
- `limit.existsUnique` and `colimit.existsUnique` are the canonical unique-factorization theorems
  for compatible component families.
- `Yoneda.ext` and `Coyoneda.ext` are the extensionality owners expressing that the Hom-formulas
  determine the limit or colimit object up to unique isomorphism.

Primitive-vs-derived split:
- primitive data: a diagram `M` together with a compatible family of component morphisms into or
  out of `M.obj i`.
- derived API: the induced morphism, its uniqueness, and the resulting objectwise uniqueness up to
  isomorphism.

Source/core/bridge triage for Remark 4.14.4:
- `source-facing`: the textbook Hom-formulas for limits and colimits, together with the remark
  that they determine the universal object uniquely.
- `core/canonical`: `limit.homIso'` and `colimit.homIso'`.
- `bridge/view`: `limit.existsUnique`, `colimit.existsUnique`, `Yoneda.ext`, and
  `Coyoneda.ext`. -/

/- Remark 4.14.4(1): the limit side of the Hom-formula is the canonical componentwise
universal-property equivalence `limit.homIso'`, identifying maps `W ⟶ limit M` with compatible
families `p_i : W ⟶ M.obj i`.
-/
recall limit.homIso'

/- Companion recall: the source unique-factorization formulation for a compatible family
`p_i : W ⟶ M.obj i` is the canonical theorem `limit.existsUnique`, after packaging that family as a
cone on `M` with cone point `W`. -/
recall limit.existsUnique

/- Remark 4.14.4(2): the colimit side of the Hom-formula is the canonical componentwise
universal-property equivalence `colimit.homIso'`, identifying maps `colimit M ⟶ W` with
compatible families `p_i : M.obj i ⟶ W`.
-/
recall colimit.homIso'

/- Companion recall: the source unique-factorization formulation for a compatible family
`p_i : M.obj i ⟶ W` is the canonical theorem `colimit.existsUnique`, after packaging that family
as a cocone on `M` with cocone point `W`. -/
recall colimit.existsUnique

/- Companion recall: the Hom-formula for limits determines the limit object up to unique
isomorphism by the Yoneda lemma, via `Yoneda.ext`. -/
recall Yoneda.ext

/- Companion recall: the Hom-formula for colimits determines the colimit object up to unique
isomorphism by the dual Yoneda lemma, via `Coyoneda.ext`. -/
recall Coyoneda.ext

end CategoryTheory.Limits

/-! ### Remark_4_14_5 (from Chap04) -/
universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Limits

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C]
variable {F : J ⥤ C}

/- Domain-style sampling for Remark 4.14.5:
- primary domain: cone and cocone categories as the owner categories for limit and colimit
  universal properties.
- sampled canonical declarations:
  `Cone`,
  `Cone.isLimitEquivIsTerminal`,
  `hasLimit_iff_hasTerminal_cone`,
  `Cocone.isColimitEquivIsInitial`,
  `hasColimit_iff_hasInitial_cocone`.
- best owner abstraction: the cone category `Cone F` and the cocone category `Cocone F`.
- primitive data: the cone and cocone structures, together with their canonical category
  instances.
- derived API: the equivalences from `IsLimit` to `IsTerminal` and from `IsColimit` to
  `IsInitial`, plus the corresponding existence-level reformulations.

Source/core/bridge triage:
- `source-facing`: the textbook remark that a limit cone is exactly a terminal object in the
  category of cones, and dually that a colimit cocone is exactly an initial object in the category
  of cocones.
- `core/canonical`: the owner categories `Cone F` and `Cocone F`.
- `bridge/view`: `Cone.isLimitEquivIsTerminal`, `hasLimit_iff_hasTerminal_cone`,
  `Cocone.isColimitEquivIsInitial`, and `hasColimit_iff_hasInitial_cocone`. -/

/- Companion recall: a cone on a diagram `F : J ⥤ C` is the canonical mathlib structure `Cone F`,
consisting of an object together with a compatible family of maps to the objects of the diagram. -/
recall Cone

/- Companion recall: cones on a fixed diagram form a category via the canonical instance
`Cone.category`. -/
recall Cone.category

/- Remark 4.14.5, canonical limit-side formulation: for a fixed cone `c : Cone F`, the data of
`IsLimit c` is canonically equivalent to `IsTerminal c` in the category of cones on `F`. -/
recall Cone.isLimitEquivIsTerminal

/- Companion recall: the existence-level limit reformulation is the canonical theorem
`hasLimit_iff_hasTerminal_cone`. -/
recall hasLimit_iff_hasTerminal_cone

/- Companion recall: a cocone on a diagram `F : J ⥤ C` is the canonical mathlib structure
`Cocone F`, consisting of an object together with a compatible family of maps from the objects of
the diagram. -/
recall Cocone

/- Companion recall: cocones on a fixed diagram form a category via the canonical instance
`Cocone.category`. -/
recall Cocone.category

/- Remark 4.14.5, canonical colimit-side formulation: for a fixed cocone `c : Cocone F`, the data
of `IsColimit c` is canonically equivalent to `IsInitial c` in the category of cocones on `F`. -/
recall Cocone.isColimitEquivIsInitial

/- Companion recall: the existence-level colimit reformulation is the canonical theorem
`hasColimit_iff_hasInitial_cocone`. -/
recall hasColimit_iff_hasInitial_cocone

end CategoryTheory.Limits

/-! ### Definition_4_14_6 (from Chap04) -/
universe w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {I : Type w} (M : I → C)

/- Domain-style sampling for Definition 4.14.6:
- `piObj` is the owner abstraction for the product object of a family `M : I → C`.
- `HasProduct` is the canonical existence class for that product.
- `Pi.π` is the derived canonical family of product projections.

Primitive-vs-derived split:
- primitive data: none in this file; the product is already owned upstream as the limit object of
  `Discrete.functor M`.
- derived API: the existence predicate `HasProduct M` and the projections `Pi.π M`. -/

/- Source/core/bridge triage for Definition 4.14.6:
- `source-facing`: the textbook product of a family.
- `core/canonical`: `piObj`.
- `bridge/view`: the discrete-diagram presentation `limit (Discrete.functor M)`, already built
  into the owner. -/

/- Companion recall: existence of the product of the family `M` is expressed by the canonical
typeclass `HasProduct M`. -/
recall HasProduct

section

variable [HasProduct M]

/- Definition 4.14.6: for a family `M : I → C`, the product is the canonical mathlib object
`∏ᶜ M`, i.e. `piObj M = limit (Discrete.functor M)` in the discrete-diagram presentation. -/
#check (∏ᶜ M : C)

/- Companion recall: the core owner declaration for the product object `∏ᶜ M` is `piObj`. -/
recall piObj

/- Companion recall: the product projections from the family members into `∏ᶜ M` are the canonical
morphisms `Pi.π`. -/
recall Pi.π

end

end CategoryTheory.Limits

/-! ### Definition_4_14_7 (from Chap04) -/
universe w v u

namespace CategoryTheory.Limits

variable {I : Type w}
variable {C : Type u} [Category.{v} C]
variable (M : I → C)

/- Domain-style sampling for Definition 4.14.7:
- primary domain: categorical coproducts as colimits of discrete diagrams.
- sampled owner abstractions in `Mathlib.CategoryTheory.Limits.Shapes.Products`:
  `Cofan`, `HasCoproduct`, `sigmaObj`, `Sigma.ι`.

Primitive-vs-derived split:
- primitive data in the domain: a cofan together with its colimit universal property.
- primitive data in this file: none; the coproduct owner is already supplied upstream by
  `sigmaObj M = colimit (Discrete.functor M)`.
- derived API: the existence predicate `HasCoproduct M` and the canonical coproduct injections
  `Sigma.ι M`. -/

/- Source/core/bridge triage for Definition 4.14.7:
- `source-facing`: the textbook coproduct of a family.
- `core/canonical`: `sigmaObj`.
- `bridge/view`: the discrete-diagram presentation `colimit (Discrete.functor M)`, already built
  into the owner. -/

/- Companion recall: existence of the coproduct of the family `M` is expressed by the canonical
typeclass `HasCoproduct M`. -/
recall HasCoproduct

section

variable [HasCoproduct M]

/- Definition 4.14.7: for a family `M : I → C`, the coproduct is the canonical mathlib object
`∐ M`, i.e. `sigmaObj M = colimit (Discrete.functor M)` in the discrete-diagram presentation. -/
#check (∐ M : C)

/- Companion recall: the core owner declaration for the coproduct object `∐ M` is `sigmaObj`. -/
recall sigmaObj

/- Companion recall: the coproduct injections from the family members into `∐ M` are the canonical
morphisms `Sigma.ι`. -/
recall Sigma.ι

end

end CategoryTheory.Limits

/-! ### Lemma_4_14_8 (from Chap04) -/
universe v₁ v₂ v u₁ u₂ u

open CategoryTheory

namespace CategoryTheory.Limits

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u} [Category.{v} C]
variable {M : I ⥤ C} [HasColimit M]
variable {N : J ⥤ C} [HasColimit N]
variable {H : I ⥤ J}

/- Domain-style sampling for Lemma 4.14.8:
- primary domain: category theory of colimits.
- sampled canonical owner abstractions: `Cocone.whisker`, `Cocone.precompose`,
  `colimit.desc`, `colimit.existsUnique`.
- source/core/bridge triage:
  - source-facing: the comparison morphism `colimit M ⟶ colimit N` induced by
    `t : M ⟶ H ⋙ N`;
  - core/canonical: the cocone on `M` obtained by precomposing
    `((colimit.cocone N).whisker H)` along `t`;
  - bridge: the textbook existence-and-uniqueness statement is exactly the
    specialization of `colimit.existsUnique` to that induced cocone. -/

/- Lemma 4.14.8: a natural transformation `t : M ⟶ H ⋙ N` induces a unique
morphism from `colimit M` to `colimit N` whose composites with the colimit legs
agree with `t` componentwise. -/
#check
  (show ∀ t : M ⟶ H ⋙ N, ∃! θ : colimit M ⟶ colimit N,
      ∀ i : I, colimit.ι M i ≫ θ = t.app i ≫ colimit.ι N (H.obj i) from
    fun t ↦ by
      simpa using
        colimit.existsUnique ((Cocone.precompose t).obj ((colimit.cocone N).whisker H)))

end CategoryTheory.Limits

/-! ### Lemma_4_14_9 (from Chap04) -/
open CategoryTheory

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Limits

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₃} [Category.{v₃} C]

variable {M : I ⥤ C} [HasLimit M] {N : J ⥤ C} [HasLimit N] {H : I ⥤ J}

/-- The comparison morphism from `limit N` to `limit M` induced by precomposing the limit cone
of `N` along `H` and postcomposing with `t`. -/
noncomputable def limitComparison (t : H ⋙ N ⟶ M) : limit N ⟶ limit M :=
  limit.lift M ((Cone.postcompose t).obj ((limit.cone N).whisker H))

-- Proof sketch: apply `limit.lift_π` to the cone on `M` obtained by whiskering `limit.cone N`
-- along `H` and postcomposing with `t`.
/-- The comparison morphism induced by `t` commutes with the limit projections. -/
theorem limitComparison_π (t : H ⋙ N ⟶ M) (i : I) :
    limitComparison t ≫ limit.π M i = limit.π N (H.obj i) ≫ t.app i := by
  -- The comparison map is the universal lift from the induced cone on `M`.
  unfold limitComparison
  -- The `i`-th leg of that cone is definitionally the required composite.
  simpa using limit.lift_π ((Cone.postcompose t).obj ((limit.cone N).whisker H)) i

-- Proof sketch: apply `limit.existsUnique` to the cone on `M` with vertex `limit N` obtained by
-- whiskering `limit.cone N` along `H` and postcomposing with `t`.
/-- Lemma 4.14.9: a natural transformation `t : H ⋙ N ⟶ M` induces a unique morphism from
`limit N` to `limit M` whose composites with the projections are `t.app i`. -/
theorem limitComparison_existsUnique (t : H ⋙ N ⟶ M) :
    ∃! θ : limit N ⟶ limit M,
      ∀ i : I, θ ≫ limit.π M i = limit.π N (H.obj i) ≫ t.app i := by
  -- The source-faithful route is to apply the universal property to the induced cone on `M`.
  simpa [limitComparison] using
    (limit.existsUnique ((Cone.postcompose t).obj ((limit.cone N).whisker H)))

end CategoryTheory.Limits

/-! ### Lemma_4_14_10 (from Chap04) -/
universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits

open CategoryTheory Functor

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₃} [Category.{v₃} C]

/- Domain-style sampling for Lemma 4.14.10:
- primary domain: categorical Fubini theorems for limits and colimits of bifunctors.
- sampled owner abstractions in `Mathlib.CategoryTheory.Limits.Fubini`:
  `DiagramOfCocones` / `DiagramOfCones`,
  `DiagramOfCocones.coconePoints` / `DiagramOfCones.conePoints`,
  `coconeOfCoconeUncurryIsColimit` / `coneOfConeUncurryIsLimit`,
  `DiagramOfCocones.mkOfHasColimits` / `DiagramOfCones.mkOfHasLimits`,
  `colimitIsoColimitCurryCompColim` / `limitIsoLimitCurryCompLim`.

Primitive-vs-derived split:
- primitive data: a chosen diagram `D : DiagramOfCocones (curry.obj M)` or
  `D : DiagramOfCones (curry.obj M)` together with the rowwise `IsColimit` / `IsLimit`
  witnesses `∀ i, IsColimit (D.obj i)` or `∀ i, IsLimit (D.obj i)`.
- derived API: the induced source-facing functors `D.coconePoints` and `D.conePoints`, the
  existence equivalences below, the rowwise coincidence isomorphisms for colimits and limits, and
  the canonical `⋙ colim` / `⋙ lim` specializations under stronger global assumptions.

Source/core/bridge triage:
- `source-facing`: a chosen rowwise colimit system for one bifunctor and the resulting functor of
  cocone points; dually, a chosen rowwise limit system and the resulting functor of cone points.
- `core/canonical`: the mathlib Fubini comparison isomorphisms and their cocone/cone
  constructions.
- `bridge/view`: the `curry.obj M ⋙ colim` and `curry.obj M ⋙ lim` specializations obtained from
  `DiagramOfCocones.mkOfHasColimits` and `DiagramOfCones.mkOfHasLimits`. -/

section

variable (M : I × J ⥤ C)

/-- Lemma 4.14.10: for a chosen diagram `D` of rowwise colimit cocones of a bifunctor `M`, the
resulting functor `D.coconePoints` has a colimit if and only if `M` has a colimit. -/
lemma hasColimit_coconePoints_iff_hasColimit (D : DiagramOfCocones (curry.obj M))
    (Q : ∀ i, IsColimit (D.obj i)) : HasColimit D.coconePoints ↔ HasColimit M := by
  constructor
  · intro h
    let _ := h
    let e : M ≅ uncurry.obj (curry.obj M) := (currying.symm.unitIso).app M
    let cM : Cocone M :=
      { pt := colimit D.coconePoints
        ι :=
          { app x := (D.obj x.1).ι.app x.2 ≫ colimit.ι D.coconePoints x.1
            naturality {x y} := fun ⟨f₁, f₂⟩ ↦ by
              have hrow := (D.obj y.1).w f₂
              have hmap := (D.map f₁).w x.2
              have hw := colimit.w D.coconePoints f₁
              dsimp [DiagramOfCocones.coconePoints] at hrow hmap hw ⊢
              simpa [DiagramOfCocones.coconePoints] using
                (calc
                  M.map (f₁, f₂) ≫ (D.obj y.1).ι.app y.2 ≫ colimit.ι D.coconePoints y.1
                      = M.map (Prod.mkHom f₁ (𝟙 x.2)) ≫
                          (M.map (Prod.mkHom (𝟙 y.1) f₂) ≫ (D.obj y.1).ι.app y.2) ≫
                            colimit.ι D.coconePoints y.1 := by
                          simp only [Prod.fac' (f₁, f₂), M.map_comp, Category.assoc]
                  _ = M.map (Prod.mkHom f₁ (𝟙 x.2)) ≫ (D.obj y.1).ι.app x.2 ≫
                        colimit.ι D.coconePoints y.1 := by
                          simpa [Category.assoc] using congrArg
                            (fun z ↦ M.map (Prod.mkHom f₁ (𝟙 x.2)) ≫ z ≫
                              colimit.ι D.coconePoints y.1)
                            hrow
                  _ = (D.obj x.1).ι.app x.2 ≫ (D.map f₁).hom ≫ colimit.ι D.coconePoints y.1 := by
                        simpa [Category.assoc] using congrArg
                          (fun z ↦ z ≫ colimit.ι D.coconePoints y.1)
                          hmap.symm
                  _ = (D.obj x.1).ι.app x.2 ≫ colimit.ι D.coconePoints x.1 ≫ 𝟙 _ := by
                        have hw' := congrArg ((D.obj x.1).ι.app x.2 ≫ ·) hw
                        simpa only [Category.comp_id, Category.assoc] using hw') } }
    let c : Cocone (uncurry.obj (curry.obj M)) :=
      (Cocone.precompose e.inv).obj cM
    let S : ∀ i, Cocone ((curry.obj M).obj i) := fun i ↦
      { pt := colimit D.coconePoints
        ι :=
          { app j := c.ι.app (i, j)
            naturality {j j'} f := by
              simpa using @NatTrans.naturality _ _ _ _ _ _ c.ι (i, j) (i, j') (𝟙 i, f) } }
    have hcocone : IsColimit (coconeOfCoconeUncurry Q c) := by
      let hico : coconeOfCoconeUncurry Q c ≅ colimit.cocone D.coconePoints :=
        Cocone.ext (Iso.refl (colimit D.coconePoints)) fun i ↦ by
          apply (Q i).hom_ext
          intro j
          simpa [S, c, cM, e, coconeOfCoconeUncurry] using
            (Q i).fac (S i) j
      exact IsColimit.ofIsoColimit (colimit.isColimit D.coconePoints) hico.symm
    have hc : IsColimit c := by
      apply IsColimit.ofCoconeUncurry Q
      exact hcocone
    let _ : HasColimit (uncurry.obj (curry.obj M)) := ⟨⟨c, hc⟩⟩
    exact hasColimit_of_iso e
  · intro h
    let _ := h
    let e : M ≅ uncurry.obj (curry.obj M) := (currying.symm.unitIso).app M
    let c : Cocone (uncurry.obj (curry.obj M)) := (Cocone.precompose e.inv).obj (colimit.cocone M)
    have hc : IsColimit c :=
      (IsColimit.precomposeInvEquiv e (colimit.cocone M)).symm (colimit.isColimit M)
    exact ⟨⟨coconeOfCoconeUncurry Q c, coconeOfCoconeUncurryIsColimit Q hc⟩⟩

/-- Under the hypotheses of Lemma 4.14.10, the colimit of the rowwise-colimit functor
`D.coconePoints` is canonically isomorphic to the colimit of `M`. -/
noncomputable def colimitCoconePointsIsoColimit (D : DiagramOfCocones (curry.obj M))
    (Q : ∀ i, IsColimit (D.obj i)) [HasColimit D.coconePoints] [HasColimit M] :
    colimit D.coconePoints ≅ colimit M :=
  let e : M ≅ uncurry.obj (curry.obj M) := (currying.symm.unitIso).app M
  let c : Cocone (uncurry.obj (curry.obj M)) := (Cocone.precompose e.inv).obj (colimit.cocone M)
  let hc : IsColimit c :=
    (IsColimit.precomposeInvEquiv e (colimit.cocone M)).symm (colimit.isColimit M)
  colimit.isoColimitCocone
    ⟨coconeOfCoconeUncurry Q c, coconeOfCoconeUncurryIsColimit Q hc⟩

/-- Bridge specialization of Lemma 4.14.10: when all `J`-indexed rowwise colimits exist in `C`,
the source-facing functor `D.coconePoints` is canonically `curry.obj M ⋙ colim`. -/
lemma hasColimit_curryCompColim_iff_hasColimit [HasColimitsOfShape J C] :
    HasColimit (curry.obj M ⋙ colim) ↔ HasColimit M := by
  simpa [DiagramOfCocones.mkOfHasColimits_coconePoints] using
    hasColimit_coconePoints_iff_hasColimit M (DiagramOfCocones.mkOfHasColimits (curry.obj M))
      fun i ↦ colimit.isColimit _

end

section

variable (M : I × J ⥤ C)

/-- Dual companion to Lemma 4.14.10: for a chosen diagram `D` of rowwise limit cones of a
bifunctor `M`, the resulting functor `D.conePoints` has a limit if and only if `M` has a
limit. -/
lemma hasLimit_conePoints_iff_hasLimit (D : DiagramOfCones (curry.obj M))
    (Q : ∀ i, IsLimit (D.obj i)) : HasLimit D.conePoints ↔ HasLimit M := by
  constructor
  · intro h
    let _ := h
    let e : M ≅ uncurry.obj (curry.obj M) := (currying.symm.unitIso).app M
    let cM : Cone M :=
      { pt := limit D.conePoints
        π :=
          { app x := limit.π D.conePoints x.1 ≫ (D.obj x.1).π.app x.2
            naturality {x y} := fun ⟨f₁, f₂⟩ ↦ by
              have hrow := (D.obj x.1).w f₂
              have hmap := (D.map f₁).w y.2
              have hw := limit.w D.conePoints f₁
              dsimp [DiagramOfCones.conePoints] at hrow hmap hw ⊢
              rw [← hw, Category.assoc, hmap, ← hrow]
              simp only [Category.id_comp, Category.assoc, Prod.fac (f₁, f₂), M.map_comp] } }
    let c : Cone (uncurry.obj (curry.obj M)) :=
      (Cone.postcompose e.hom).obj cM
    let S : ∀ i, Cone ((curry.obj M).obj i) := fun i ↦
      { pt := limit D.conePoints
        π :=
          { app j := c.π.app (i, j)
            naturality {j j'} f := by
              simpa using @NatTrans.naturality _ _ _ _ _ _ c.π (i, j) (i, j') (𝟙 i, f) } }
    have hcone : IsLimit (coneOfConeUncurry Q c) := by
      let hiso : coneOfConeUncurry Q c ≅ limit.cone D.conePoints :=
        Cone.ext (Iso.refl (limit D.conePoints)) fun i ↦ by
          apply (Q i).hom_ext
          intro j
          simpa [S, c, cM, e, coneOfConeUncurry] using (Q i).fac (S i) j
      exact IsLimit.ofIsoLimit (limit.isLimit D.conePoints) hiso.symm
    have hc : IsLimit c := by
      apply IsLimit.ofConeOfConeUncurry Q
      exact hcone
    let _ : HasLimit (uncurry.obj (curry.obj M)) := ⟨⟨c, hc⟩⟩
    exact hasLimit_of_iso e.symm
  · intro h
    let _ := h
    let e : M ≅ uncurry.obj (curry.obj M) := (currying.symm.unitIso).app M
    let c : Cone (uncurry.obj (curry.obj M)) := (Cone.postcompose e.hom).obj (limit.cone M)
    have hc : IsLimit c := (IsLimit.postcomposeHomEquiv e (limit.cone M)).symm (limit.isLimit M)
    exact ⟨⟨coneOfConeUncurry Q c, coneOfConeUncurryIsLimit Q hc⟩⟩

/-- Dual bridge specialization of Lemma 4.14.10: when all `J`-indexed rowwise limits exist in `C`,
the source-facing functor `D.conePoints` is canonically `curry.obj M ⋙ lim`. -/
lemma hasLimit_curryCompLim_iff_hasLimit [HasLimitsOfShape J C] :
    HasLimit (curry.obj M ⋙ lim) ↔ HasLimit M := by
  simpa [DiagramOfCones.mkOfHasLimits_conePoints] using
    hasLimit_conePoints_iff_hasLimit M (DiagramOfCones.mkOfHasLimits (curry.obj M))
      fun i ↦ limit.isLimit _

/-- Under the hypotheses of Lemma 4.14.10, the limit of the rowwise-limit functor
`D.conePoints` is canonically isomorphic to the limit of `M`. -/
noncomputable def limitConePointsIsoLimit (D : DiagramOfCones (curry.obj M))
    (Q : ∀ i, IsLimit (D.obj i)) [HasLimit D.conePoints] [HasLimit M] :
    limit D.conePoints ≅ limit M :=
  let e : M ≅ uncurry.obj (curry.obj M) := (currying.symm.unitIso).app M
  let c : Cone (uncurry.obj (curry.obj M)) := (Cone.postcompose e.hom).obj (limit.cone M)
  let hc : IsLimit c := (IsLimit.postcomposeHomEquiv e (limit.cone M)).symm (limit.isLimit M)
  limit.isoLimitCone ⟨coneOfConeUncurry Q c, coneOfConeUncurryIsLimit Q hc⟩

end

/- Companion recall: when both colimits exist, the canonical comparison isomorphism identifying the
total colimit of `M` with the iterated colimit `colimit (curry.obj M ⋙ colim)` is
`colimitIsoColimitCurryCompColim`. -/
recall colimitIsoColimitCurryCompColim

/- Companion recall: when both iterated colimits exist, the canonical comparison isomorphism
`colimitCurrySwapCompColimIsoColimitCurryCompColim` identifies the two orders of iterated colimit,
corresponding to the textbook equality
`colim_i colim_j M_{i,j} = colim_j colim_i M_{i,j}` up to canonical isomorphism. -/
recall colimitCurrySwapCompColimIsoColimitCurryCompColim

/- Dual companion recall: the canonical limit comparison identifying the limit of `M` with the
iterated limit `limit (curry.obj M ⋙ lim)` is `limitIsoLimitCurryCompLim`. -/
recall limitIsoLimitCurryCompLim

/- Dual companion recall: the canonical comparison
`limitCurrySwapCompLimIsoLimitCurryCompLim` identifies the two orders of iterated limit. -/
recall limitCurrySwapCompLimIsoLimitCurryCompLim

end CategoryTheory.Limits

/-! ### Lemma_4_14_11 (from Chap04) -/
universe w v u

namespace CategoryTheory.Limits

open HasLimitOfHasProductsOfHasEqualizers

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [SmallCategory J]
variable {F : J ⥤ C}
variable {c₁ : Fan F.obj}
variable {c₂ : Fan fun f : Σ p : J × J, p.1 ⟶ p.2 ↦ F.obj f.1.2}
variable (s t : c₁.pt ⟶ c₂.pt)
variable
  (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫ F.map f.2)
  (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.2⟩)
variable {i : Fork s t}

/- Domain-style sampling for Lemma 4.14.11:
- primary domain: constructing limits from products and equalizers in category theory.
- sampled owner abstractions in
  `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers`:
  `HasLimitOfHasProductsOfHasEqualizers.buildLimit`,
  `HasLimitOfHasProductsOfHasEqualizers.buildIsLimit`,
  `limitConeOfEqualizerAndProduct`,
  `hasLimit_of_equalizer_and_product`.

Primitive-vs-derived split:
- primitive data: the product cones `c₁`, `c₂`, the comparison morphisms `s`, `t`, the
  compatibility equations `hs`, `ht`, and the equalizer fork `i`.
- derived API: the induced cone `buildLimit s t hs ht i` and the owner-level proof
  `buildIsLimit`.

Source/core/bridge triage:
- `source-facing`: the textbook construction of a limit cone from products and an equalizer.
- `core/canonical`: `buildIsLimit`.
- `bridge/view`: this file is a direct canonical recall of that owner theorem, not a parallel
  wrapper.
This rewrite targets the `core/canonical` layer by recalling the owner theorem directly. -/

/- Lemma 4.14.11: for a diagram `F : J ⥤ C`, if one chooses a product of the objects `F.obj j`,
a product of the target objects indexed by morphisms `u : j₁ ⟶ j₂`, and an equalizer of the two
canonical maps whose `u`-components are the projection to `F.obj j₂` and the composite of the
projection to `F.obj j₁` with `F.map u`, then the induced cone is a limit cone of `F`. This is
exactly the canonical mathlib theorem
`HasLimitOfHasProductsOfHasEqualizers.buildIsLimit`. -/
recall buildIsLimit (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) (hi : IsLimit i) :
    IsLimit (buildLimit s t hs ht i)

end CategoryTheory.Limits

/-! ### Lemma_4_14_12 (from Chap04) -/
universe w v u

namespace CategoryTheory.Limits

open HasColimitOfHasCoproductsOfHasCoequalizers

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [SmallCategory J]
variable {F : J ⥤ C}
variable {c₁ : Cofan fun f : Σ p : J × J, p.1 ⟶ p.2 ↦ F.obj f.1.1}
variable {c₂ : Cofan F.obj}
variable (s t : c₁.pt ⟶ c₂.pt)
variable
  (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ s = F.map f.2 ≫ c₂.ι.app ⟨f.1.2⟩)
  (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ t = c₂.ι.app ⟨f.1.1⟩)
variable {i : Cofork s t}

/- Domain-style sampling for Lemma 4.14.12:
- primary domain: constructing colimits from coproducts and coequalizers in category theory.
- sampled owner abstractions in
  `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers`:
  `HasColimitOfHasCoproductsOfHasCoequalizers.buildColimit`,
  `HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit`,
  `colimitCoconeOfCoequalizerAndCoproduct`,
  `hasColimit_of_coequalizer_and_coproduct`.

Primitive-vs-derived split:
- primitive data: the coproduct cocones `c₁`, `c₂`, the comparison morphisms `s`, `t`, the
  compatibility equations `hs`, `ht`, and the coequalizer cofork `i`.
- derived API: the induced cocone `buildColimit s t hs ht i` and the owner-level proof
  `buildIsColimit`.

Source/core/bridge triage:
- `source-facing`: the textbook construction of a colimit cocone from coproducts and a
  coequalizer.
- `core/canonical`: `HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit`.
- `bridge/view`: this file is a direct canonical recall of that owner theorem, not a parallel
  wrapper.
This rewrite targets the `core/canonical` layer by recalling the owner theorem directly. -/

/- Lemma 4.14.12: for a diagram `F : J ⥤ C`, if one chooses a coproduct of the objects `F.obj j`,
a coproduct of the source objects indexed by morphisms `u : j₁ ⟶ j₂`, and a coequalizer of the two
canonical maps whose `u`-components are the projection to `F.obj j₁` and the composite of `F.map u`
with the projection to `F.obj j₂`, then the induced cocone is a colimit cocone of `F`. This is
exactly the canonical mathlib theorem
`HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit`. -/
recall buildIsColimit (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) (hi : IsColimit i) :
    IsColimit (buildColimit s t hs ht i)

end CategoryTheory.Limits
