import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_6_1 (from Chap02) -/
universe v u₁ u₂

open CategoryTheory

variable (D : Type u₁) [SmallCategory D]
variable (C : Type u₂) [Category.{v} C]

/- Definition 2.6.1: for a small category `D` and a category `C`, a `D`-shaped diagram in `C`
is just a covariant functor as in Definition 2.2.1, namely the canonical functor type `D ⥤ C`
(equivalently, `CategoryTheory.Functor D C`). -/
#check (D ⥤ C)

/-! ### Definition_2_6_2 (from Chap02) -/
universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (D : Type u₁) [Category.{v₁} D]
variable (C : Type u₂) [Category.{v₂} C]
variable (F G : D ⥤ C)
variable (X : C)

/- Definition 2.6.2: a morphism of `D`-shaped diagrams is the canonical natural transformation
between functors `F G : D ⥤ C`, namely `F ⟶ G`; for a fixed object `X : C`, the constant
diagram is the functor sending every object of `D` to `X` and every morphism to `𝟙 X`. -/
#check (F ⟶ G)

/- A fixed object `X : C` determines the constant `D`-shaped diagram in `C`. -/
#check ((Functor.const D).obj X)

/-! ### Definition_2_6_3 (from Chap02) -/
universe v u₁ u₂

open CategoryTheory Limits

variable (D : Type u₁) [Category.{v} D]
variable (C : Type u₂) [Category.{v} C]
variable (F : D ⥤ C)
variable [HasColimit F]

/- Definition 2.6.3: the colimit of a diagram `F` is the canonical object `colimit F` of `C`. -/
#check (colimit F : C)

/- The colimit object carries its canonical cocone over `F`. -/
recall colimit.cocone (F : D ⥤ C) [HasColimit F] : Cocone F

/- Equivalently, the colimit cocone provides a diagram map from `F` to the constant diagram on
`colimit F`. -/
#check ((colimit.cocone F).ι : F ⟶ (Functor.const D).obj (colimit F))

/- The canonical cocone on `colimit F` is initial among cocones over `F`. -/
recall colimit.isColimit (F : D ⥤ C) [HasColimit F] : IsColimit (colimit.cocone F)

/-! ### Definition_2_6_4 (from Chap02) -/
universe v u₁ u₂

open CategoryTheory Limits

variable (D : Type u₁) [Category.{v} D]
variable (C : Type u₂) [Category.{v} C]
variable (F : D ⥤ C)
variable [HasLimit F]

/- Definition 2.6.4: the limit of a diagram `F` is the canonical object `limit F` of `C`. -/
#check (limit F : C)

/- The limit object carries its canonical cone over `F`. -/
recall limit.cone (F : D ⥤ C) [HasLimit F] : Cone F

/- Equivalently, the limit cone provides a diagram map from the constant diagram on `limit F`
to `F`. -/
#check ((limit.cone F).π : (Functor.const D).obj (limit F) ⟶ F)

/- The canonical cone on `limit F` is terminal among cones over `F`. -/
recall limit.isLimit (F : D ⥤ C) [HasLimit F] : IsLimit (limit.cone F)

/-! ### Example_2_6_5 (from Chap02) -/
universe v u₁ u₂

open CategoryTheory CategoryTheory.Limits

variable {ι : Type u₁} {C : Type u₂} [Category.{v} C] (f : ι → C)

/- Example 2.6.5: when a diagram is indexed by a discrete type `ι`, the existence of its colimit
is expressed by the canonical coproduct class `HasCoproduct f`. -/
#check (HasCoproduct f : Prop)

/- Dually, the existence of its limit is expressed by the canonical product class
`HasProduct f`. -/
#check (HasProduct f : Prop)

variable [HasCoproduct f]

/- The colimit of a discrete diagram is the coproduct object `∐ f`. In sets and topological
spaces, these recover disjoint unions. -/
#check (∐ f : C)

variable [HasProduct f]

/- The limit of a discrete diagram is the product object `∏ᶜ f`. In the standard examples, these
recover Cartesian products. -/
#check (∏ᶜ f : C)

/- Topological spaces have arbitrary coproducts and products, giving disjoint unions and Cartesian
products. -/
#check (inferInstance : HasCoproducts TopCat)

/- Topological spaces have arbitrary products. -/
#check (inferInstance : HasProducts TopCat)

/- Abelian groups have arbitrary coproducts and products; the coproducts are direct sums. -/
#check (inferInstance : HasCoproducts AddCommGrpCat)

/- Abelian groups have arbitrary products. -/
#check (inferInstance : HasProducts AddCommGrpCat)

/- Groups have arbitrary products, giving Cartesian products in `GrpCat`. -/
#check (inferInstance : HasProducts GrpCat)

/- For groups, the indexed free product carries the canonical coproduct inclusions
`Monoid.CoprodI.of`, and its universal property is expressed by `Monoid.CoprodI.lift`. -/
#check Monoid.CoprodI.of
#check Monoid.CoprodI.lift

/-! ### Example_2_6_6 (from Chap02) -/
universe v u

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y Z : C}

/- Example 2.6.6: for a diagram shape `Y ← X → Z`, the corresponding colimit is a pushout; for a
parallel pair it is a coequalizer, and reversing the arrows gives pullbacks and equalizers. -/
recall pushout.isColimit (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
  IsColimit (pushout.cocone f g)

/- A coequalizer is the colimit of a parallel pair. -/
recall coequalizerIsCoequalizer (p q : X ⟶ Y) [HasCoequalizer p q] :
  IsColimit (Cofork.ofπ (coequalizer.π p q) (coequalizer.condition p q))

/- Reversing the arrows in a span gives a pullback as the corresponding limit. -/
recall pullback.isLimit (a : X ⟶ Z) (b : Y ⟶ Z) [HasPullback a b] :
  IsLimit (pullback.cone a b)

/- Reversing the arrows in a parallel pair gives an equalizer as the corresponding limit. -/
recall equalizerIsEqualizer (p q : X ⟶ Y) [HasEqualizer p q] :
  IsLimit (Fork.ofι (equalizer.ι p q) (equalizer.condition p q))

/-! ### Definition_2_6_7 (from Chap02) -/
universe v u

open CategoryTheory Limits

/- Definition 2.6.7: a category is cocomplete when it has all colimits, expressed by the
canonical abbreviation `HasColimits`. -/
recall HasColimits (C : Type u) [Category.{v} C] : Prop

/- Completeness is the dual notion, expressed by the canonical abbreviation `HasLimits`. -/
recall HasLimits (C : Type u) [Category.{v} C] : Prop

/-! ### Remark_2_6_8 (from Chap02) -/
universe u

open CategoryTheory Limits

noncomputable instance : Coreflective (forget₂ GrpCat MonCat) :=
  Coreflective.mk MonCat.units GrpCat.forget₂MonAdj

/-- The category of groups is cocomplete because it is a coreflective subcategory of monoids. -/
noncomputable instance : HasColimits GrpCat :=
  hasColimits_of_coreflective (forget₂ GrpCat MonCat)

/- Remark 2.6.8: the category of sets is complete and cocomplete, via the canonical instances
`HasLimits (Type u)` and `HasColimits (Type u)`. -/
#check (inferInstance : HasLimits (Type u))
#check (inferInstance : HasColimits (Type u))

/- The category of topological spaces is complete and cocomplete. -/
#check (inferInstance : HasLimits TopCat)
#check (inferInstance : HasColimits TopCat)

/- The category of based spaces, realized as `Under (⊤_ TopCat)`, is complete and cocomplete. -/
#check (inferInstance : HasLimits (Under (⊤_ TopCat)))
#check (inferInstance : HasColimits (Under (⊤_ TopCat)))

/- The category of groups is complete and cocomplete. -/
#check (inferInstance : HasLimits GrpCat)
#check (inferInstance : HasColimits GrpCat)

/- The category of abelian groups is complete and cocomplete. -/
#check (inferInstance : HasLimits AddCommGrpCat)
#check (inferInstance : HasColimits AddCommGrpCat)
