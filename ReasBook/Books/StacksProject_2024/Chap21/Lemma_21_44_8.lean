import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import stacks_project.Chap21.Definition_21_44_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {U : C}

local notation "ModU" => LocalizedRingedSiteModules J 𝒪 U
local notation "ModOver" V =>
  LocalizedRingedSiteModules (J := J.over U) (𝒪 := 𝒪.over U) V

/-- Restriction from `\mathcal O_U`-modules to the iterated localization over `V : Over U`. -/
abbrev localizedRestrictionToOver
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U : C} (V : Over U) :
    ModU ⥤ ModOver V :=
  SheafOfModules.pushforward
    (𝟙 ((((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U).over V))

/-- Restriction to an iterated localization preserves zero morphisms. -/
instance localizedRestrictionToOver_preservesZeroMorphisms
    (V : Over U) :
    (localizedRestrictionToOver 𝒪 V).PreservesZeroMorphisms := sorry

/-- Restriction of cochain complexes of `\mathcal O_U`-modules to the iterated localization over
`V : Over U`. -/
abbrev localizedRestrictionComplexToOver
    (𝒪 : Sheaf J CommRingCat.{max u v}) {U : C} (V : Over U) :
    CochainComplex ModU ℤ ⥤ CochainComplex (ModOver V) ℤ :=
  (localizedRestrictionToOver 𝒪 V).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The localization functor from complexes of `\mathcal O_U`-modules to the derived category
`D(\mathcal O_U)`. -/
abbrev localizedDerivedCategoryQuotient
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C) :
    CochainComplex ModU ℤ ⥤ DerivedCategory ModU :=
  DerivedCategory.Q

local notation "DModU" => DerivedCategory ModU

variable [Abelian ModU]
variable [∀ V : Over U, Abelian (ModOver V)]

/-- A morphism in `D(\mathcal O_U)` between the objects represented by complexes `E` and `F`. -/
abbrev LocalizedDerivedMorphism
    (E F : CochainComplex ModU ℤ) :=
  (localizedDerivedCategoryQuotient 𝒪 U).obj E ⟶
    (localizedDerivedCategoryQuotient 𝒪 U).obj F

/-- The proposition that a derived morphism from a strictly perfect complex admits a roof whose
restricted numerators are locally represented by chain maps. -/
def HasLocalRoofRepresentative
    (E F : CochainComplex ModU ℤ)
    (α : LocalizedDerivedMorphism E F) : Prop :=
  ∃ G : CochainComplex ModU ℤ, ∃ f : F ⟶ G, ∃ β : E ⟶ G,
    ∃ e :
      (localizedDerivedCategoryQuotient 𝒪 U).obj F ≅
        (localizedDerivedCategoryQuotient 𝒪 U).obj G,
      e.hom = (localizedDerivedCategoryQuotient 𝒪 U).map f ∧
        α = (localizedDerivedCategoryQuotient 𝒪 U).map β ≫ e.inv ∧
      ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
        ∀ i : ι,
          ∃ αi : ((localizedRestrictionComplexToOver 𝒪 (cover i)).obj E) ⟶
              ((localizedRestrictionComplexToOver 𝒪 (cover i)).obj F),
            Nonempty
              (Homotopy
                (αi ≫ (localizedRestrictionComplexToOver 𝒪 (cover i)).map f)
                ((localizedRestrictionComplexToOver 𝒪 (cover i)).map β))

/-- The proposition that a morphism of complexes becomes zero in `D(\mathcal O_U)`. -/
def MapsToZeroInLocalizedDerivedCategory
    (E F : CochainComplex ModU ℤ) (α : E ⟶ F) : Prop :=
  (localizedDerivedCategoryQuotient 𝒪 U).map α = 0

/-- The proposition that a morphism of complexes is locally homotopic to zero after restricting to
a covering of `U`. -/
def HasLocalNullHomotopy
    (E F : CochainComplex ModU ℤ) (α : E ⟶ F) : Prop :=
  ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
    ∀ i : ι,
      Nonempty (Homotopy ((localizedRestrictionComplexToOver 𝒪 (cover i)).map α) 0)

/-- Lemma 21.44.8 (1): a morphism in the localized derived category from a strictly perfect
complex is locally represented by a morphism of complexes after restricting to a cover of `U`. -/
abbrev exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect
    (E F : CochainComplex ModU ℤ)
    (α : LocalizedDerivedMorphism E F) :
    Prop :=
  CochainComplex.IsStrictlyPerfect E →
    HasLocalRoofRepresentative E F α

-- Proof sketch: unfold
-- `exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect`; the abbreviation is exactly the
-- implication from strict perfectness of `E` to the local roof-representative property for `α`.
/-- Applying the main abbreviation to a strictly perfect source complex yields a local roof
representative for the given derived morphism. -/
def exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect_apply
    (E F : CochainComplex ModU ℤ)
    (α : LocalizedDerivedMorphism E F)
    (h : exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect E F α)
    (hE : CochainComplex.IsStrictlyPerfect E) :
    HasLocalRoofRepresentative E F α := sorry

/-- If a morphism of complexes from a strictly perfect complex becomes zero in the localized
derived category, then after restricting to a cover of `U` it is homotopic to zero. -/
abbrev exists_cover_homotopicToZero_of_isStrictlyPerfect_of_Q_map_eq_zero
    (E F : CochainComplex ModU ℤ)
    (α : E ⟶ F) :
    Prop :=
  CochainComplex.IsStrictlyPerfect E →
    MapsToZeroInLocalizedDerivedCategory E F α →
      HasLocalNullHomotopy E F α

end

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {U : C}
variable [Abelian ModU]
variable [∀ V : Over U, Abelian (ModOver V)]

-- Proof sketch: unfold
-- `exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect`; the theorem simply restates the
-- proposition abbreviation as its defining implication.
/-- Unfolding the main abbreviation identifies it with the implication from strict perfectness of
`E` to the existence of a local roof representative for `α`. -/
theorem exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect_iff
    (E F : CochainComplex ModU ℤ)
    (α : LocalizedDerivedMorphism E F) :
    exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect E F α ↔
      CochainComplex.IsStrictlyPerfect E →
        HasLocalRoofRepresentative E F α := sorry

end SheafOfModules.RingedSite
