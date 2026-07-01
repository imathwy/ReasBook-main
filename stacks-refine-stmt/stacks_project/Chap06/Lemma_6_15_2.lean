import Mathlib
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Over
import stacks_project.Chap06.Definition_6_15_1
import stacks_project.Chap06.LieAlgebraCat

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

private abbrev pointedBase : Type u := ULift.{u} PUnit

private noncomputable def pointedEquivUnder : Pointed.{u} ≌ Under (pointedBase.{u}) where
  functor :=
    { obj := fun X ↦ Under.mk (fun _ : pointedBase ↦ X.point)
      map := fun {X Y} f ↦ Under.homMk f.toFun (by
        funext x
        exact f.map_point) }
  inverse :=
    { obj := fun X ↦ Pointed.of (X.hom (ULift.up PUnit.unit))
      map := fun {X Y} f ↦ ⟨f.right, by
        simpa using congr_fun (Under.w f) (ULift.up PUnit.unit)⟩ }
  unitIso := NatIso.ofComponents (fun X ↦ Pointed.Iso.mk (Equiv.refl _) rfl)
  counitIso := NatIso.ofComponents (fun X ↦ Under.isoMk (Iso.refl _))

/-- The category of pointed sets has all limits. -/
instance : HasLimits Pointed :=
  Adjunction.has_limits_of_equivalence pointedEquivUnder.functor

/-- The forgetful functor from pointed sets to types preserves limits. -/
instance : PreservesLimits (forget Pointed) :=
  typeToPointedForgetAdjunction.rightAdjoint_preservesLimits

/-- The category of pointed sets has all colimits. -/
instance : HasColimits Pointed :=
  HasColimitsOfSize.mk (C := Pointed) fun J [Category J] ↦ by
    letI : HasColimits (Under pointedBase) := inferInstance
    letI : HasColimitsOfShape J (Under pointedBase) := inferInstance
    exact Adjunction.hasColimitsOfShape_of_equivalence pointedEquivUnder.functor

/-- The category of pointed sets has filtered colimits. -/
instance : HasFilteredColimits Pointed := by
  let h : HasColimits (Under pointedBase) := inferInstance
  letI : HasFilteredColimits (Under pointedBase) :=
    { HasColimitsOfShape := fun J _ _ ↦ h.has_colimits_of_shape J }
  exact ⟨fun J _ _ ↦ Adjunction.hasColimitsOfShape_of_equivalence pointedEquivUnder.functor⟩

/-- The forgetful functor from pointed sets to types preserves filtered colimits. -/
instance : PreservesFilteredColimits (forget Pointed) where
  preserves_filtered_colimits J _ _ := by
    change PreservesColimitsOfShape J (pointedEquivUnder.functor ⋙ Under.forget pointedBase)
    letI : PreservesColimitsOfShape J pointedEquivUnder.functor := inferInstance
    letI : PreservesColimitsOfShape J (Under.forget pointedBase) := inferInstance
    infer_instance

private theorem pointed_isIso_of_bijective {X Y : Pointed} (f : X ⟶ Y)
    (hf : Function.Bijective f) : IsIso f := by
  simpa using
    (Pointed.Iso.mk (Equiv.ofBijective f hf) (by simpa using f.map_point)).isIso_hom

/-- The forgetful functor from pointed sets to types reflects isomorphisms. -/
instance : (forget Pointed).ReflectsIsomorphisms where
  reflects f :=
    pointed_isIso_of_bijective f <|
      (CategoryTheory.isIso_iff_bijective ((forget Pointed).map f)).mp inferInstance

/-- The category of groups has filtered colimits. -/
instance : HasFilteredColimits GrpCat where
  HasColimitsOfShape _ _ _ :=
    ⟨fun F ↦ ⟨GrpCat.FilteredColimits.colimitCocone F,
      GrpCat.FilteredColimits.colimitCoconeIsColimit F⟩⟩

-- Proof sketch: limits of Lie algebras are constructed on the corresponding limits of the
-- underlying vector spaces, with bracket defined pointwise.

/-- Lemma 6.15.2 (1): the category of pointed sets, with its forgetful functor to sets, defines a
type of algebraic structures. -/
instance pointed_sets_algebraic_structure_type :
    IsAlgebraicStructure Pointed (forget Pointed) :=
  inferInstance

/-- Lemma 6.15.2 (2): the category of abelian groups, with its forgetful functor to sets, defines
a type of algebraic structures. -/
instance abelian_groups_algebraic_structure_type :
    IsAlgebraicStructure AddCommGrpCat (forget AddCommGrpCat) :=
  inferInstance

/-- Lemma 6.15.2 (3): the category of groups, with its forgetful functor to sets, defines a type
of algebraic structures. -/
instance groups_algebraic_structure_type :
    IsAlgebraicStructure GrpCat (forget GrpCat) :=
  inferInstance

/-- Lemma 6.15.2 (4): the category of monoids, with its forgetful functor to sets, defines a type
of algebraic structures. -/
instance monoids_algebraic_structure_type :
    IsAlgebraicStructure MonCat (forget MonCat) := by
  letI : HasLimits MonCat := inferInstance
  letI : PreservesLimits (forget MonCat) := inferInstance
  let h : HasColimits MonCat := inferInstance
  letI : HasFilteredColimits MonCat :=
    { HasColimitsOfShape := fun I _ _ ↦ h.has_colimits_of_shape I }
  letI : PreservesFilteredColimits (forget MonCat) :=
    { preserves_filtered_colimits := fun I _ _ ↦ by infer_instance }
  letI : (forget MonCat).ReflectsIsomorphisms := inferInstance
  infer_instance

/-- Lemma 6.15.2 (5): the category of rings, with its forgetful functor to sets, defines a type
of algebraic structures. -/
instance rings_algebraic_structure_type :
    IsAlgebraicStructure RingCat (forget RingCat) := by
  letI : HasLimits RingCat := inferInstance
  letI : PreservesLimits (forget RingCat) := inferInstance
  let h : HasColimits RingCat := inferInstance
  letI : HasFilteredColimits RingCat :=
    { HasColimitsOfShape := fun I _ _ ↦ h.has_colimits_of_shape I }
  letI : PreservesFilteredColimits (forget RingCat) :=
    { preserves_filtered_colimits := fun I _ _ ↦ by infer_instance }
  letI : (forget RingCat).ReflectsIsomorphisms := inferInstance
  infer_instance

/-- Lemma 6.15.2 (6): for a fixed ring `R`, the category of `R`-modules with its forgetful functor
to sets defines a type of algebraic structures. -/
instance modules_algebraic_structure_type (R : Type u) [Ring R] :
    IsAlgebraicStructure (ModuleCat.{u} R) (forget (ModuleCat.{u} R)) := by
  letI : HasLimits (ModuleCat.{u} R) := inferInstance
  letI : PreservesLimits (forget (ModuleCat.{u} R)) := inferInstance
  let h : HasColimitsOfSize.{u, u} (ModuleCat.{u} R) := inferInstance
  letI : HasFilteredColimits (ModuleCat.{u} R) :=
    { HasColimitsOfShape := fun I _ _ ↦ h.has_colimits_of_shape I }
  letI : PreservesFilteredColimits (forget (ModuleCat.{u} R)) :=
    { preserves_filtered_colimits := fun I _ _ ↦ by infer_instance }
  letI : (forget (ModuleCat.{u} R)).ReflectsIsomorphisms := inferInstance
  infer_instance

/-- Lemma 6.15.2 (7): for a fixed commutative ring `R`, the category of Lie algebras over `R`, with its
forgetful functor to sets, defines a type of algebraic structures. -/
instance lie_algebras_algebraic_structure_type (R : Type u) [CommRing R] :
    IsAlgebraicStructure (LieAlgebraCat R) (forget (LieAlgebraCat R)) := by
  sorry
