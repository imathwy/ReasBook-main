import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {B : Type w} [CommRing B] {B' : Type w} [CommRing B']
variable [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
variable [HasColimitsOfShape Cᵒᵖ (ModuleCat B')]

local notation "BPresheaf" => Cᵒᵖ ⥤ ModuleCat B
local notation "BPrimePresheaf" => Cᵒᵖ ⥤ ModuleCat B'
local notation "QisB" => HomotopyCategory.quasiIso (ModuleCat B) (up ℤ)
local notation "QisBPresheaf" => HomotopyCategory.quasiIso BPresheaf (up ℤ)
local notation "QisBPrimePresheaf" => HomotopyCategory.quasiIso BPrimePresheaf (up ℤ)

/-- The functor `K(\mathcal A) ⥤ D(\mathcal B)` induced by an additive functor
`F : \mathcal A ⥤ \mathcal B`. -/
abbrev mapHomotopyCategoryToDerived
    {𝒜 : Type u} {ℬ : Type w}
    [Category.{v} 𝒜] [Category ℬ]
    [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory ℬ]
    (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory ℬ :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The constant-diagram functor on `B`-modules is additive. -/
instance categoryOverPointDerivedInverseImage_additive :
    ((Functor.const (Cᵒᵖ) : ModuleCat B ⥤ BPresheaf)).Additive := sorry

/-- The exact inverse-image functor on derived categories for the projection from a category over a
point, here specialized to `B`-modules. -/
abbrev categoryOverPointDerivedInverseImage :
    DerivedCategory (ModuleCat B) ⥤ DerivedCategory BPresheaf :=
  (Functor.const (Cᵒᵖ) : ModuleCat B ⥤ BPresheaf).mapDerivedCategory

/-- The homotopy-to-derived functor whose total left derived functor is the derived lower shriek
for the projection from a category over a point. -/
abbrev categoryOverPointLowerShriekToDerived :
    HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B) :=
  (colim : BPresheaf ⥤ ModuleCat B).mapHomotopyCategory (up ℤ) ⋙
    DerivedCategory.Qh

/-- The derived lower shriek functor `L\pi_!` for the projection from a category over a point,
here specialized to `B`-modules. -/
abbrev categoryOverPointDerivedLowerShriek
    [Functor.HasLeftDerivedFunctor
      categoryOverPointLowerShriekToDerived
      QisBPresheaf] :
    DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B) :=
  Functor.totalLeftDerived
    categoryOverPointLowerShriekToDerived
    DerivedCategory.Qh
    QisBPresheaf

/-- Extension of scalars along a ring map `B → B'` is additive on module categories. -/
instance pointChangeOfRings_additive (φ : B →+* B') :
    (ModuleCat.extendScalars φ).Additive := sorry

/-- Pointwise extension of scalars along `φ` is additive on `B`-module valued presheaves. -/
instance presheafChangeOfRings_additive (φ : B →+* B') :
    ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
      (ModuleCat.extendScalars φ)).Additive := sorry

/-- The derived inverse-image functor on `D(B)` attached to a ring map `B → B'`. -/
abbrev pointChangeOfRingsDerivedPullback (φ : B →+* B')
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (ModuleCat.extendScalars φ))
      QisB] :
    DerivedCategory (ModuleCat B) ⥤ DerivedCategory (ModuleCat B') :=
  Functor.totalLeftDerived
    (mapHomotopyCategoryToDerived (ModuleCat.extendScalars φ))
    DerivedCategory.Qh
    QisB

-- Proof sketch: unfold `pointChangeOfRingsDerivedPullback`; it is defined to be the total left
-- derived functor of extension of scalars along `φ`.
/-- The point-level derived pullback is, by definition, the total left derived functor of
extension of scalars along the ring map `φ`. -/
theorem pointChangeOfRingsDerivedPullback_def (φ : B →+* B')
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (ModuleCat.extendScalars φ))
      QisB] :
    pointChangeOfRingsDerivedPullback φ =
      Functor.totalLeftDerived
        (mapHomotopyCategoryToDerived (ModuleCat.extendScalars φ))
        DerivedCategory.Qh
        QisB := sorry

/-- The derived inverse-image functor on `D(\underline B)` attached to a ring map `B → B'`,
computed pointwise on `B`-module valued presheaves. -/
abbrev presheafChangeOfRingsDerivedPullback (φ : B →+* B')
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived
        ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
          (ModuleCat.extendScalars φ)))
      QisBPresheaf] :
    DerivedCategory BPresheaf ⥤ DerivedCategory BPrimePresheaf :=
  Functor.totalLeftDerived
    (mapHomotopyCategoryToDerived
      ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
        (ModuleCat.extendScalars φ)))
    DerivedCategory.Qh
    QisBPresheaf

-- Proof sketch: unfold `presheafChangeOfRingsDerivedPullback`; it is defined as the total left
-- derived functor of pointwise extension of scalars on `B`-module valued presheaves.
/-- The presheaf-level derived pullback is, by definition, the total left derived functor of the
pointwise extension-of-scalars functor on `B`-module valued presheaves. -/
theorem presheafChangeOfRingsDerivedPullback_def (φ : B →+* B')
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived
        ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
          (ModuleCat.extendScalars φ)))
      QisBPresheaf] :
    presheafChangeOfRingsDerivedPullback φ =
      Functor.totalLeftDerived
        (mapHomotopyCategoryToDerived
          ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
            (ModuleCat.extendScalars φ)))
        DerivedCategory.Qh
        QisBPresheaf := sorry

/-- The obvious right adjoint `D(B') ⥤ D(\underline B)` obtained by first restricting scalars
along `B → B'` and then taking the constant `B`-valued diagram on `Cᵒᵖ`. -/
abbrev categoryOverPointChangeOfRingsRightAdjoint (φ : B →+* B') :
    DerivedCategory (ModuleCat B') ⥤ DerivedCategory BPresheaf :=
  (ModuleCat.restrictScalars φ).mapDerivedCategory ⋙
    categoryOverPointDerivedInverseImage

-- Proof sketch: unfold `categoryOverPointChangeOfRingsRightAdjoint`; it is the composite of the
-- derived restriction-of-scalars functor with the derived constant-diagram functor.
/-- The obvious right adjoint factors as derived restriction of scalars followed by the derived
constant-diagram functor over `Cᵒᵖ`. -/
theorem categoryOverPointChangeOfRingsRightAdjoint_def (φ : B →+* B') :
    categoryOverPointChangeOfRingsRightAdjoint φ =
      (ModuleCat.restrictScalars φ).mapDerivedCategory ⋙
        (categoryOverPointDerivedInverseImage :
          DerivedCategory (ModuleCat B) ⥤ DerivedCategory BPresheaf) := sorry

-- Proof sketch: the two composites in the statement are assumed to be left adjoint to the same
-- explicit right adjoint `categoryOverPointChangeOfRingsRightAdjoint φ`. The uniqueness theorem
-- `Adjunction.leftAdjointUniq` then produces the canonical isomorphism between them.
/-- Lemma 21.39.6: in the category-over-a-point situation of Example 21.39.1, for a ring map
`φ : B →+* B'`, the composite obtained by first changing rings on `B`-module valued presheaves
and then applying `L\pi'_!` is canonically isomorphic to the composite obtained by first applying
`L\pi_!` and then changing rings on the point. This is the library-facing form of the textbook
base-change identity between `L\pi_!`, `Lh^*`, `Lf^*`, and `L\pi'_!`. -/
abbrev categoryOverPoint_derivedLowerShriek_changeOfRingsIso (φ : B →+* B')
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (ModuleCat.extendScalars φ))
      QisB]
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived
        ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
          (ModuleCat.extendScalars φ)))
      QisBPresheaf]
    [Functor.HasLeftDerivedFunctor
      categoryOverPointLowerShriekToDerived
      QisBPresheaf]
    [Functor.HasLeftDerivedFunctor
      categoryOverPointLowerShriekToDerived
      QisBPrimePresheaf]
    (adj_presheaf :
      presheafChangeOfRingsDerivedPullback φ ⋙
          (categoryOverPointDerivedLowerShriek :
            DerivedCategory BPrimePresheaf ⥤ DerivedCategory (ModuleCat B')) ⊣
        categoryOverPointChangeOfRingsRightAdjoint φ)
    (adj_point :
      (categoryOverPointDerivedLowerShriek :
          DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B)) ⋙
          pointChangeOfRingsDerivedPullback φ ⊣
        categoryOverPointChangeOfRingsRightAdjoint φ) :
    presheafChangeOfRingsDerivedPullback φ ⋙
        (categoryOverPointDerivedLowerShriek :
          DerivedCategory BPrimePresheaf ⥤ DerivedCategory (ModuleCat B')) ≅
      (categoryOverPointDerivedLowerShriek :
          DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B)) ⋙
        pointChangeOfRingsDerivedPullback φ :=
  Adjunction.leftAdjointUniq adj_presheaf adj_point

-- Proof sketch: unfold `categoryOverPoint_derivedLowerShriek_changeOfRingsIso`; it is defined to
-- be the uniqueness isomorphism between the two specified left adjoints of the same right adjoint.
/-- The base-change isomorphism is defined by uniqueness of left adjoints to the obvious derived
restriction-constant functor. -/
theorem categoryOverPoint_derivedLowerShriek_changeOfRingsIso_def (φ : B →+* B')
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (ModuleCat.extendScalars φ))
      QisB]
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived
        ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
          (ModuleCat.extendScalars φ)))
      QisBPresheaf]
    [Functor.HasLeftDerivedFunctor
      categoryOverPointLowerShriekToDerived
      QisBPresheaf]
    [Functor.HasLeftDerivedFunctor
      categoryOverPointLowerShriekToDerived
      QisBPrimePresheaf]
    (adj_presheaf :
      presheafChangeOfRingsDerivedPullback φ ⋙
          (categoryOverPointDerivedLowerShriek :
            DerivedCategory BPrimePresheaf ⥤ DerivedCategory (ModuleCat B')) ⊣
        categoryOverPointChangeOfRingsRightAdjoint φ)
    (adj_point :
      (categoryOverPointDerivedLowerShriek :
          DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B)) ⋙
          pointChangeOfRingsDerivedPullback φ ⊣
        categoryOverPointChangeOfRingsRightAdjoint φ) :
    categoryOverPoint_derivedLowerShriek_changeOfRingsIso φ
        adj_presheaf adj_point =
      Adjunction.leftAdjointUniq adj_presheaf adj_point := sorry

end

end CategoryTheory
