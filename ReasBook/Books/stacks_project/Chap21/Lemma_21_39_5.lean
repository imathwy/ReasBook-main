import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [Category A] [Abelian A] [HasDerivedCategory A]
variable [HasDerivedCategory (Cᵒᵖ ⥤ A)]
variable [HasColimitsOfShape Cᵒᵖ A]

/-- The inverse-image functor for the projection from a category over a point is the constant
diagram functor. -/
abbrev categoryOverPointInverseImage : A ⥤ (Cᵒᵖ ⥤ A) :=
  (Functor.const (Cᵒᵖ) : A ⥤ (Cᵒᵖ ⥤ A))

/-- The constant inverse-image functor over a point is additive. -/
instance categoryOverPointInverseImage_additive :
    ((Functor.const (Cᵒᵖ) : A ⥤ (Cᵒᵖ ⥤ A))).Additive := sorry

/-- The exact inverse-image functor on derived categories for the projection from a category over a
point. -/
abbrev categoryOverPointDerivedInverseImage :
    DerivedCategory A ⥤ DerivedCategory (Cᵒᵖ ⥤ A) :=
  ((Functor.const (Cᵒᵖ) : A ⥤ (Cᵒᵖ ⥤ A))).mapDerivedCategory

/-- The lower shriek functor for the projection from a category over a point is the colimit
functor. -/
abbrev categoryOverPointLowerShriek : (Cᵒᵖ ⥤ A) ⥤ A :=
  colim

/-- The adjunction `\pi_! ⊣ \pi^{-1}` for the projection from a category over a point. -/
abbrev categoryOverPointLowerShriekAdjunction :
    (colim : (Cᵒᵖ ⥤ A) ⥤ A) ⊣ (Functor.const (Cᵒᵖ) : A ⥤ (Cᵒᵖ ⥤ A)) :=
  Limits.colimConstAdj

/-- The homotopy-to-derived functor whose total left derived functor is the derived lower shriek
for a category over a point. -/
abbrev categoryOverPointLowerShriekToDerived :
    HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A :=
  ((colim : (Cᵒᵖ ⥤ A) ⥤ A)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- The derived lower shriek functor `L\pi_!` for the projection from a category over a point. -/
abbrev categoryOverPointDerivedLowerShriek
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointLowerShriekToDerived :
        HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))] :
    DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A :=
  Functor.totalLeftDerived
    (categoryOverPointLowerShriekToDerived :
      HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A)
    (DerivedCategory.Qh :
      HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Cᵒᵖ ⥤ A))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))

-- Proof sketch: if `C` has an initial object, then `Cᵒᵖ` has a terminal object, so the colimit of
-- a constant diagram is evaluation at that terminal object; if `C` has a final object, then
-- `Cᵒᵖ` has an initial object and the constant diagram still has colimit the given value because
-- all of its transition maps are identities.
/-- If the indexing category has an initial or a final object, then the underived lower shriek for
the projection to a point has invertible counit `\pi_! \pi^{-1} \to \mathrm{id}`. -/
theorem categoryOverPointLowerShriek_comp_inverseImage_counit_isIso
    (hC : Nonempty (Limits.HasInitial C) ∨ Nonempty (Limits.HasTerminal C)) :
    IsIso
      ((categoryOverPointLowerShriekAdjunction :
          (colim : (Cᵒᵖ ⥤ A) ⥤ A) ⊣ (Functor.const (Cᵒᵖ) : A ⥤ (Cᵒᵖ ⥤ A))).counit) := sorry

variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointLowerShriekToDerived :
    HomotopyCategory (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) ⥤ DerivedCategory A)
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ))]

-- Proof sketch: under the initial/final-object hypothesis, the underived composite
-- `π_! ∘ π⁻¹` has invertible counit by the previous theorem. Since `π⁻¹` is an exact functor, it
-- lifts directly to derived categories, and then the adjunction criterion of Lemma `4.24.4`
-- identifies invertibility of the derived counit with the statement that `Lπ_! ∘ π⁻¹ = id`.
/-- Lemma 21.39.5: in the category-over-a-point situation of Example 21.39.1, if `C` has either
an initial object or a final object, then the derived lower shriek followed by inverse image is
naturally isomorphic to the identity on `D(A)`, equivalently the counit
`L\pi_! \circ \pi^{-1} \to \mathrm{id}` is an isomorphism. Specializing `A` to `AddCommGrpCat`
and to `ModuleCat B` recovers the textbook statements on `D(\mathrm{Ab})` and `D(B)`. -/
theorem categoryOverPointDerivedLowerShriek_comp_inverseImage_counit_isIso
    (adj :
      (categoryOverPointDerivedLowerShriek :
          DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A) ⊣
        (categoryOverPointDerivedInverseImage :
          DerivedCategory A ⥤ DerivedCategory (Cᵒᵖ ⥤ A)))
    (hC : Nonempty (Limits.HasInitial C) ∨ Nonempty (Limits.HasTerminal C)) :
    IsIso adj.counit := sorry

end

end CategoryTheory
