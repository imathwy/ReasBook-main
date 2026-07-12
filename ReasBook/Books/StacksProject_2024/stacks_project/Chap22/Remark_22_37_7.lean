import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap22.Proposition_22_37_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

noncomputable section

universe uR uDA uDB uN vDA vDB vN

section

variable {DA : Type uDA} {DB : Type uDB}
variable [Category.{vDA} DA] [Category.{vDB} DB]
variable [HasZeroObject DA] [Preadditive DA]
variable [HasShift DA ℤ] [∀ n : ℤ, (shiftFunctor DA n).Additive] [Pretriangulated DA]

-- Semantic recall: `ObjectProperty.FullSubcategory` is the canonical owner for restricting a
-- functor to graded-projective objects, while `Triangle.mk _ _ _ ∈ distTriang _` is the source-
-- facing way to say that an object is a cone of a morphism in a triangulated category.

/-- An object is a cone of a morphism between graded-projective objects when it is the third
object of a distinguished triangle whose first two objects are graded-projective. -/
def IsConeOfMapBetweenGradedProjectives
    (gradedProjective : ObjectProperty DA) (M : DA) : Prop :=
  ∃ (X Y : DA) (_ : gradedProjective X) (_ : gradedProjective Y)
      (f : X ⟶ Y) (g : Y ⟶ M) (δ : M ⟶ (shiftFunctor DA (1 : ℤ)).obj X),
    Triangle.mk f g δ ∈ distTriang DA

/-- The defining expansion of `IsConeOfMapBetweenGradedProjectives`. -/
theorem isConeOfMapBetweenGradedProjectives_iff
    (gradedProjective : ObjectProperty DA) (M : DA) :
    IsConeOfMapBetweenGradedProjectives gradedProjective M ↔
      ∃ (X Y : DA) (_ : gradedProjective X) (_ : gradedProjective Y)
          (f : X ⟶ Y) (g : Y ⟶ M) (δ : M ⟶ (shiftFunctor DA (1 : ℤ)).obj X),
        Triangle.mk f g δ ∈ distTriang DA :=
  Iff.rfl

end

section

variable {DA : Type uDA} {DB : Type uDB}
variable [Category.{vDA} DA] [Category.{vDB} DB]

/-- If `F ≅ G` and `N ≅ F(A)`, the canonical comparison at `A` can be rewritten in the
source-facing form `G(A) ≅ N ≅ F(A)` used in Remark 22.37.7. -/
abbrev tensorUnitComparisonIsoOfNatIso
    {F G : DA ⥤ DB} {Aunit : DA} {N : DB}
    (hFG : F ≅ G) (hObjectIso : N ≅ F.obj Aunit) :
    G.obj Aunit ≅ N :=
  hFG.symm.app Aunit ≪≫ hObjectIso.symm

/-- The comparison `G(A) ≅ N ≅ F(A)` recovers the original component of `F ≅ G` at `A`. -/
theorem tensorUnitComparisonIsoOfNatIso_comp
    {F G : DA ⥤ DB} {Aunit : DA} {N : DB}
    (hFG : F ≅ G) (hObjectIso : N ≅ F.obj Aunit) :
    tensorUnitComparisonIsoOfNatIso hFG hObjectIso ≪≫ hObjectIso = hFG.symm.app Aunit := by
  simp [tensorUnitComparisonIsoOfNatIso]

/-- Restricting a natural isomorphism to the full subcategory of graded-projective objects gives
the functorial comparison on graded-projective objects used in Remark 22.37.7. -/
abbrev gradedProjectiveComparisonIsoOfNatIso
    {F G : DA ⥤ DB} (gradedProjective : ObjectProperty DA) (hFG : F ≅ G) :
    gradedProjective.ι ⋙ G ≅ gradedProjective.ι ⋙ F :=
  Functor.isoWhiskerLeft gradedProjective.ι hFG.symm

/-- The restricted comparison agrees at `A` with the source-facing tensor-unit comparison. -/
theorem gradedProjectiveComparisonIsoOfNatIso_app
    {F G : DA ⥤ DB} {Aunit : DA} {N : DB}
    (gradedProjective : ObjectProperty DA) (hA : gradedProjective Aunit)
    (hFG : F ≅ G) (hObjectIso : N ≅ F.obj Aunit) :
    (gradedProjectiveComparisonIsoOfNatIso gradedProjective hFG).app ⟨Aunit, hA⟩ =
      tensorUnitComparisonIsoOfNatIso hFG hObjectIso ≪≫ hObjectIso := by
  ext
  simp [gradedProjectiveComparisonIsoOfNatIso, tensorUnitComparisonIsoOfNatIso,
    Functor.isoWhiskerLeft_hom]

end

section

variable {DA : Type uDA} {DB : Type uDB}
variable [Category.{vDA} DA] [Category.{vDB} DB]
variable [HasZeroObject DA] [Preadditive DA]
variable [HasShift DA ℤ] [∀ n : ℤ, (shiftFunctor DA n).Additive] [Pretriangulated DA]

/-- Remark 22.37.7: let `G = derivedTensorWith N`. If the comparison from `G(A)` to `F(A)` has
been extended to a functorial isomorphism on graded-projective objects, then every object `M`
which is a cone of a morphism between graded-projective objects admits some comparison
isomorphism `G(M) ≅ F(M)`. The separate helpers `tensorUnitComparisonIsoOfNatIso` and
`gradedProjectiveComparisonIsoOfNatIso` record the stronger special case where this
graded-projective comparison comes from a global natural isomorphism. -/
@[stacks 09SB]
theorem dgBimoduleRealization_projectiveConeComparison
    (e : DA ≌ DB)
    {DGBimodAB : Type uN} [Category.{vN} DGBimodAB] [HasZeroMorphisms DGBimodAB]
    (derivedTensorWith : CochainComplex DGBimodAB ℤ → DA ⥤ DB)
    (gradedProjective : ObjectProperty DA)
    (N : CochainComplex DGBimodAB ℤ)
    (projectiveComparison :
      gradedProjective.ι ⋙ derivedTensorWith N ≅ gradedProjective.ι ⋙ e.functor)
    (M : DA)
    (hM_cone : IsConeOfMapBetweenGradedProjectives gradedProjective M) :
    Nonempty ((derivedTensorWith N).obj M ≅ e.functor.obj M) := by
  sorry

end
