import Mathlib.Algebra.Exact
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.BasedCWComplex

open CategoryTheory Limits
open HomotopicalAlgebra

noncomputable section

universe w

/-- A chosen reduced suspension/cofiber setup on `BasedCWComplex` for the Chapter 14 reduced
homology axioms. -/
structure BasedCWReducedSuspensionCofiberSetup
    [CategoryWithCofibrations BasedCWComplex] where
  /-- The chosen reduced suspension endofunctor on based CW complexes. -/
  suspension : BasedCWComplex ⥤ BasedCWComplex
  /-- The chosen cofiber construction on arrows of based CW complexes. -/
  cofiber : Arrow BasedCWComplex ⥤ BasedCWComplex
  /-- The chosen quotient map from a based CW complex into the cofiber of a cofibration. -/
  cofiberMap :
    ∀ {A X : BasedCWComplex} (i : A ⟶ X), X ⟶ cofiber.obj (Arrow.mk i)

/-- CW exactness for a `ℤ`-graded family of functors on based CW complexes. The cofiber object and
quotient map are carried explicitly, as in `ReducedHomologyTheory`. -/
class CWExactness
    [CategoryWithCofibrations BasedCWComplex]
    (cofiber : Arrow BasedCWComplex ⥤ BasedCWComplex)
    (cofiberMap : ∀ {A X : BasedCWComplex} (i : A ⟶ X), X ⟶ cofiber.obj (Arrow.mk i))
    (E : ℤ → BasedCWComplex ⥤ AddCommGrpCat) : Prop where
  /-- For a cofibration `i : A ⟶ X` of based CW complexes, the induced sequence
  `E_q(A) ⟶ E_q(X) ⟶ E_q(cofiber i) ⟶ E_(q-1)(A)` is exact. -/
  exactness :
    ∀ q {A X : BasedCWComplex} (i : A ⟶ X) [Cofibration i],
      ∃ δ : (E q).obj (cofiber.obj (Arrow.mk i)) ⟶ (E (q - 1)).obj A,
        Function.Exact ((E q).map i) ((E q).map (cofiberMap i)) ∧
          Function.Exact ((E q).map (cofiberMap i)) δ

/-- Suspension isomorphisms for a `ℤ`-graded family of functors on based CW complexes. -/
class CWReducedHomologySuspension
    (suspension : BasedCWComplex ⥤ BasedCWComplex)
    (E : ℤ → BasedCWComplex ⥤ AddCommGrpCat) : Prop where
  /-- Each degree `q` admits a suspension isomorphism
  `E_q(ΣX) ≅ E_(q-1)(X)` on based CW complexes. -/
  exists_suspensionIso : ∀ q, Nonempty (suspension ⋙ E q ≅ E (q - 1))

namespace CWReducedHomologySuspension

/-- A CW suspension axiom determines a chosen degree-shifting suspension isomorphism. -/
noncomputable abbrev suspensionIso
    {suspension : BasedCWComplex ⥤ BasedCWComplex}
    {E : ℤ → BasedCWComplex ⥤ AddCommGrpCat}
    [h : CWReducedHomologySuspension suspension E]
    (q : ℤ) :
    suspension ⋙ E q ≅ E (q - 1) :=
  Classical.choice (h.exists_suspensionIso q)

/-- The chosen suspension isomorphism recovers the existence form used in source statements that
only ask for a degree-shifting suspension isomorphism. -/
theorem suspensionIso_nonempty
    {suspension : BasedCWComplex ⥤ BasedCWComplex}
    {E : ℤ → BasedCWComplex ⥤ AddCommGrpCat}
    [h : CWReducedHomologySuspension suspension E]
    (q : ℤ) :
    Nonempty (suspension ⋙ E q ≅ E (q - 1)) :=
  ⟨suspensionIso q⟩

end CWReducedHomologySuspension

/-- Wedge additivity for a `ℤ`-graded family of functors on based CW complexes. -/
class CWWedgeAdditive
    (E : ℤ → BasedCWComplex ⥤ AddCommGrpCat) : Prop where
  /-- Each degree functor preserves wedges indexed by a discrete type. -/
  preservesWedges :
    ∀ q {ι : Type w}, PreservesColimitsOfShape (Discrete ι) (E q)

/-- Definition 14.4.4: a reduced homology theory on based CW complexes is a `ℤ`-graded family of
functors on the full subcategory of based spaces whose underlying spaces admit CW-complex
structures, satisfying the CW versions of exactness, suspension, and wedge additivity. -/
class ReducedHomologyTheoryOnBasedCWComplexes
    [CategoryWithCofibrations BasedCWComplex]
    (suspension : outParam (BasedCWComplex ⥤ BasedCWComplex))
    (cofiber : outParam (Arrow BasedCWComplex ⥤ BasedCWComplex))
    (cofiberMap :
      outParam (∀ {A X : BasedCWComplex} (i : A ⟶ X), X ⟶ cofiber.obj (Arrow.mk i)))
    (E : ℤ → BasedCWComplex ⥤ AddCommGrpCat) : Prop
    extends CWExactness cofiber cofiberMap E,
      CWReducedHomologySuspension suspension E,
      CWWedgeAdditive.{w} E

namespace ReducedHomologyTheoryOnBasedCWComplexes

/-- A reduced homology theory on based CW complexes determines a chosen degree-shifting
suspension isomorphism in each degree. -/
noncomputable abbrev suspensionIso
    [CategoryWithCofibrations BasedCWComplex]
    {suspension : BasedCWComplex ⥤ BasedCWComplex}
    {cofiber : Arrow BasedCWComplex ⥤ BasedCWComplex}
    {cofiberMap : ∀ {A X : BasedCWComplex} (i : A ⟶ X), X ⟶ cofiber.obj (Arrow.mk i)}
    {E : ℤ → BasedCWComplex ⥤ AddCommGrpCat}
    [ReducedHomologyTheoryOnBasedCWComplexes suspension cofiber cofiberMap E]
    (q : ℤ) :
    suspension ⋙ E q ≅ E (q - 1) :=
  CWReducedHomologySuspension.suspensionIso q

end ReducedHomologyTheoryOnBasedCWComplexes

/-- A reduced homology theory on based CW complexes carries the three CW axioms together. -/
theorem ReducedHomologyTheoryOnBasedCWComplexes.spec
    [CategoryWithCofibrations BasedCWComplex]
    {suspension : BasedCWComplex ⥤ BasedCWComplex}
    {cofiber : Arrow BasedCWComplex ⥤ BasedCWComplex}
    {cofiberMap : ∀ {A X : BasedCWComplex} (i : A ⟶ X), X ⟶ cofiber.obj (Arrow.mk i)}
    {E : ℤ → BasedCWComplex ⥤ AddCommGrpCat}
    [h : ReducedHomologyTheoryOnBasedCWComplexes.{w} suspension cofiber cofiberMap E] :
    CWExactness cofiber cofiberMap E ∧
      CWReducedHomologySuspension suspension E ∧
      CWWedgeAdditive.{w} E :=
  ⟨inferInstance, inferInstance, inferInstance⟩
