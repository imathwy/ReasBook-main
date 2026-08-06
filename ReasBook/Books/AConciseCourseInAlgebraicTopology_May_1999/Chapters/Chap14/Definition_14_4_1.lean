import Mathlib.Algebra.Exact
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1

open CategoryTheory Limits
open HomotopicalAlgebra

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` did not surface a canonical reduced-homology-theory owner
-- in the current environment. The source is therefore formalized on the full subcategory of
-- cofibrant objects in `BasedSpace`, i.e. based spaces with nondegenerate basepoint, relative to
-- explicit suspension and cofiber data.

/-- The category of nondegenerately based spaces, formalized as the full subcategory of cofibrant
objects in `BasedSpace`. -/
abbrev nondegeneratelyBasedSpace [CategoryWithCofibrations BasedSpace] :=
  CategoryTheory.ObjectProperty.FullSubcategory
    (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace)

local notation "NBasedSpace" => nondegeneratelyBasedSpace

/-- A chosen reduced suspension/cofiber setup on nondegenerately based spaces for the Chapter 14
reduced homology axioms. -/
structure ReducedSuspensionCofiberSetup
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace] where
  /-- The chosen reduced suspension endofunctor on nondegenerately based spaces. -/
  suspension : NBasedSpace ⥤ NBasedSpace
  /-- The chosen cofiber construction on arrows of nondegenerately based spaces. -/
  cofiber : Arrow NBasedSpace ⥤ NBasedSpace
  /-- The chosen quotient map from a based space into the cofiber of a cofibration. -/
  cofiberMap : ∀ {A X : NBasedSpace} (i : A ⟶ X), X ⟶ cofiber.obj (Arrow.mk i)

/-- Exactness for cofibrations in a `ℤ`-graded family of functors on nondegenerately based spaces.
The cofiber term and quotient map are carried by the chosen Chapter 14 reduced suspension/cofiber
setup because the current environment does not provide a single canonical cofiber owner. -/
class CofibrationExact
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpace ⥤ AddCommGrpCat) : Prop where
  /-- For a cofibration `i : A ⟶ X`, the induced sequence
  `E_q(A) ⟶ E_q(X) ⟶ E_q(cofiber i) ⟶ E_(q-1)(A)` is exact in the usual abelian-group sense. -/
  exactness :
    ∀ q {A X : NBasedSpace} (i : A ⟶ X) [Cofibration i],
      ∃ δ : (E q).obj (setup.cofiber.obj (Arrow.mk i)) ⟶ (E (q - 1)).obj A,
        Function.Exact ((E q).map i) ((E q).map (setup.cofiberMap i)) ∧
          Function.Exact ((E q).map (setup.cofiberMap i)) δ

/-- Suspension isomorphisms for a `ℤ`-graded family of functors on nondegenerately based spaces. -/
class ReducedHomologySuspension
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpace ⥤ AddCommGrpCat) : Prop where
  /-- Each degree `q` carries a natural suspension isomorphism
  `E_q(ΣX) ≅ E_(q-1)(X)`. -/
  suspensionIso : ∀ q, Nonempty (setup.suspension ⋙ E q ≅ E (q - 1))

/-- Definition 14.4.1: a reduced homology theory on nondegenerately based spaces, formalized here
relative to a chosen reduced suspension endofunctor and cofiber construction on
`nondegeneratelyBasedSpace`, is a `ℤ`-graded family of functors
`nondegeneratelyBasedSpace ⥤ AddCommGrpCat` satisfying exactness for cofibrations, suspension
isomorphism, wedge additivity, and weak-equivalence invariance. -/
class ReducedHomologyTheory
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpace ⥤ AddCommGrpCat) : Prop
    extends CofibrationExact setup E,
      ReducedHomologySuspension setup E where
  /-- Each degree functor preserves coproducts indexed by a discrete type, i.e. based wedges. -/
  preservesWedges :
    ∀ q {ι : Type u}, PreservesColimitsOfShape (Discrete ι) (E q)
  /-- A weak equivalence of nondegenerately based spaces induces an isomorphism in every degree. -/
  map_isIso :
    ∀ q {X Y : NBasedSpace} (f : X ⟶ Y) [WeakEquivalence f], IsIso ((E q).map f)

/-- A reduced homology theory satisfies the cofibration exactness axiom. -/
instance reducedHomologyTheoryToCofibrationExact
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpace ⥤ AddCommGrpCat}
    [h : ReducedHomologyTheory setup E] :
    CofibrationExact setup E :=
  h.toCofibrationExact

/-- A reduced homology theory satisfies the suspension-isomorphism axiom. -/
instance reducedHomologyTheoryToReducedHomologySuspension
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpace ⥤ AddCommGrpCat}
    [h : ReducedHomologyTheory setup E] :
    ReducedHomologySuspension setup E :=
  h.toReducedHomologySuspension

namespace ReducedHomologyTheory

/-- The suspension axiom implies existence of a natural suspension isomorphism in degree `q`. -/
theorem suspensionIso_nonempty
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpace ⥤ AddCommGrpCat}
    [h : ReducedHomologyTheory setup E]
    (q : ℤ) :
    Nonempty (setup.suspension ⋙ E q ≅ E (q - 1)) := by
  let hSusp : ReducedHomologySuspension setup E := inferInstance
  exact hSusp.suspensionIso q

/-- A reduced homology theory carries a chosen natural suspension isomorphism in degree `q`. -/
noncomputable abbrev suspensionNatIso
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpace ⥤ AddCommGrpCat}
    [ReducedHomologyTheory setup E]
    (q : ℤ) :
    setup.suspension ⋙ E q ≅ E (q - 1) :=
  Classical.choice ((inferInstance : ReducedHomologySuspension setup E).suspensionIso q)

/-- Applying the chosen suspension axiom at a fixed nondegenerately based space yields the
degree-shift isomorphism `E_q(ΣX) ≅ E_(q-1)(X)`. -/
noncomputable abbrev suspensionIsoApp
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpace ⥤ AddCommGrpCat}
    [h : ReducedHomologyTheory setup E]
    (q : ℤ) (X : NBasedSpace) :
    (E q).obj (setup.suspension.obj X) ≅ (E (q - 1)).obj X :=
  (suspensionNatIso q).app X

/-- The chosen suspension isomorphism yields the existential objectwise form used in source
statements that only ask for existence. -/
theorem suspensionIsoApp_nonempty
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    {E : ℤ → NBasedSpace ⥤ AddCommGrpCat}
    [ReducedHomologyTheory setup E]
    (q : ℤ) (X : NBasedSpace) :
    Nonempty ((E q).obj (setup.suspension.obj X) ≅ (E (q - 1)).obj X) :=
  ⟨suspensionIsoApp q X⟩

end ReducedHomologyTheory
