import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Definition_14_4_4

open CategoryTheory Limits
open HomotopicalAlgebra

noncomputable section

universe w

-- This file reuses Chapter 14's canonical `BasedCWReducedSuspensionCofiberSetup` owner for the
-- chosen reduced suspension and cofiber data on `BasedCWComplex`.

/-- CW exactness for a `ℤ`-graded family of contravariant functors on based CW complexes,
relative to a chosen Chapter 14 reduced suspension/cofiber setup. -/
class CWReducedCohomologyExactness
    [CategoryWithCofibrations BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (E : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat) : Prop where
  /-- For a cofibration `i : A ⟶ X` of based CW complexes, the sequence
  `E q (cofiber i) ⟶ E q X ⟶ E q A ⟶ E (q + 1) (cofiber i)` is exact in the usual
  contravariant abelian-group sense. -/
  exactness :
    ∀ q {A X : BasedCWComplex} (i : A ⟶ X) [Cofibration i],
      ∃ δ :
          (E q).obj (Opposite.op A) ⟶
            (E (q + 1)).obj (Opposite.op (setup.cofiber.obj (Arrow.mk i))),
        Function.Exact ((E q).map (setup.cofiberMap i).op) ((E q).map i.op) ∧
          Function.Exact ((E q).map i.op) δ

/-- Suspension isomorphisms for a `ℤ`-graded family of contravariant functors on based CW
complexes, relative to a chosen Chapter 14 reduced suspension/cofiber setup. -/
class CWReducedCohomologySuspension
    [CategoryWithCofibrations BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (E : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat) : Prop where
  /-- Each degree `q` carries a natural suspension isomorphism
  `(E q).obj (Opposite.op (setup.suspension.obj X)) ≅ (E (q - 1)).obj (Opposite.op X)`. -/
  suspensionIso : ∀ q, Nonempty (setup.suspension.op ⋙ E q ≅ E (q - 1))

namespace CWReducedCohomologySuspension

/-- A CW suspension axiom determines a chosen natural suspension isomorphism in degree `q`. -/
noncomputable abbrev suspensionNatIso
    [CategoryWithCofibrations BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    {E : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat}
    [h : CWReducedCohomologySuspension setup E]
    (q : ℤ) :
    setup.suspension.op ⋙ E q ≅ E (q - 1) :=
  Classical.choice (h.suspensionIso q)

/-- Applying the chosen suspension isomorphism at `X` yields the degree-shift isomorphism
`(E q)(ΣX) ≅ (E (q - 1))(X)`. -/
noncomputable abbrev suspensionIsoApp
    [CategoryWithCofibrations BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    {E : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat}
    [CWReducedCohomologySuspension setup E]
    (q : ℤ) (X : BasedCWComplex) :
    (E q).obj (Opposite.op (setup.suspension.obj X)) ≅ (E (q - 1)).obj (Opposite.op X) :=
  (suspensionNatIso q).app (Opposite.op X)

/-- The chosen objectwise suspension isomorphism recovers the source-facing existence form. -/
theorem suspensionIsoApp_nonempty
    [CategoryWithCofibrations BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    {E : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat}
    [CWReducedCohomologySuspension setup E]
    (q : ℤ) (X : BasedCWComplex) :
    Nonempty ((E q).obj (Opposite.op (setup.suspension.obj X)) ≅
      (E (q - 1)).obj (Opposite.op X)) :=
  ⟨suspensionIsoApp q X⟩

end CWReducedCohomologySuspension

/-- Weak-equivalence invariance for a `ℤ`-graded family of contravariant functors on based CW
complexes. -/
class CWReducedCohomologyWeakEquivalenceInvariant
    [CategoryWithWeakEquivalences BasedCWComplex]
    (E : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat) : Prop where
  /-- A weak equivalence of based CW complexes induces an isomorphism in every degree after
  applying the contravariant functor `E q`. -/
  map_isIso :
    ∀ q {X Y : BasedCWComplex} (f : X ⟶ Y) [WeakEquivalence f], IsIso ((E q).map f.op)

/-- Definition 19.2.3: relative to a chosen Chapter 14 based-CW reduced suspension/cofiber setup,
a reduced cohomology theory on based CW complexes is a `ℤ`-graded family of contravariant
functors on the full subcategory of based spaces whose underlying spaces admit CW-complex
structures, satisfying the CW versions of the reduced cohomology axioms. -/
class ReducedCohomologyTheoryOnBasedCWComplexes
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (E : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat) : Prop
    extends CWReducedCohomologyExactness setup E,
      CWReducedCohomologySuspension setup E,
      CWReducedCohomologyWeakEquivalenceInvariant E where
  /-- Each degree functor sends wedges indexed by a discrete type to products. -/
  preservesWedgeProducts :
    ∀ q {ι : Type w}, PreservesLimitsOfShape (Discrete ι) (E q)

namespace ReducedCohomologyTheoryOnBasedCWComplexes

/-- A reduced cohomology theory on based CW complexes determines a chosen natural suspension
isomorphism in each degree. -/
noncomputable abbrev suspensionNatIso
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    {E : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat}
    [ReducedCohomologyTheoryOnBasedCWComplexes setup E]
    (q : ℤ) :
    setup.suspension.op ⋙ E q ≅ E (q - 1) :=
  CWReducedCohomologySuspension.suspensionNatIso q

/-- Applying the chosen suspension isomorphism at `X` gives `(E q)(ΣX) ≅ (E (q - 1))(X)`. -/
noncomputable abbrev suspensionIsoApp
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    {E : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat}
    [ReducedCohomologyTheoryOnBasedCWComplexes setup E]
    (q : ℤ) (X : BasedCWComplex) :
    (E q).obj (Opposite.op (setup.suspension.obj X)) ≅ (E (q - 1)).obj (Opposite.op X) :=
  CWReducedCohomologySuspension.suspensionIsoApp q X

end ReducedCohomologyTheoryOnBasedCWComplexes

/-- A reduced cohomology theory on based CW complexes carries the exactness, suspension, and
weak-equivalence companion owners, while wedge additivity remains available as a field. -/
theorem ReducedCohomologyTheoryOnBasedCWComplexes.spec
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    {E : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat}
    [ReducedCohomologyTheoryOnBasedCWComplexes setup E] :
    CWReducedCohomologyExactness setup E ∧
      CWReducedCohomologySuspension setup E ∧
      CWReducedCohomologyWeakEquivalenceInvariant E :=
  ⟨inferInstance, inferInstance, inferInstance⟩
