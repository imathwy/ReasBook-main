import Mathlib.CategoryTheory.CommSq
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_2_3

open CategoryTheory Opposite HomotopicalAlgebra

noncomputable section

universe w

local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

private theorem stableOperationTargetDegree (q n : ℤ) :
    q + n - 1 = (q - 1) + n := by
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

variable [CategoryWithCofibrations BasedCWComplex]
variable [CategoryWithWeakEquivalences BasedCWComplex]

-- Semantic recall: `lean_leansearch` surfaced only generic natural-transformation APIs, not a
-- dedicated cohomology-operation owner. Local Chapter 19 precedent already packages reduced
-- cohomology theories as graded `AddCommGrpCat`-valued functors, so this item is formalized as a
-- degreewise natural transformation together with suspension compatibility.

/-- Definition 22.5.3 (1): for reduced cohomology theories `E` and `F`, a cohomology operation
of type `q` and degree `n` is a natural transformation `E q ⟶ F (q + n)`. -/
abbrev cohomologyOperation
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (E F : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheoryOnBasedCWComplexes setup E]
    [ReducedCohomologyTheoryOnBasedCWComplexes setup F]
    (q n : ℤ) : Type _ :=
  E q ⟶ F (q + n)

/-- Unfolding `cohomologyOperation` recovers the corresponding natural-transformation type. -/
theorem cohomologyOperation_def
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (E F : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheoryOnBasedCWComplexes setup E]
    [ReducedCohomologyTheoryOnBasedCWComplexes setup F]
    (q n : ℤ) :
    cohomologyOperation setup E F q n = (E q ⟶ F (q + n)) := rfl

/-- The chosen suspension isomorphism for `F` in degree `q + n`, rewritten so its target degree
is `F ((q - 1) + n)`. -/
noncomputable abbrev shiftedSuspensionNatIso
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (F : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheoryOnBasedCWComplexes setup F]
    (q n : ℤ) :
    setup.suspension.op ⋙ F (q + n) ≅ F ((q - 1) + n) :=
  ReducedCohomologyTheoryOnBasedCWComplexes.suspensionNatIso (q + n) ≪≫
    eqToIso (congrArg F (stableOperationTargetDegree q n))

/-- Definition 22.5.3 (2): a stable cohomology operation of degree `n` is a sequence of
cohomology operations, one in each type `q`, compatible with the suspension isomorphisms coming
from the chosen suspension isomorphisms determined by the reduced cohomology theories `E` and `F`
on the fixed Chapter 14 based-CW setup `setup`. -/
structure StableCohomologyOperation
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (E F : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheoryOnBasedCWComplexes setup E]
    [ReducedCohomologyTheoryOnBasedCWComplexes setup F]
    (n : ℤ) where
  /-- The degree-`q` component of the stable cohomology operation. -/
  toCohomologyOperation (q : ℤ) :
    cohomologyOperation setup E F q n
  /-- The degree-`q` component commutes with suspension via the chosen suspension isomorphisms
  attached to the reduced cohomology theories `E` and `F`. -/
  suspensionCompatible (q : ℤ) :
    CommSq
      (ReducedCohomologyTheoryOnBasedCWComplexes.suspensionNatIso q).hom
      (Functor.whiskerLeft setup.suspension.op (toCohomologyOperation q))
      (toCohomologyOperation (q - 1))
      (shiftedSuspensionNatIso setup F q n).hom

/-- A stable cohomology operation can be evaluated at each degree `q`. -/
instance stableCohomologyOperationCoeFun
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (E F : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheoryOnBasedCWComplexes setup E]
    [ReducedCohomologyTheoryOnBasedCWComplexes setup F]
    (n : ℤ) :
    CoeFun
      (StableCohomologyOperation setup E F n)
      (fun _ ↦ (q : ℤ) → cohomologyOperation setup E F q n) where
  coe η := η.toCohomologyOperation

/-- Evaluating a stable cohomology operation as a function recovers its degree-`q` component. -/
@[simp] theorem StableCohomologyOperation.coe_apply
    {setup : BasedCWReducedSuspensionCofiberSetup}
    {E F : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat}
    [ReducedCohomologyTheoryOnBasedCWComplexes setup E]
    [ReducedCohomologyTheoryOnBasedCWComplexes setup F]
    {n : ℤ} (η : StableCohomologyOperation setup E F n) (q : ℤ) :
    η q = η.toCohomologyOperation q := rfl

/-- The suspension-compatibility square of a stable cohomology operation as an equality of
composites. -/
theorem StableCohomologyOperation.suspensionCompatible_w
    {setup : BasedCWReducedSuspensionCofiberSetup}
    {E F : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat}
    [ReducedCohomologyTheoryOnBasedCWComplexes setup E]
    [ReducedCohomologyTheoryOnBasedCWComplexes setup F]
    {n : ℤ} (η : StableCohomologyOperation setup E F n) (q : ℤ) :
    (ReducedCohomologyTheoryOnBasedCWComplexes.suspensionNatIso q).hom ≫ η (q - 1) =
      Functor.whiskerLeft setup.suspension.op (η q) ≫
        (shiftedSuspensionNatIso setup F q n).hom :=
  (η.suspensionCompatible q).w
