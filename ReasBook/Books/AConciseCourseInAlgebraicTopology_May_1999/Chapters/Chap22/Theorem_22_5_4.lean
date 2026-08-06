import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_5_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Construction_22_3_3

open CategoryTheory Opposite
open HomotopicalAlgebra

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

-- Semantic recall: `lean_leansearch` surfaced no verified additive representability owner for
-- cohomology operations. Chapter 22 already fixes the explicit representation datum
-- `ReducedCohomologyEilenbergMacLaneRepresentation`, so this item is stated directly on that
-- source-facing surface.

variable [CategoryWithCofibrations BasedSpace]
variable [CategoryWithCofibrations BasedCWComplex]
variable [CategoryWithWeakEquivalences BasedCWComplex]
variable {π : Type} [AddCommGroup π] {q : ℕ}

/-- The degree-`q + n` reduced cohomology group of the source representing space carried by `R`,
computed using a target reduced theory `E` on the same setup. -/
noncomputable abbrev reducedCohomologyGroupOfRepresentingSpace
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π q)
    (E : BundledReducedCohomologyTheory R.setup) (n : ℕ) :
    AddCommGrpCat :=
  (E.cohomology ((q : ℤ) + n)).obj (op R.basedCWComplex)

/-- A based map `f : X ⟶ K(π, q)` is classifying for `x ∈ H̃^q(X; π)` if its based-homotopy
class is the image of `x` under the representability comparison carried by `R`. -/
def IsClassifyingMap
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π q) {X : BasedCWComplexᵒᵖ}
    (x : (R.theory.cohomology (q : ℤ)).obj X) :
    (X.unop.obj ⟶ R.space) → Prop :=
  fun f ↦
    ((reducedCohomology_isRepresentedByAdditiveEilenbergMacLaneSpace R).hom.app X).toFun x =
      Quotient.mk (basedHomotopySetoid X.unop.obj R.space) f

/-- The fundamental class on the source representing space is classified by the identity
self-map of that representing space. -/
theorem fundamentalCohomologyClass_isClassifyingMap
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π q) :
    IsClassifyingMap R (fundamentalCohomologyClass R) (𝟙 R.space) := by
  simpa [IsClassifyingMap] using fundamentalCohomologyClass_spec R

/-- Pulling back `u ∈ H̃^(q + n)(K(π, q); E)` along a based map `f : X ⟶ K(π, q)` yields the
value of the induced cohomology operation on the classifying map `f`. -/
noncomputable def cohomologyOperationValueOfClassifyingMap
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π q)
    (E : BundledReducedCohomologyTheory R.setup) (n : ℕ)
    (u : reducedCohomologyGroupOfRepresentingSpace R E n) {X : BasedCWComplexᵒᵖ}
    (f : X.unop.obj ⟶ R.space) :
    (E.cohomology ((q : ℤ) + n)).obj X :=
  let f' : X.unop ⟶ R.basedCWComplex := CategoryTheory.ObjectProperty.homMk f
  (eqToHom
    (congrArg
      (fun Y ↦ (E.cohomology ((q : ℤ) + n)).obj Y)
      (Opposite.op_unop X)))
    (((E.cohomology ((q : ℤ) + n)).map f'.op) u)

/-- Based-homotopic classifying maps induce the same pullback of the representing class `u`. -/
private theorem cohomologyOperationValueOfClassifyingMap_eq_of_basedHomotopy
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π q)
    (E : BundledReducedCohomologyTheory R.setup) (n : ℕ)
    (u : reducedCohomologyGroupOfRepresentingSpace R E n) {X : BasedCWComplexᵒᵖ}
    {f g : X.unop.obj ⟶ R.space} (hfg : (basedHomotopySetoid X.unop.obj R.space).r f g) :
    cohomologyOperationValueOfClassifyingMap R E n u f =
      cohomologyOperationValueOfClassifyingMap R E n u g := by
  sorry

/-- Evaluating the cohomology operation induced by `u` on a class `x ∈ H̃^q(X; π)` can be done
using any based map classifying `x`. -/
noncomputable def cohomologyOperationOfRepresentingClassApp
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π q)
    (E : BundledReducedCohomologyTheory R.setup) (n : ℕ)
    (u : reducedCohomologyGroupOfRepresentingSpace R E n) {X : BasedCWComplexᵒᵖ} :
    (R.theory.cohomology (q : ℤ)).obj X →
      (E.cohomology ((q : ℤ) + n)).obj X :=
  fun x ↦
    let xClass :=
      ((reducedCohomology_isRepresentedByAdditiveEilenbergMacLaneSpace R).app X).hom.toFun x
    Quotient.lift
      (fun f : X.unop.obj ⟶ R.space ↦ cohomologyOperationValueOfClassifyingMap R E n u f)
      (fun _ _ hfg ↦ cohomologyOperationValueOfClassifyingMap_eq_of_basedHomotopy R E n u hfg)
      xClass

/-- The quotient-level evaluation map attached to `u` agrees with pullback along any classifying
map for the input class. -/
theorem cohomologyOperationOfRepresentingClassApp_apply_of_classifyingMap
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π q)
    (E : BundledReducedCohomologyTheory R.setup) (n : ℕ)
    (u : reducedCohomologyGroupOfRepresentingSpace R E n) {X : BasedCWComplexᵒᵖ}
    (x : (R.theory.cohomology (q : ℤ)).obj X) {f : X.unop.obj ⟶ R.space}
    (hf : IsClassifyingMap R x f) :
    cohomologyOperationOfRepresentingClassApp R E n u x =
      cohomologyOperationValueOfClassifyingMap R E n u f := by
  dsimp [cohomologyOperationOfRepresentingClassApp]
  rw [hf]
  rfl

/-- A class in `H̃^(q + n)(K(π, q); ρ)` induces a cohomology operation
`H̃^q(-; π) → H̃^(q + n)(-; ρ)` by pulling back along classifying maps of each cohomology class. -/
noncomputable def cohomologyOperationOfRepresentingClass
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π q)
    (E : BundledReducedCohomologyTheory R.setup) (n : ℕ)
    (u : reducedCohomologyGroupOfRepresentingSpace R E n) :
    cohomologyOperation R.setup R.theory.cohomology E.cohomology (q : ℤ) (n : ℤ) :=
  { app := fun X ↦
      AddCommGrpCat.ofHom <|
        AddMonoidHom.mk'
          (cohomologyOperationOfRepresentingClassApp R E n u)
          sorry
    naturality := sorry }

/-- Evaluating `cohomologyOperationOfRepresentingClass R E n u` on a classifying map recovers the
pullback of `u` along that classifying map. -/
theorem cohomologyOperationOfRepresentingClass_apply_of_classifyingMap
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π q)
    (E : BundledReducedCohomologyTheory R.setup) (n : ℕ)
    (u : reducedCohomologyGroupOfRepresentingSpace R E n) {X : BasedCWComplexᵒᵖ}
    (x : (R.theory.cohomology (q : ℤ)).obj X) {f : X.unop.obj ⟶ R.space}
    (hf : IsClassifyingMap R x f) :
    (cohomologyOperationOfRepresentingClass R E n u).app X x =
      cohomologyOperationValueOfClassifyingMap R E n u f := by
  simpa [cohomologyOperationOfRepresentingClass] using
    cohomologyOperationOfRepresentingClassApp_apply_of_classifyingMap R E n u x hf

/-- Theorem 22.5.4. Given an explicit degree-`q` representing space for reduced cohomology with
coefficients in `π` and a target reduced theory `E` on the same setup, cohomology operations
`H̃^q(-; π) → H̃^(q + n)(-; E)` correspond bijectively to classes in
`H̃^(q + n)(K(π, q); E)`. -/
noncomputable def cohomologyOperation_equiv_reducedCohomologyGroupOfRepresentingSpace
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π q)
    (E : BundledReducedCohomologyTheory R.setup) (n : ℕ) :
    cohomologyOperation R.setup R.theory.cohomology E.cohomology (q : ℤ) (n : ℤ) ≃
      reducedCohomologyGroupOfRepresentingSpace R E n :=
  { toFun := fun η ↦
      η.app (op R.basedCWComplex)
        (fundamentalCohomologyClass R)
    invFun := fun u ↦ cohomologyOperationOfRepresentingClass R E n u
    left_inv := sorry
    right_inv := sorry }

/-- Evaluating the equivalence of Theorem 22.5.4 on a cohomology operation recovers its value on
the fundamental class of the source representing space carried by `R`. -/
@[simp] theorem cohomologyOperation_equiv_reducedCohomologyGroupOfRepresentingSpace_apply
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π q)
    (E : BundledReducedCohomologyTheory R.setup) (n : ℕ)
    (η : cohomologyOperation R.setup R.theory.cohomology E.cohomology (q : ℤ) (n : ℤ)) :
    cohomologyOperation_equiv_reducedCohomologyGroupOfRepresentingSpace R E n η =
      η.app (op R.basedCWComplex)
        (fundamentalCohomologyClass R) := sorry

/-- The inverse equivalence of Theorem 22.5.4 sends a representing class to the induced
cohomology operation obtained by pullback along classifying maps. -/
@[simp] theorem cohomologyOperation_equiv_reducedCohomologyGroupOfRepresentingSpace_symm_apply
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π q)
    (E : BundledReducedCohomologyTheory R.setup) (n : ℕ)
    (u : reducedCohomologyGroupOfRepresentingSpace R E n) :
    (cohomologyOperation_equiv_reducedCohomologyGroupOfRepresentingSpace R E n).symm u =
      cohomologyOperationOfRepresentingClass R E n u := sorry
