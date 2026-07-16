import StacksProject_2024.stacks_project.Chap13.Definition_13_33_1
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import StacksProject_2024.stacks_project.Chap22.CompactDGModule
import StacksProject_2024.stacks_project.Chap22.ShiftedFreeDGModule

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CochainComplex

noncomputable section

universe u v w

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

/-- An object of a chosen model `D` of `D(A, d)` has countable cohomology when each cohomology
module `H^i(M)` has countable underlying type. -/
def hasCountableCohomology {R : Type u} [Ring R] {D : Type v} [Category.{w} D]
    (H : ℤ → D ⥤ ModuleCat R) (M : D) : Prop :=
  ∀ i : ℤ, Countable ((H i).obj M)

@[simp] theorem hasCountableCohomology_iff {R : Type u} [Ring R] {D : Type v} [Category.{w} D]
    (H : ℤ → D ⥤ ModuleCat R) (M : D) :
    hasCountableCohomology H M ↔ ∀ i : ℤ, Countable ((H i).obj M) :=
  Iff.rfl

/-- An object of a category is a sequential homotopy colimit of compact objects if it is the
homotopy colimit of a sequential diagram whose terms satisfy the chosen compactness predicate. -/
def isSequentialHomotopyColimitOfCompactObjects {D : Type v} [Category.{w} D] [HasZeroObject D]
    [Preadditive D] [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
    [Pretriangulated D] (Compact : D → Prop) (M : D) : Prop :=
  ∃ (E : ℕ ⥤ D) (_ : HasCoproduct E.obj),
    (∀ n : ℕ, Compact (E.obj n)) ∧ IsHomotopyColimitOf E M

@[simp] theorem isSequentialHomotopyColimitOfCompactObjects_iff {D : Type v} [Category.{w} D]
    [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] (Compact : D → Prop)
    (M : D) :
    isSequentialHomotopyColimitOfCompactObjects Compact M ↔
      ∃ (E : ℕ ⥤ D) (_ : HasCoproduct E.obj),
        (∀ n : ℕ, Compact (E.obj n)) ∧ IsHomotopyColimitOf E M :=
  Iff.rfl

section

variable {R : Type u} [Ring R]
variable {D : Type v} [Category.{w} D]
variable (H : ℤ → D ⥤ ModuleCat R)
variable (HA : ℤ → ModuleCat R)

/- Source/core/bridge triage:
- `core/canonical`: the generic predicates `hasCountableCohomology` and
  `isSequentialHomotopyColimitOfCompactObjects`, with the Chapter 13 owner
  `CategoryTheory.IsHomotopyColimitOf` for the homotopy-colimit clause;
- `bridge/view`: the countability-transfer lemma below, which turns source cohomology modules
  `HA i = H^i(A)` into countable cohomology for a chosen regular object in a model `D`.
-/

/-- If the chosen regular object `A₀` computes the source cohomology family `HA`, then `A₀` has
countable cohomology whenever each `HA i` is countable. -/
theorem hasCountableCohomology_of_regularObject
    (A₀ : D)
    (hA₀ : ∀ i : ℤ, (H i).obj A₀ ≅ HA i)
    (hA : ∀ i : ℤ, Countable (HA i)) :
    hasCountableCohomology H A₀ := by
  intro i
  simpa using Countable.of_equiv (HA i) (hA₀ i).symm.toLinearEquiv.toEquiv

end

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "homology" =>
  (DerivedCategory.homologyFunctor (ModuleCat A) : ℤ → DMod ⥤ ModuleCat A)

/-- Lemma 22.38.3: let `(A, d)` be a differential graded algebra with `H^i(A)` countable for each
`i`, and let `M` be an object of `D(A, d)`. In the current Chapter 22 model,
`D(A, d)` is `DerivedCategory (ModuleCat A)`, the regular differential graded module `A[0]` is
`DerivedCategory.Q.obj (shiftedFreeDGModule A 0)`, compactness is expressed by preservation of
coproducts by the represented functor `preadditiveCoyoneda.obj (op E)`, and cohomology is
`DerivedCategory.homologyFunctor (ModuleCat A)`. If the cohomology of `A[0]` identifies with the
source cohomology family `HA i = H^i(A)`, then `M` is a sequential homotopy colimit of compact
objects if and only if `H^i(M)` is countable for each `i`. -/
@[stacks 0CRM]
theorem isSequentialHomotopyColimitOfCompactObjects_iff_hasCountableCohomology
    (HA : ℤ → ModuleCat A)
    (hA₀ : ∀ i : ℤ,
      (homology i).obj (DerivedCategory.Q.obj (shiftedFreeDGModule A 0) : DMod) ≅ HA i)
    (hA : ∀ i : ℤ, Countable (HA i))
    (M : DMod) :
    isSequentialHomotopyColimitOfCompactObjects derivedCompactObject M ↔
      hasCountableCohomology homology M := by
  sorry

end

end CategoryTheory
