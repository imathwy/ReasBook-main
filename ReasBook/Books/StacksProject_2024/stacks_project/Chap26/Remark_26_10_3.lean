import Mathlib.Algebra.Field.ULift
import StacksProject_2024.stacks_project.Chap29.Example_29_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: Chapter 29 already owns the counterexample structure
-- `ImmersionNotOpenThenClosed` together with the factorization predicate
-- `Scheme.Hom.HasOpenThenClosedFactorization`. This remark is the thin bridge from that explicit
-- counterexample to the existential formulation stated in Chapter 26.

section

variable {k : Type u} [Field k] {Z : Scheme.{u}} {i : Z ⟶ example2934U k}

/-- Any Chapter 29 counterexample of type `ImmersionNotOpenThenClosed` yields the existential
counterexample promised in Remark 26.10.3. -/
theorem ImmersionNotOpenThenClosed.existsImmersionNotFactorableAsOpenThenClosed
    (h : ImmersionNotOpenThenClosed k Z i) :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y),
      IsImmersion f ∧ ¬ f.HasOpenThenClosedFactorization := by
  refine ⟨Z, example2934X k, i ≫ example2934ι k, h.isImmersion_comp, ?_⟩
  exact h.not_hasOpenThenClosedFactorization

end

/- Remark 26.10.3: there exist schemes `X` and `Y` and an immersion `f : X ⟶ Y` such that `f`
cannot be factored as an open immersion followed by a closed immersion. -/
@[stacks 01IP]
theorem existsImmersionNotFactorableAsOpenThenClosed :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y),
      IsImmersion f ∧ ¬ f.HasOpenThenClosedFactorization := by
  let _ : Field (ULift.{u} ℚ) := ULift.field
  obtain ⟨Z, i, hi⟩ := example2934ExistsImmersionNotOpenThenClosed (ULift.{u} ℚ)
  exact hi.existsImmersionNotFactorableAsOpenThenClosed

/-- Remark 26.10.3, expanded into the explicit existential factorization failure. -/
@[stacks 01IP]
theorem existsImmersion_not_exists_openThenClosedFactorization :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y),
      IsImmersion f ∧
        ¬ (∃ (middle : Scheme.{u}) (openMap : X ⟶ middle) (closedMap : middle ⟶ Y),
            IsOpenImmersion openMap ∧
              IsClosedImmersion closedMap ∧
              (openMap ≫ closedMap) = f) := by
  let _ : Field (ULift.{u} ℚ) := ULift.field
  obtain ⟨Z, i, hi⟩ := example2934ExistsImmersionNotOpenThenClosed (ULift.{u} ℚ)
  refine ⟨Z, example2934X (ULift.{u} ℚ), i ≫ example2934ι (ULift.{u} ℚ), hi.isImmersion_comp, ?_⟩
  exact hi.not_exists_openThenClosedFactorization

end AlgebraicGeometry
