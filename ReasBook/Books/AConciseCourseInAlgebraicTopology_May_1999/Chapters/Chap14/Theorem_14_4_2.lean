import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Definition_14_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_1

open CategoryTheory Limits
open HomotopicalAlgebra

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` did not surface a canonical library owner for this
-- equivalence. Following the local Chapter 19 dual precedent, this file fixes one reduced
-- suspension/cofiber setup and bundles the reduced side around `ReducedHomologyTheory`.

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "NBasedSpace" => nondegeneratelyBasedSpace

/-- The source-facing type of pair homology theories together with their coefficient group. -/
abbrev PairHomologyTheoryWithCoefficients : Type _ :=
  Σ π : Type u, Σ _ : AddCommGroup π, PairHomologyTheory π

/-- The coefficient group of a bundled pair homology theory. -/
abbrev PairHomologyTheoryWithCoefficients.coefficients
    (H : PairHomologyTheoryWithCoefficients) : Type u :=
  H.1

/-- The packaged coefficient group of a bundled pair homology theory carries its additive-group
structure. -/
instance instAddCommGroupCoefficientsOfPairHomologyTheoryWithCoefficients
    (H : PairHomologyTheoryWithCoefficients) :
    AddCommGroup H.coefficients :=
  H.2.1

/-- The underlying pair homology theory of a bundled coefficient-theory pair. -/
abbrev PairHomologyTheoryWithCoefficients.theory
    (H : PairHomologyTheoryWithCoefficients) :
    PairHomologyTheory H.coefficients :=
  H.2.2

/-- A reduced homology theory on nondegenerately based spaces, bundled as a graded family of
functors together with the `ReducedHomologyTheory` predicate from Definition 14.4.1. -/
abbrev ReducedHomologyTheoryOnNondegeneratelyBasedSpaces
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup) :=
  { E : ℤ → NBasedSpace ⥤ AddCommGrpCat.{u} //
      ReducedHomologyTheory.{u, u} setup E }

/-- The underlying graded functor of a bundled reduced homology theory. -/
abbrev ReducedHomologyTheoryOnNondegeneratelyBasedSpaces.homology
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (E : ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup) :
    ℤ → NBasedSpace ⥤ AddCommGrpCat.{u} :=
  E.1

/-- A bundled reduced homology theory carries the Definition 14.4.1 axioms on its underlying
graded functor. -/
instance reducedHomologyTheoryOnNondegeneratelyBasedSpacesToReducedHomologyTheory
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (E : ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup) :
    ReducedHomologyTheory.{u, u} setup E.homology :=
  E.2

/-- A bundled reduced homology theory is determined by its underlying graded functor together
with the Definition 14.4.1 axioms. -/
theorem ReducedHomologyTheoryOnNondegeneratelyBasedSpaces.spec
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (E : ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup) :
    ReducedHomologyTheory.{u, u} setup E.1 :=
  E.2

/-- Theorem 14.4.2: homology theories on pairs of spaces determine and are determined by reduced
homology theories on nondegenerately based spaces. For a chosen reduced suspension/cofiber setup
`setup` from Definition 14.4.1, the pair side is packaged as
`PairHomologyTheoryWithCoefficients`, while the reduced side is packaged as
`ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup`, namely
`{ E : ℤ → NBasedSpace ⥤ AddCommGrpCat.{u} //
    ReducedHomologyTheory.{u, u} setup E }`. -/
theorem pairHomologyTheoryEquivReducedHomologyTheory
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup) :
    Nonempty
      (PairHomologyTheoryWithCoefficients ≃
        ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup) := sorry

/-- Any explicit equivalence between the pair-side and reduced-side theories yields the expected
forward and backward transport identities on the underlying carriers. -/
theorem pairHomologyTheoryEquivReducedHomologyTheory_explicit
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (equivalence :
      PairHomologyTheoryWithCoefficients ≃
        ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup) :
    (∀ E : PairHomologyTheoryWithCoefficients, equivalence.symm (equivalence E) = E) ∧
      ∀ E : ReducedHomologyTheoryOnNondegeneratelyBasedSpaces setup,
        equivalence (equivalence.symm E) = E := by
  exact ⟨equivalence.left_inv, equivalence.right_inv⟩
