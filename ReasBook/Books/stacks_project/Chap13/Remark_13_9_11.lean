import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomologicalComplex
open CochainComplex

local notation "Cpx" => CochainComplex AddCommGrpCat ℤ

/- Domain-style sampling:
- primary domain: cochain complexes, degreewise split short complexes, and homotopy-category
  commutative squares;
- relevant owner declarations inspected:
  `ShortComplex.map`,
  `HomologicalComplex.eval`,
  `ShortComplex.Splitting`,
  `ShortComplex.Hom`,
  `exists_rightMap_eq_in_homotopyCategory_of_termwiseSplitMono`,
  `exists_leftMap_eq_in_homotopyCategory_of_termwiseSplitEpi`,
  `comp_eq_zero_in_homotopyCategory_of_termwiseSplit`;
- best owner abstraction: the rows are canonically `ShortComplex` objects, while their termwise
  split exactness is the Chapter `13` owner existence property
  `∀ n, Nonempty ((S.map (eval AddCommGrpCat (up ℤ) n)).Splitting)`
  rather than chosen public splitting data; the homotopy-category compatibility data are
  canonically `CommSq`, while any strict replacement should be expressed by the row-morphism owner
  `ShortComplex.Hom` with fixed outer components rather than by a bespoke package of two squares;
- source/core/bridge triage:
  `source-facing`: the existence of a counterexample to strictifying a homotopy-commutative
    diagram between termwise split exact sequences of cochain complexes;
  `core/canonical`: `ShortComplex`, degreewise `ShortComplex.Splitting`, `CommSq`, and
    `ShortComplex.Hom`;
  `bridge/view`: equality in the homotopy category via the quotient functor `Q`.

Primitive data here is the pair of short complexes and the three vertical maps between their
terms. The termwise split condition is a genuine existence property and should therefore stay as
`Nonempty`-valued degreewise splitness rather than exposing a chosen family of splittings. The
homotopy-commutativity assumptions are expressed directly through `CommSq`, while the claim that a
strict replacement exists is expressed by the canonical owner `S₁ ⟶ S₂` together with fixed outer
components and equality of the middle quotient class, without packaging them into local wrapper
structures.
-/

-- Proof sketch: use the counterexample from Examples, Equation `(110.64.0.1)`, whose two rows are
-- degreewise split short exact sequences of complexes and whose outer squares commute only in the
-- homotopy category. If a homotopic replacement `b'` of the middle map existed making both
-- squares commute strictly, the induced trace computation would become additive, contradicting the
-- example.
/-- Remark 13.9.11: there exists a counterexample in `AddCommGrpCat` showing that a morphism
between the middle terms of two termwise split exact sequences of cochain complexes cannot in
general be replaced by a homotopic morphism making the homotopy-commutative diagram strictly
commutative in the category of complexes. -/
theorem exists_termwiseSplit_counterexample_to_middleMap_strictification :
    let Q := HomotopyCategory.quotient AddCommGrpCat (up ℤ)
    ∃ (S₁ S₂ : ShortComplex Cpx) (a : S₁.X₁ ⟶ S₂.X₁) (b : S₁.X₂ ⟶ S₂.X₂)
      (c : S₁.X₃ ⟶ S₂.X₃),
      (∀ n : ℤ, Nonempty ((S₁.map (eval AddCommGrpCat (up ℤ) n)).Splitting)) ∧
      (∀ n : ℤ, Nonempty ((S₂.map (eval AddCommGrpCat (up ℤ) n)).Splitting)) ∧
      CommSq (Q.map S₁.f) (Q.map a) (Q.map b) (Q.map S₂.f) ∧
      CommSq (Q.map S₁.g) (Q.map b) (Q.map c) (Q.map S₂.g) ∧
      ¬ ∃ φ : S₁ ⟶ S₂, φ.τ₁ = a ∧ φ.τ₃ = c ∧ Q.map φ.τ₂ = Q.map b := sorry
