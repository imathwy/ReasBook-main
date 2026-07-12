import StacksProject_2024.Chap22.Proposition_22_36_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape DerivedCategory

noncomputable section

universe u

namespace CochainComplex

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "Q" => (DerivedCategory.Q : DGMod ⥤ DMod)

/-- The differential graded module `M` has vanishing cohomology on the interval `[a, b]`. -/
def cohomologyVanishesOn (M : DGMod) (a b : ℤ) : Prop :=
  ∀ i ∈ Set.Icc a b, IsZero (M.homology i)

theorem cohomologyVanishesOn_iff (M : DGMod) (a b : ℤ) :
    cohomologyVanishesOn M a b ↔
      ∀ i : ℤ, a ≤ i → i ≤ b → IsZero (M.homology i) := by
  simp [cohomologyVanishesOn, Set.mem_Icc]

/-- For a fixed interval `[a, b]`, every morphism `E ⟶ Q.obj M` vanishes once the cohomology of
`M` vanishes on that interval. -/
def homVanishesOnWindow (E : DMod) (M : DGMod) (a b : ℤ) : Prop :=
  cohomologyVanishesOn M a b → ∀ f : E ⟶ Q.obj M, f = 0

theorem homVanishesOnWindow.eq_zero {E : DMod} {M : DGMod} {a b : ℤ}
    (h : homVanishesOnWindow E M a b) (hM : cohomologyVanishesOn M a b) (f : E ⟶ Q.obj M) :
    f = 0 :=
  h hM f

/- Semantic recall: local Section 22.36 precedent uses `DMod := DerivedCategory (ModuleCat A)`
and `derivedCompactObject` for compactness, while Proposition `22.36.4` provides the canonical
bridge through `IsRetractOfFiniteCellDGModule`. -/

/-- Lemma 22.36.5: for every compact object `E` of `D(A, d)` there are integers `a ≤ b`
such that every map from `E` to a differential graded module whose cohomology vanishes in the
window `[a,b]` is zero. -/
@[stacks 09RA]
theorem hom_vanishes_of_compact_of_cohomology_vanishes_on_interval
    (E : DMod)
    (hE : derivedCompactObject E) :
    ∃ a b, a ≤ b ∧ ∀ {M : DGMod}, homVanishesOnWindow E M a b := by
  sorry

/-- Proposition `22.36.4` rephrases the compactness hypothesis in Lemma `22.36.5` as the finite
cell retract property. This bridge keeps the source-facing interval-vanishing conclusion available
from that chapter-level owner directly. -/
theorem hom_vanishes_of_retract_finiteCellDGModule_of_cohomology_vanishes_on_interval
    (E : DMod) (hE : IsRetractOfFiniteCellDGModule E) :
    ∃ a b, a ≤ b ∧ ∀ {M : DGMod}, homVanishesOnWindow E M a b := by
  exact hom_vanishes_of_compact_of_cohomology_vanishes_on_interval E
    (derivedCompactObject_of_isRetractOfFiniteCellDGModule hE)

end CochainComplex
