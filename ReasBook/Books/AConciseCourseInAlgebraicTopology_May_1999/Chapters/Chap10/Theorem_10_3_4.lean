import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.HomotopyClasses
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_4_4

open Function Set
open scoped Topology Topology.Homotopy

universe u

-- Chapter 7 already owns the canonical quotient `continuousMapHomotopyClasses X Y` and the
-- induced postcomposition map `continuousMapHomotopyClassesPostcompose`. This file keeps the
-- Chapter 10 source-facing theorem names around that canonical owner.

section

variable {X Y Z : Type u}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Postcomposition with `e : C(Y, Z)` respects ordinary homotopy classes of maps out of `X`. -/
theorem homotopyClassesPostcompose_wellDefined (e : C(Y, Z)) {f₀ f₁ : C(X, Y)}
    (h : ContinuousMap.Homotopic f₀ f₁) :
    ContinuousMap.Homotopic (e.comp f₀) (e.comp f₁) := by
  simpa using ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl e) h

/-- Postcomposition by `e : C(Y, Z)` induces the map `e_* : [X,Y] → [X,Z]`. -/
abbrev homotopyClassesPostcompose (X : Type u) [TopologicalSpace X] (e : C(Y, Z)) :
    continuousMapHomotopyClasses X Y → continuousMapHomotopyClasses X Z :=
  continuousMapHomotopyClassesPostcompose e

@[simp] theorem homotopyClassesPostcompose_mk (e : C(Y, Z)) (f : C(X, Y)) :
    homotopyClassesPostcompose X e ⟦f⟧ = (⟦e.comp f⟧ : continuousMapHomotopyClasses X Z) :=
  rfl

end

section

variable {X Y Z : Type u}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable [Topology.CWComplex (Set.univ : Set X)]

/-- Theorem 10.3.4 (1): if `X` is a CW complex of dimension less than `n`, expressed as
`Topology.RelCWComplex.dimLE (Set.univ : Set X) m` for some `m < n`, and `e : C(Y, Z)` is an
`n`-equivalence, then the induced map `e_* : [X,Y] → [X,Z]` is bijective. -/
theorem homotopyClassesPostcompose_bijective_of_dimLE_of_lt_of_isNEquivalence
    (m n : ℕ) (h_dim : Topology.RelCWComplex.dimLE (Set.univ : Set X) m) (hmn : m < n)
    (e : C(Y, Z)) [IsNEquivalence n e] :
    Function.Bijective (homotopyClassesPostcompose X e) := sorry

/-- Theorem 10.3.4 (2), in its canonical sharpened form: if `X` has CW dimension at most `n`
and `e : C(Y, Z)` is an `n`-equivalence, then the induced map `e_* : [X,Y] → [X,Z]` is
surjective. In particular, this applies to the source case `dim X = n`. -/
theorem homotopyClassesPostcompose_surjective_of_dimLE_of_isNEquivalence
    (n : ℕ) (h_dim : Topology.RelCWComplex.dimLE (Set.univ : Set X) n) (e : C(Y, Z))
    [IsNEquivalence n e] :
    Function.Surjective (homotopyClassesPostcompose X e) := sorry

end
