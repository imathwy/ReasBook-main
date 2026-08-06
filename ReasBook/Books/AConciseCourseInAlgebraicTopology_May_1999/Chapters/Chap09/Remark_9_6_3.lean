import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Corollary_9_5_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_2

open scoped ContinuousMap Topology Topology.Homotopy

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

-- Semantic recall via `lean_leansearch`: `ContinuousMap.HomotopyEquiv` is the canonical owner for
-- homotopy equivalences of spaces, and local Chapter 9 already packages the induced bijection on
-- each `π_ q` as `homotopyGroupMap_bijective_of_homotopyEquiv`.

namespace ContinuousMap.HomotopyEquiv

/-- Remark 9.6.3, degreewise form: the forward map of a homotopy equivalence is an
`n`-equivalence for every `n : ℕ`. -/
theorem isNEquivalence (e : X ≃ₕ Y) (n : ℕ) : IsNEquivalence n e.toFun := by
  refine ⟨?_, ?_⟩
  · intro x q hq
    exact (e.bijective_homotopyGroupMap q x).injective
  · intro x q hq
    exact (e.bijective_homotopyGroupMap q x).surjective

/-- Remark 9.6.3: every homotopy equivalence is a weak equivalence. Concretely, if
`e : X ≃ₕ Y`, then the forward map `e.toFun : C(X, Y)` is an `n`-equivalence for every
`n : ℕ`, hence a weak equivalence. The converse direction is not asserted here; later source
remarks require extra hypotheses such as CW conditions. -/
theorem isWeakEquivalence (e : X ≃ₕ Y) : IsWeakEquivalence e.toFun := by
  refine ⟨?_⟩
  intro n
  exact e.isNEquivalence n

/-- Typeclass form of Remark 9.6.3 for the forward map of a homotopy equivalence. -/
instance instIsWeakEquivalence (e : X ≃ₕ Y) : IsWeakEquivalence e.toFun :=
  e.isWeakEquivalence

end ContinuousMap.HomotopyEquiv
