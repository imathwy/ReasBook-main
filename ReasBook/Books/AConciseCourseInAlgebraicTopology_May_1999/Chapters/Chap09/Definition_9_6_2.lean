import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Topology Topology.Homotopy

variable {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]

-- Semantic recall via `lean_leansearch`: mathlib has a general weak-equivalence typeclass for
-- categories with weak equivalences, but this item needs the source-faithful continuous-map owner
-- built from `IsNEquivalence`.

/-- Definition 9.6.2: a continuous map `e : C(Y, Z)` is a weak equivalence if it is an
`n`-equivalence for every `n : ℕ`. -/
@[mk_iff isWeakEquivalence_iff]
class IsWeakEquivalence (e : C(Y, Z)) : Prop where
  /-- A weak equivalence is an `n`-equivalence in every degree. -/
  isNEquivalence (n : ℕ) : IsNEquivalence n e

/-- A weak equivalence induces an `n`-equivalence for every `n`. -/
instance isNEquivalence_of_isWeakEquivalence (e : C(Y, Z)) [h : IsWeakEquivalence e] (n : ℕ) :
    IsNEquivalence n e :=
  h.isNEquivalence n
