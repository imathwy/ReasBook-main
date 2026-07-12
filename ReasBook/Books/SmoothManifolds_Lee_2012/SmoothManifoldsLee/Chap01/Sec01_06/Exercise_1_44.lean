import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

open scoped Manifold ContDiff

universe uK uE uH uM

section

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H}

namespace ModelWithCorners

/-- The manifold interior of `M`, regarded as its canonical open submanifold. -/
abbrev interiorOpens (I : ModelWithCorners 𝕜 E H) (M : Type uM) [TopologicalSpace M]
    [ChartedSpace H M] {n : ℕ∞ω} [IsManifold I n M] (hn : n ≠ 0) : Opens M :=
  ⟨I.interior M, I.isOpen_interior hn⟩

end ModelWithCorners

/- Exercise 1.44 (1): an open subset of a smooth manifold with boundary inherits the same
manifold-with-boundary structure. This is the canonical mathlib instance
`TopologicalSpace.Opens.instIsManifold`. -/
example {n : ℕ∞ω} [IsManifold I n M] (U : Opens M) : IsManifold I n U := inferInstance

/- Exercise 1.44 (2): the preferred charts on an open subset are the restrictions of the ambient
preferred charts. This is the canonical `TopologicalSpace.Opens.chartAt_eq` lemma. -/
example (U : Opens M) (x : U) : chartAt H x = (chartAt H x.1).subtypeRestr ⟨x⟩ :=
  U.chartAt_eq

/-- Exercise 1.44 (3): if an open subset lies in the manifold interior, then it is a manifold
without boundary. -/
theorem open_subset_of_interior_boundaryless (U : Opens M) (hU : (U : Set M) ⊆ I.interior M) :
    BoundarylessManifold I U where
  isInteriorPoint' x := I.isInteriorPoint_iff_isInteriorPoint_val.2 (hU x.2)

/-- Exercise 1.44 (4): the manifold interior of `M` is itself an open submanifold without
boundary. -/
theorem manifoldInterior_boundaryless {n : ℕ∞ω} [IsManifold I n M] (hn : n ≠ 0) :
    BoundarylessManifold I (I.interiorOpens M hn) :=
  open_subset_of_interior_boundaryless (I.interiorOpens M hn) fun _ hx ↦ hx

end
