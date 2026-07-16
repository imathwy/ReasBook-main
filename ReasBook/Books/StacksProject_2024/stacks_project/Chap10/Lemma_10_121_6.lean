import StacksProject_2024.stacks_project.Chap10.Definition_10_121_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] [Ring.KrullDimLE 1 R]
variable [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

namespace Submodule

variable (M M' : Submodule R V)

-- Proof sketch: unfold `latticeDistance`; both quotient-length terms are identical when the two
-- lattices agree, so the integer difference is zero.
/-- The distance from a lattice to itself is zero. -/
theorem latticeDistance_self [IsLattice K M] :
    latticeDistance M M = 0 := sorry

variable (M'' : Submodule R V)

-- Proof sketch: choose a lattice contained in all three lattices, rewrite each distance as the
-- difference of two finite lengths relative to that common sublattice, and use additivity of
-- module length in short exact sequences to telescope the resulting expression.
/-- Lemma 10.121.6: for lattices `M`, `M'`, and `M''` in a finite-dimensional `K`-vector space
over a one-dimensional Noetherian local domain `R`, the lattice distance is additive:
`d(M, M'') = d(M, M') + d(M', M'')`. The canonical ambient hypothesis is
`[Ring.KrullDimLE 1 R]`. -/
theorem latticeDistance_add [IsLattice K M] [IsLattice K M'] [IsLattice K M'']
    : latticeDistance M M'' = latticeDistance M M' + latticeDistance M' M'' := sorry

-- Proof sketch: unfold `latticeDistance`; swapping `M` and `M'` exchanges the two quotient-length
-- terms, so the defining integer difference changes sign.
/-- Swapping the two lattices negates the lattice distance. -/
theorem latticeDistance_neg_swap [IsLattice K M] [IsLattice K M'] :
    latticeDistance M M' = - latticeDistance M' M := sorry

end Submodule

end
