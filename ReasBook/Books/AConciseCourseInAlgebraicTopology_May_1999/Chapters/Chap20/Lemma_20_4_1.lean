import Mathlib.Topology.Sets.Compacts
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.TopCat.Subspace

open AlgebraicTopology

noncomputable section

universe u

-- The source-facing compact-support statement is expressed using the canonical bundled compact
-- subspace owner `TopologicalSpace.Compacts`, the Chapter 20 owner
-- `rSingularHomology R n X` for constant-coefficient singular homology, and the repository's
-- canonical subtype inclusion morphism `TopCat.subtypeInclusion`.

section compactSubspace

variable (R : Type u) [CommRing R]
variable (n : ℕ)
variable {R} {n}
variable {M : Type u} [TopologicalSpace M]

/-- The map on `rSingularHomology` induced by a continuous map `f : X ⟶ Y`. -/
abbrev rSingularHomologyMap (R : Type u) [CommRing R] (n : ℕ) {X Y : TopCat.{u}}
    (f : X ⟶ Y) :
    rSingularHomology R n X ⟶ rSingularHomology R n Y :=
  ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (constantCoefficientModule R)).map f

namespace TopologicalSpace.Compacts

/-- The canonical inclusion `K ⟶ M` of a bundled compact subspace `K ⊆ M`. -/
abbrev inclusion (K : TopologicalSpace.Compacts M) : TopCat.of K ⟶ TopCat.of M :=
  TopCat.subtypeInclusion (K : Set M)

@[simp] theorem inclusion_apply (K : TopologicalSpace.Compacts M) (x : K) :
    K.inclusion.hom x = x :=
  rfl

/-- The map on `rSingularHomology` induced by the inclusion of a compact subspace `K ⊆ M`. -/
abbrev rSingularHomologyInclusion (K : TopologicalSpace.Compacts M) (R : Type u) [CommRing R]
    (n : ℕ) :
    rSingularHomology R n (TopCat.of K) ⟶ rSingularHomology R n (TopCat.of M) :=
  rSingularHomologyMap R n K.inclusion

end TopologicalSpace.Compacts

/-- Lemma 20.4.1: every class in `H_n(M; R)` is induced from a class on some compact subspace of
`M`, via the canonical inclusion-induced map on `rSingularHomology`. -/
theorem exists_compactSubspace_of_rSingularHomologyClass
    (η : rSingularHomology R n (TopCat.of M)) :
    ∃ K : TopologicalSpace.Compacts M,
      ∃ ηK : rSingularHomology R n (TopCat.of K),
        K.rSingularHomologyInclusion R n ηK = η := sorry

end compactSubspace
end
