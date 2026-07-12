import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

section

variable {X : Scheme.{u}} [QuasiSeparatedSpace X.carrier]
variable {n : ℕ}

-- Semantic recall: `lean_leansearch` pointed to the quasi-separated / affine-open owners, and the
-- nearby Chapter 28 precedent `Lemma_28_29_1` fixes the source-faithful API here as finite
-- families of irreducible components with explicit chosen generic points.

/-- Lemma 28.29.4: for a quasi-separated scheme `X`, finitely many pairwise distinct irreducible
components with chosen generic points, and an arbitrary point `x : X`, there exists an affine open
subset containing `x` and all of those generic points. -/
theorem exists_affineOpen_containing_point_and_genericPoints_of_pairwiseDistinct_irreducibleComponents
    (x : X) (Z : Fin n → irreducibleComponents X) (η : Fin n → X)
    (hpairwise : Pairwise fun i j ↦ Z i ≠ Z j)
    (hη : ∀ i, IsGenericPoint (η i) (Z i : Set X)) :
    ∃ U : { V : X.Opens // IsAffineOpen V }, x ∈ (U.1 : Set X) ∧ ∀ i, η i ∈ (U.1 : Set X) := sorry

end
