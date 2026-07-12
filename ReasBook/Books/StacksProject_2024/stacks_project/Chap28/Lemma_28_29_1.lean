import Mathlib.AlgebraicGeometry.AffineScheme

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

section

variable {X : Scheme.{u}} [QuasiSeparatedSpace X.carrier]
variable {n : ℕ}

-- Semantic recall: `lean_leansearch` suggested the canonical affine-open union API
-- `AlgebraicGeometry.IsAffineOpen.iSup_of_disjoint`. The source-facing main entries here quantify
-- over opens `U : X.Opens` with explicit `IsAffineOpen U`, while bundled `X.affineOpens`
-- companions provide the reusable packaged view downstream.

/-- Lemma 28.29.1 (1): for finitely many pairwise distinct irreducible components of a
quasi-separated scheme `X`, together with chosen generic points on those components, there exist
affine open neighborhoods of the generic points that are pairwise disjoint. -/
theorem exists_pairwiseDisjoint_affineOpenNeighborhoods_genericPoints_of_pairwiseDistinct_irreducibleComponents
    (Z : Fin n → irreducibleComponents X) (η : Fin n → X)
    (hpairwise : Pairwise fun i j ↦ Z i ≠ Z j)
    (hη : ∀ i, IsGenericPoint (η i) (Z i : Set X)) :
    ∃ U : Fin n → X.Opens,
      (∀ i, IsAffineOpen (U i)) ∧
        (∀ i, η i ∈ (U i : Set X)) ∧ Pairwise (fun i j ↦ Disjoint (U i) (U j)) := sorry

/-- Companion packaging of Lemma 28.29.1 (1) through the affine-open subtype. -/
theorem exists_pairwiseDisjoint_affineOpenNeighborhoods_genericPoints_of_pairwiseDistinct_irreducibleComponents_affineOpens
    (Z : Fin n → irreducibleComponents X) (η : Fin n → X)
    (hpairwise : Pairwise fun i j ↦ Z i ≠ Z j)
    (hη : ∀ i, IsGenericPoint (η i) (Z i : Set X)) :
    ∃ U : Fin n → X.affineOpens,
      (∀ i, η i ∈ ((U i : X.Opens) : Set X)) ∧
        Pairwise (fun i j ↦ Disjoint (U i : X.Opens) (U j : X.Opens)) := sorry

/-- Lemma 28.29.1 (2): for finitely many pairwise distinct irreducible components of a
quasi-separated scheme `X`, together with chosen generic points on those components, there exists
an affine open subset containing all of those generic points. -/
theorem exists_affineOpen_containing_genericPoints_of_pairwiseDistinct_irreducibleComponents
    (Z : Fin n → irreducibleComponents X) (η : Fin n → X)
    (hpairwise : Pairwise fun i j ↦ Z i ≠ Z j)
    (hη : ∀ i, IsGenericPoint (η i) (Z i : Set X)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, η i ∈ (U : Set X) := sorry

/-- Companion packaging of Lemma 28.29.1 (2) through the affine-open subtype. -/
theorem exists_affineOpen_containing_genericPoints_of_pairwiseDistinct_irreducibleComponents_affineOpens
    (Z : Fin n → irreducibleComponents X) (η : Fin n → X)
    (hpairwise : Pairwise fun i j ↦ Z i ≠ Z j)
    (hη : ∀ i, IsGenericPoint (η i) (Z i : Set X)) :
    ∃ U : X.affineOpens, ∀ i, η i ∈ ((U : X.Opens) : Set X) := sorry

end
