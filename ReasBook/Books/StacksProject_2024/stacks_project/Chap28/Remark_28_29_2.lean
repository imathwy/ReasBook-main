import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

-- Semantic recall: this counterexample is most useful downstream when phrased using the canonical
-- owners `irreducibleComponents X`, `IsGenericPoint`, and affine opens `U : X.Opens`.
-- `lean_leansearch` also recalled `AlgebraicGeometry.quasiSeparatedSpace_iff_affine` as the
-- canonical background API for the missing quasi-separatedness hypothesis.

/-- A choice of two generic points on distinct irreducible components of a scheme `X` for which
no affine open subset of `X` contains both points. -/
class GenericPointsWithoutCommonAffineOpen
    (X : Scheme) (Z : Fin 2 → irreducibleComponents X) (η : Fin 2 → X) : Prop where
  /-- The ambient scheme is not quasi-separated. -/
  not_quasiSeparated : ¬ QuasiSeparatedSpace X.carrier
  /-- The chosen irreducible components are distinct. -/
  pairwise : Pairwise (fun i j ↦ Z i ≠ Z j)
  /-- Each chosen point is generic in the corresponding irreducible component. -/
  isGenericPoint : ∀ i, IsGenericPoint (η i) (Z i : Set X)
  /-- No affine open subset of `X` contains both chosen generic points. -/
  no_common_affineOpen : ¬ ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, η i ∈ U

/-- Remark 28.29.2: there exists a non-quasi-separated scheme `X` with two generic points on
distinct irreducible components such that no affine open subset of `X` contains both points.
Equivalently, Lemma 28.29.1 fails without the quasi-separatedness hypothesis. -/
theorem exists_nonQuasiSeparated_scheme_with_genericPoints_not_in_common_affineOpen :
    ∃ X : Scheme,
      ∃ Z : Fin 2 → irreducibleComponents X,
        ∃ η : Fin 2 → X, GenericPointsWithoutCommonAffineOpen X Z η := sorry
