import Mathlib
import SmoothManifolds_Lee_2012.Chap08.Sec08_63.Problem_8_19
import SmoothManifolds_Lee_2012.Chap08.Sec08_63.Problem_8_29

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix
open LieAlgebra.Orthogonal

noncomputable section

-- Semantic recall note: `lean_leansearch` was unavailable in this runner, so the `su(2)` owner
-- is reused from Problem 8.29 as `special_unitary_matrix_lie_subalgebra 2`, while the `o(3)`
-- owner is reused directly from mathlib as `LieAlgebra.Orthogonal.so (Fin 3) ℝ`.
-- Domain sampling pass:
-- * primary domain: explicit Lie algebra equivalences from the cross-product Lie algebra on `ℝ^3`
--   to classical matrix Lie algebras;
-- * source-facing layer: the explicit matrix parametrizations from `ℝ^3` into `su(2)` and `o(3)`;
-- * core/canonical owners: `Cross.lieRing` and `Cross.lieAlgebra` on `Fin 3 → ℝ`,
--   `special_unitary_matrix_lie_subalgebra 2`, and `LieAlgebra.Orthogonal.so (Fin 3) ℝ`;
-- * bridge/view layer: the induced `LieHom`s and `LieEquiv`s built from those explicit matrix
--   formulas;
-- * primitive data: the explicit matrix-valued linear maps;
-- * derived API: membership, Lie-bracket compatibility, bijectivity, and the resulting
--   equivalences.

local notation "su₂" => special_unitary_matrix_lie_subalgebra 2
local notation "o₃" => so (Fin 3) ℝ
local notation "R3" => Fin 3 → ℝ

attribute [local instance] Cross.lieRing Cross.lieAlgebra

/-- The first normalized Pauli-type basis matrix for the explicit `su(2)` identification. -/
private def problem_8_30_su2_basis_x : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), (1 / 2 : ℂ); -(1 / 2 : ℂ), (0 : ℂ)]

/-- The second normalized Pauli-type basis matrix for the explicit `su(2)` identification. -/
private def problem_8_30_su2_basis_y : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), ((1 / 2 : ℝ) : ℂ) * Complex.I; ((1 / 2 : ℝ) : ℂ) * Complex.I, (0 : ℂ)]

/-- The third normalized Pauli-type basis matrix for the explicit `su(2)` identification. -/
private def problem_8_30_su2_basis_z : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1 / 2 : ℝ) : ℂ) * Complex.I, (0 : ℂ); (0 : ℂ), -(((1 / 2 : ℝ) : ℂ) * Complex.I)]

/-- The explicit matrix-valued linear map from `ℝ^3` to the standard `su(2)` basis. -/
def problem_8_30_cross_to_su2_matrix : R3 →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (LinearMap.proj 0).smulRight problem_8_30_su2_basis_x +
    (LinearMap.proj 1).smulRight problem_8_30_su2_basis_y +
      (LinearMap.proj 2).smulRight problem_8_30_su2_basis_z

/-- Coordinate formula for `problem_8_30_cross_to_su2_matrix`. -/
theorem problem_8_30_cross_to_su2_matrix_apply (u : R3) :
    problem_8_30_cross_to_su2_matrix u =
      !![(u 2 / 2 : ℂ) * Complex.I, (u 0 / 2 : ℂ) + (u 1 / 2 : ℂ) * Complex.I;
        -(u 0 / 2 : ℂ) + (u 1 / 2 : ℂ) * Complex.I, -((u 2 / 2 : ℂ) * Complex.I)] := sorry

/-- The explicit `su(2)` matrix attached to `u : ℝ^3` lies in `su₂`. -/
theorem problem_8_30_cross_to_su2_matrix_mem (u : R3) :
    problem_8_30_cross_to_su2_matrix u ∈ su₂ := sorry

private def crossToSu2Linear : R3 →ₗ[ℝ] su₂ :=
  problem_8_30_cross_to_su2_matrix.codRestrict su₂
    problem_8_30_cross_to_su2_matrix_mem

private theorem crossToSu2Linear_map_lie (u v : R3) :
    crossToSu2Linear ⁅u, v⁆ = ⁅crossToSu2Linear u, crossToSu2Linear v⁆ := sorry

/-- The explicit Lie algebra homomorphism from `ℝ^3` with the cross product to `su(2)`. -/
def problem_8_30_cross_to_su2_hom : R3 →ₗ⁅ℝ⁆ su₂ :=
  { toLinearMap := crossToSu2Linear
    map_lie' := fun {u v} ↦ crossToSu2Linear_map_lie u v }

/-- Forgetting the subtype on `problem_8_30_cross_to_su2_hom` recovers the explicit matrix
formula. -/
theorem problem_8_30_cross_to_su2_hom_apply (u : R3) :
    ((problem_8_30_cross_to_su2_hom u : su₂) :
      Matrix (Fin 2) (Fin 2) ℂ) = problem_8_30_cross_to_su2_matrix u := sorry

/-- The explicit `su(2)` parametrization is bijective. -/
theorem problem_8_30_cross_to_su2_hom_bijective :
    Function.Bijective problem_8_30_cross_to_su2_hom := sorry

/-- The standard basis matrix in `o(3)` corresponding to rotation about the first coordinate axis.
-/
private def problem_8_30_o3_basis_x : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(0 : ℝ), 0, 0; 0, 0, -1; 0, 1, 0]

/-- The standard basis matrix in `o(3)` corresponding to rotation about the second coordinate axis.
-/
private def problem_8_30_o3_basis_y : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(0 : ℝ), 0, 1; 0, 0, 0; -1, 0, 0]

/-- The standard basis matrix in `o(3)` corresponding to rotation about the third coordinate axis.
-/
private def problem_8_30_o3_basis_z : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(0 : ℝ), -1, 0; 1, 0, 0; 0, 0, 0]

/-- The explicit matrix-valued linear map from `ℝ^3` to the standard `o(3)` basis. -/
def problem_8_30_cross_to_o3_matrix : R3 →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ :=
  (LinearMap.proj 0).smulRight problem_8_30_o3_basis_x +
    (LinearMap.proj 1).smulRight problem_8_30_o3_basis_y +
      (LinearMap.proj 2).smulRight problem_8_30_o3_basis_z

/-- Coordinate formula for `problem_8_30_cross_to_o3_matrix`. -/
theorem problem_8_30_cross_to_o3_matrix_apply (u : R3) :
    problem_8_30_cross_to_o3_matrix u =
      !![(0 : ℝ), -u 2, u 1; u 2, 0, -u 0; -u 1, u 0, 0] := sorry

/-- The explicit `o(3)` matrix attached to `u : ℝ^3` lies in `o₃`. -/
theorem problem_8_30_cross_to_o3_matrix_mem (u : R3) :
    problem_8_30_cross_to_o3_matrix u ∈ o₃ := sorry

private def crossToO3Linear : R3 →ₗ[ℝ] o₃ :=
  problem_8_30_cross_to_o3_matrix.codRestrict o₃
    problem_8_30_cross_to_o3_matrix_mem

private theorem crossToO3Linear_map_lie (u v : R3) :
    crossToO3Linear ⁅u, v⁆ = ⁅crossToO3Linear u, crossToO3Linear v⁆ := sorry

/-- The explicit Lie algebra homomorphism from `ℝ^3` with the cross product to `o(3)`. -/
def problem_8_30_cross_to_o3_hom : R3 →ₗ⁅ℝ⁆ o₃ :=
  { toLinearMap := crossToO3Linear
    map_lie' := fun {u v} ↦ crossToO3Linear_map_lie u v }

/-- Forgetting the subtype on `problem_8_30_cross_to_o3_hom` recovers the explicit matrix
formula. -/
theorem problem_8_30_cross_to_o3_hom_apply (u : R3) :
    ((problem_8_30_cross_to_o3_hom u : o₃) :
      Matrix (Fin 3) (Fin 3) ℝ) = problem_8_30_cross_to_o3_matrix u := sorry

/-- The explicit `o(3)` parametrization is bijective. -/
theorem problem_8_30_cross_to_o3_hom_bijective :
    Function.Bijective problem_8_30_cross_to_o3_hom := sorry

/-- Problem 8-30 (1): the normalized Pauli-matrix parametrization gives an explicit Lie algebra
equivalence from `ℝ^3` with the cross product to `su(2)`. -/
def problem_8_30_cross_equiv_su2 : R3 ≃ₗ⁅ℝ⁆ su₂ :=
  LieEquiv.ofBijective problem_8_30_cross_to_su2_hom problem_8_30_cross_to_su2_hom_bijective

/-- Applying `problem_8_30_cross_equiv_su2` recovers the explicit `su(2)` matrix formula. -/
theorem problem_8_30_cross_equiv_su2_apply (u : R3) :
    ((problem_8_30_cross_equiv_su2 u : su₂) :
      Matrix (Fin 2) (Fin 2) ℂ) = problem_8_30_cross_to_su2_matrix u := sorry

/-- Problem 8-30 (2): the standard skew-symmetric matrix parametrization gives an explicit Lie
algebra equivalence from `ℝ^3` with the cross product to `o(3)`. -/
def problem_8_30_cross_equiv_o3 : R3 ≃ₗ⁅ℝ⁆ o₃ :=
  LieEquiv.ofBijective problem_8_30_cross_to_o3_hom problem_8_30_cross_to_o3_hom_bijective

/-- Applying `problem_8_30_cross_equiv_o3` recovers the explicit `o(3)` matrix formula. -/
theorem problem_8_30_cross_equiv_o3_apply (u : R3) :
    ((problem_8_30_cross_equiv_o3 u : o₃) :
      Matrix (Fin 3) (Fin 3) ℝ) = problem_8_30_cross_to_o3_matrix u := sorry

/-- Problem 8-30 (3): composing the two explicit identifications with `ℝ^3` yields an explicit
Lie algebra equivalence between `su(2)` and `o(3)`. -/
def problem_8_30_su2_equiv_o3 : su₂ ≃ₗ⁅ℝ⁆ o₃ :=
  problem_8_30_cross_equiv_su2.symm.trans problem_8_30_cross_equiv_o3

/-- Applying `problem_8_30_su2_equiv_o3` sends an `su(2)` element to the corresponding explicit
`o(3)` matrix. -/
theorem problem_8_30_su2_equiv_o3_apply (A : su₂) :
    ((problem_8_30_su2_equiv_o3 A : o₃) : Matrix (Fin 3) (Fin 3) ℝ) =
      problem_8_30_cross_to_o3_matrix (problem_8_30_cross_equiv_su2.symm A) := sorry
