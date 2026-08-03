import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Data.Int.ModEq
import Mathlib.Data.PNat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_3_theorem_9_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Domain style sampling:
-- * primary domain: kernels of integer linear congruence maps as full-rank sublattices of `ℤ^n`
-- * source-facing owner kept here: the congruence kernel `exercise_9_1_congruence_lattice`
-- * core/canonical owners reused here: `is_primitive_integer_vector`, `Submodule.IsLattice`,
--   and additive-subgroup index

section Exercise91

variable {n : ℕ}

/-- The linear congruence map `x ↦ ∑ i, k_i x_i mod p` used in Exercise 9.1. -/
noncomputable def exercise_9_1_congruence_map
    (k : Fin n → ℤ) (p : ℕ+) :
    (Fin n → ℤ) →ₗ[ℤ] ZMod (p : ℕ) :=
  LinearMap.lsum ℤ (fun _ ↦ ℤ) ℤ fun i ↦
    (k i : ZMod (p : ℕ)) • (Int.castAddHom (ZMod (p : ℕ))).toIntLinearMap

/-- The congruence submodule
`Λ = {x ∈ ℤ^n | ∑ i k_i x_i ≡ 0 mod p}`
from Exercise 9.1. -/
noncomputable def exercise_9_1_congruence_lattice
    (k : Fin n → ℤ) (p : ℕ+) : Submodule ℤ (Fin n → ℤ) :=
  LinearMap.ker (exercise_9_1_congruence_map k p)

/-- The coordinatewise embedding of `ℤ^n` into `ℚ^n`. -/
noncomputable def exercise_9_1_rational_embedding :
    (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) :=
  LinearMap.pi fun i ↦
    (Int.castAddHom ℚ).toIntLinearMap.comp
      (LinearMap.proj i : (Fin n → ℤ) →ₗ[ℤ] ℤ)

/-- The congruence lattice of Exercise 9.1 viewed as a `ℤ`-submodule of `ℚ^n`. -/
noncomputable def exercise_9_1_rational_lattice
    (k : Fin n → ℤ) (p : ℕ+) : Submodule ℤ (Fin n → ℚ) :=
  (exercise_9_1_congruence_lattice k p).map exercise_9_1_rational_embedding

/-- The coordinatewise embedding `ℤ^n → ℚ^n` sends each coordinate to the corresponding rational
number. -/
@[simp] theorem exercise_9_1_rational_embedding_apply
    (x : Fin n → ℤ) (i : Fin n) :
    exercise_9_1_rational_embedding x i = x i := by
  simp [exercise_9_1_rational_embedding]

/-- The coordinatewise embedding `ℤ^n → ℚ^n` is injective. -/
theorem exercise_9_1_rational_embedding_injective :
    Function.Injective (exercise_9_1_rational_embedding : (Fin n → ℤ) → Fin n → ℚ) := by
  intro x y hxy
  ext i
  exact Int.cast_injective <| congrFun hxy i

/-- Membership in `exercise_9_1_rational_lattice k p` is exactly the existence of an integral
congruence vector whose image in `ℚ^n` is the given point. -/
theorem mem_exercise_9_1_rational_lattice_iff
    (k : Fin n → ℤ) (p : ℕ+) (x : Fin n → ℚ) :
    x ∈ exercise_9_1_rational_lattice k p ↔
      ∃ y, y ∈ exercise_9_1_congruence_lattice k p ∧
        exercise_9_1_rational_embedding y = x := by
  change x ∈ (exercise_9_1_congruence_lattice k p).map exercise_9_1_rational_embedding ↔
    ∃ y, y ∈ exercise_9_1_congruence_lattice k p ∧ exercise_9_1_rational_embedding y = x
  exact Submodule.mem_map

/-- Membership in `exercise_9_1_congruence_lattice k p` is exactly the defining congruence
`∑ i k_i x_i ≡ 0 mod p`. -/
theorem mem_exercise_9_1_congruence_lattice_iff
    (k : Fin n → ℤ) (p : ℕ+) (x : Fin n → ℤ) :
    x ∈ exercise_9_1_congruence_lattice k p ↔
      (∑ i, k i * x i) ≡ 0 [ZMOD (p : ℤ)] := sorry

/-- Exercise 9.1 (1). If the integers `k₁, …, kₙ` are relatively prime, equivalently if `k` is a
primitive integer vector, then the congruence set
`Λ = {x ∈ ℤ^n | ∑ i k_i x_i ≡ 0 mod p}` is a lattice. Here the lattice is realized as the
corresponding full-rank `ℤ`-submodule of `ℚ^n`. -/
theorem exercise_9_1_congruence_lattice_is_lattice
    (k : Fin n → ℤ) (p : ℕ+)
    (hprimitive : is_primitive_integer_vector k) :
    Submodule.IsLattice ℚ (exercise_9_1_rational_lattice k p) := sorry

/-- Exercise 9.1 (2). For this full-rank sublattice of `ℤ^n`, the determinant is its index in the
ambient integer lattice; this index is `p`. -/
theorem exercise_9_1_congruence_lattice_index_eq
    (k : Fin n → ℤ) (p : ℕ+)
    (hprimitive : is_primitive_integer_vector k) :
    (exercise_9_1_congruence_lattice k p).toAddSubgroup.index = p := sorry

end Exercise91
