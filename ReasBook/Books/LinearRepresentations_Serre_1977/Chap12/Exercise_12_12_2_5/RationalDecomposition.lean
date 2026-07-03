import Mathlib
import Serre.Chap12.Corollary_12_12_2_2
import Serre.Chap12.Exercise_12_12_2_5.QuaternionicSchurModel

noncomputable section

open scoped MonoidAlgebra Quaternion TensorProduct

universe u v w

namespace Representation

section

local notation "Q8" => QuaternionGroup 2

/-- Helper for Exercise 12-12.2-5: the four rational linear characters of `Q8`, indexed so that
their values on the conjugacy classes `{±1}, {±i}, {±j}, {±k}` are the Walsh-Hadamard sign
patterns `(1, 1, 1, 1)`, `(1, 1, -1, -1)`, `(1, -1, 1, -1)`, and `(1, -1, -1, 1)`. -/
def quaternion_group_two_rational_linear_character_family (n : Fin 4) : Q8 →* ℚ where
  toFun
    | QuaternionGroup.a i =>
        match n.1, i.val with
        | 0, _ => 1
        | 1, _ => 1
        | 2, 0 => 1
        | 2, 1 => -1
        | 2, 2 => 1
        | 2, _ => -1
        | _, 0 => 1
        | _, 1 => -1
        | _, 2 => 1
        | _, _ => -1
    | QuaternionGroup.xa i =>
        match n.1, i.val with
        | 0, _ => 1
        | 1, _ => -1
        | 2, 0 => 1
        | 2, 1 => -1
        | 2, 2 => 1
        | 2, _ => -1
        | _, 0 => -1
        | _, 1 => 1
        | _, 2 => -1
        | _, _ => 1
  map_one' := by
    -- The source identity is `a 0`, and every linear character takes value `1` on it.
    fin_cases n <;> rfl
  map_mul' := by
    rintro (i | i) (j | j)
    -- Route correction: package the four scalar factors by a complete finite multiplication
    -- check on the explicit eight-element quaternion table, just as for the Hamilton embedding.
    · fin_cases n <;> fin_cases i <;> fin_cases j <;> native_decide
    · fin_cases n <;> fin_cases i <;> fin_cases j <;> native_decide
    · fin_cases n <;> fin_cases i <;> fin_cases j <;> native_decide
    · fin_cases n <;> fin_cases i <;> fin_cases j <;> native_decide

/-- Helper for Exercise 12-12.2-5: each rational linear character of `Q8` extends to an algebra
map `ℚ[Q8] → ℚ` by the universal property of the monoid algebra. -/
def quaternion_group_two_rational_linear_character_algHom (n : Fin 4) :
    ℚ[Q8] →ₐ[ℚ] ℚ :=
  MonoidAlgebra.lift ℚ ℚ Q8 (quaternion_group_two_rational_linear_character_family n)

/-- Helper for Exercise 12-12.2-5: on a basis element `single g r`, the `n`-th rational linear
character contributes the expected scalar `r χₙ(g)`. -/
theorem quaternion_group_two_rational_linear_character_algHom_single
    (n : Fin 4) (g : Q8) (r : ℚ) :
    quaternion_group_two_rational_linear_character_algHom n (Finsupp.single g r) =
      r * quaternion_group_two_rational_linear_character_family n g := by
  -- This is the defining computation rule for `MonoidAlgebra.lift`.
  simpa [quaternion_group_two_rational_linear_character_algHom, smul_eq_mul] using
    (MonoidAlgebra.lift_single
      (quaternion_group_two_rational_linear_character_family n) g r)

/-- Helper for Exercise 12-12.2-5: the four scalar linear characters together with the explicit
quaternion quotient define the rational comparison map from `ℚ[Q8]` to Serre's proposed simple
product. -/
def quaternion_group_two_rational_comparison_algHom :
    ℚ[Q8] →ₐ[ℚ] ℚ × ℚ × ℚ × ℚ × ℍ[ℚ] :=
  (quaternion_group_two_rational_linear_character_algHom 0).prod
    ((quaternion_group_two_rational_linear_character_algHom 1).prod
      ((quaternion_group_two_rational_linear_character_algHom 2).prod
        ((quaternion_group_two_rational_linear_character_algHom 3).prod
          quaternionGroupTwoGroupAlgebraToQuaternion)))

/-- Helper for Exercise 12-12.2-5: on a basis element `single g r`, the rational comparison map
records the four scalar character values together with the quaternion image of `g`. -/
theorem quaternion_group_two_rational_comparison_algHom_single
    (g : Q8) (r : ℚ) :
    quaternion_group_two_rational_comparison_algHom (Finsupp.single g r) =
      ((r * quaternion_group_two_rational_linear_character_family 0 g,
        r * quaternion_group_two_rational_linear_character_family 1 g,
        r * quaternion_group_two_rational_linear_character_family 2 g,
        r * quaternion_group_two_rational_linear_character_family 3 g,
        r • ((quaternionGroupTwoToQuaternionUnits g : Units ℍ[ℚ]) : ℍ[ℚ])) :
          ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
  -- Unfold the product map and apply the single-basis computation rule in each slot.
  simp [quaternion_group_two_rational_comparison_algHom,
    quaternion_group_two_rational_linear_character_algHom_single,
    quaternionGroupTwoGroupAlgebraToQuaternion_single, smul_eq_mul]

/-- Helper for Exercise 12-12.2-5: the normalized class sum supported on `{±1}`. -/
def quaternion_group_two_class_sum_one : ℚ[Q8] :=
  Finsupp.single (1 : Q8) (1 / 2 : ℚ) +
    Finsupp.single (QuaternionGroup.a (2 : ZMod 4)) (1 / 2 : ℚ)

/-- Helper for Exercise 12-12.2-5: the normalized class sum supported on `{±i}`. -/
def quaternion_group_two_class_sum_i : ℚ[Q8] :=
  Finsupp.single (QuaternionGroup.a (1 : ZMod 4)) (1 / 2 : ℚ) +
    Finsupp.single (QuaternionGroup.a (3 : ZMod 4)) (1 / 2 : ℚ)

/-- Helper for Exercise 12-12.2-5: the normalized class sum supported on `{±j}`. -/
def quaternion_group_two_class_sum_j : ℚ[Q8] :=
  Finsupp.single (QuaternionGroup.xa (0 : ZMod 4)) (1 / 2 : ℚ) +
    Finsupp.single (QuaternionGroup.xa (2 : ZMod 4)) (1 / 2 : ℚ)

/-- Helper for Exercise 12-12.2-5: the normalized class sum supported on `{±k}`. -/
def quaternion_group_two_class_sum_k : ℚ[Q8] :=
  Finsupp.single (QuaternionGroup.xa (3 : ZMod 4)) (1 / 2 : ℚ) +
    Finsupp.single (QuaternionGroup.xa (1 : ZMod 4)) (1 / 2 : ℚ)

/-- Helper for Exercise 12-12.2-5: the normalized sign-pair difference supported on `1 - (-1)`. -/
def quaternion_group_two_class_difference_one : ℚ[Q8] :=
  Finsupp.single (1 : Q8) (1 / 2 : ℚ) +
    Finsupp.single (QuaternionGroup.a (2 : ZMod 4)) (-(1 / 2 : ℚ))

/-- Helper for Exercise 12-12.2-5: the normalized sign-pair difference supported on `i - (-i)`. -/
def quaternion_group_two_class_difference_i : ℚ[Q8] :=
  Finsupp.single (QuaternionGroup.a (1 : ZMod 4)) (1 / 2 : ℚ) +
    Finsupp.single (QuaternionGroup.a (3 : ZMod 4)) (-(1 / 2 : ℚ))

/-- Helper for Exercise 12-12.2-5: the normalized sign-pair difference supported on `j - (-j)`. -/
def quaternion_group_two_class_difference_j : ℚ[Q8] :=
  Finsupp.single (QuaternionGroup.xa (0 : ZMod 4)) (1 / 2 : ℚ) +
    Finsupp.single (QuaternionGroup.xa (2 : ZMod 4)) (-(1 / 2 : ℚ))

/-- Helper for Exercise 12-12.2-5: the normalized sign-pair difference supported on `k - (-k)`. -/
def quaternion_group_two_class_difference_k : ℚ[Q8] :=
  Finsupp.single (QuaternionGroup.xa (3 : ZMod 4)) (1 / 2 : ℚ) +
    Finsupp.single (QuaternionGroup.xa (1 : ZMod 4)) (-(1 / 2 : ℚ))

/-- Helper for Exercise 12-12.2-5: the four normalized class sums map to the Walsh-Hadamard
rows in the scalar block, while their quaternion coordinates vanish. -/
theorem quaternion_group_two_rational_comparison_class_sum_images :
    quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_sum_one =
      ((1, 1, 1, 1, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) ∧
    quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_sum_i =
      ((1, 1, -1, -1, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) ∧
    quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_sum_j =
      ((1, -1, 1, -1, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) ∧
    quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_sum_k =
      ((1, -1, -1, 1, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
  have h_one :
      quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_sum_one =
        ((1, 1, 1, 1, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
    -- Expand the `{±1}` class sum into two basis elements and evaluate each summand explicitly.
    rw [quaternion_group_two_class_sum_one]
    calc
      quaternion_group_two_rational_comparison_algHom
          (Finsupp.single (1 : Q8) (1 / 2 : ℚ) +
            Finsupp.single (QuaternionGroup.a (2 : ZMod 4)) (1 / 2 : ℚ)) =
          quaternion_group_two_rational_comparison_algHom (Finsupp.single (1 : Q8) (1 / 2 : ℚ)) +
            quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.a (2 : ZMod 4)) (1 / 2 : ℚ)) := by
            exact quaternion_group_two_rational_comparison_algHom.map_add _ _
      _ = ((1, 1, 1, 1, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
            rw [quaternion_group_two_rational_comparison_algHom_single,
              quaternion_group_two_rational_comparison_algHom_single]
            ext <;> native_decide
  have h_i :
      quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_sum_i =
        ((1, 1, -1, -1, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
    -- Expand the `{±i}` class sum and read off the second Walsh-Hadamard row.
    rw [quaternion_group_two_class_sum_i]
    calc
      quaternion_group_two_rational_comparison_algHom
          (Finsupp.single (QuaternionGroup.a (1 : ZMod 4)) (1 / 2 : ℚ) +
            Finsupp.single (QuaternionGroup.a (3 : ZMod 4)) (1 / 2 : ℚ)) =
          quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.a (1 : ZMod 4)) (1 / 2 : ℚ)) +
            quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.a (3 : ZMod 4)) (1 / 2 : ℚ)) := by
            exact quaternion_group_two_rational_comparison_algHom.map_add _ _
      _ = ((1, 1, -1, -1, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
            rw [quaternion_group_two_rational_comparison_algHom_single,
              quaternion_group_two_rational_comparison_algHom_single]
            ext <;> native_decide
  have h_j :
      quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_sum_j =
        ((1, -1, 1, -1, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
    -- Expand the `{±j}` class sum and read off the third Walsh-Hadamard row.
    rw [quaternion_group_two_class_sum_j]
    calc
      quaternion_group_two_rational_comparison_algHom
          (Finsupp.single (QuaternionGroup.xa (0 : ZMod 4)) (1 / 2 : ℚ) +
            Finsupp.single (QuaternionGroup.xa (2 : ZMod 4)) (1 / 2 : ℚ)) =
          quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.xa (0 : ZMod 4)) (1 / 2 : ℚ)) +
            quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.xa (2 : ZMod 4)) (1 / 2 : ℚ)) := by
            exact quaternion_group_two_rational_comparison_algHom.map_add _ _
      _ = ((1, -1, 1, -1, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
            rw [quaternion_group_two_rational_comparison_algHom_single,
              quaternion_group_two_rational_comparison_algHom_single]
            ext <;> native_decide
  have h_k :
      quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_sum_k =
        ((1, -1, -1, 1, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
    -- Expand the `{±k}` class sum and read off the fourth Walsh-Hadamard row.
    rw [quaternion_group_two_class_sum_k]
    calc
      quaternion_group_two_rational_comparison_algHom
          (Finsupp.single (QuaternionGroup.xa (3 : ZMod 4)) (1 / 2 : ℚ) +
            Finsupp.single (QuaternionGroup.xa (1 : ZMod 4)) (1 / 2 : ℚ)) =
          quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.xa (3 : ZMod 4)) (1 / 2 : ℚ)) +
            quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.xa (1 : ZMod 4)) (1 / 2 : ℚ)) := by
            exact quaternion_group_two_rational_comparison_algHom.map_add _ _
      _ = ((1, -1, -1, 1, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
            rw [quaternion_group_two_rational_comparison_algHom_single,
              quaternion_group_two_rational_comparison_algHom_single]
            ext <;> native_decide
  exact ⟨h_one, h_i, h_j, h_k⟩

/-- Helper for Exercise 12-12.2-5: the four normalized sign-pair differences have zero scalar
coordinates and recover the quaternion basis `1, i, j, k`. -/
theorem quaternion_group_two_rational_comparison_class_difference_images :
    quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_difference_one =
      ((0, 0, 0, 0, (1 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) ∧
    quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_difference_i =
      ((0, 0, 0, 0, rationalQuaternionBasis.i) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) ∧
    quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_difference_j =
      ((0, 0, 0, 0, rationalQuaternionBasis.j) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) ∧
    quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_difference_k =
      ((0, 0, 0, 0, rationalQuaternionBasis.k) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
  have h_one :
      quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_difference_one =
        ((0, 0, 0, 0, (1 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
    -- Expand `1 - (-1)` and evaluate the two source basis elements independently.
    rw [quaternion_group_two_class_difference_one]
    calc
      quaternion_group_two_rational_comparison_algHom
          (Finsupp.single (1 : Q8) (1 / 2 : ℚ) +
            Finsupp.single (QuaternionGroup.a (2 : ZMod 4)) (-(1 / 2 : ℚ))) =
          quaternion_group_two_rational_comparison_algHom (Finsupp.single (1 : Q8) (1 / 2 : ℚ)) +
            quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.a (2 : ZMod 4)) (-(1 / 2 : ℚ))) := by
            exact quaternion_group_two_rational_comparison_algHom.map_add _ _
      _ = ((0, 0, 0, 0, (1 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
            rw [quaternion_group_two_rational_comparison_algHom_single,
              quaternion_group_two_rational_comparison_algHom_single]
            ext <;> native_decide
  have h_i :
      quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_difference_i =
        ((0, 0, 0, 0, rationalQuaternionBasis.i) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
    -- Expand `i - (-i)` and recover the quaternion basis vector `i`.
    rw [quaternion_group_two_class_difference_i]
    calc
      quaternion_group_two_rational_comparison_algHom
          (Finsupp.single (QuaternionGroup.a (1 : ZMod 4)) (1 / 2 : ℚ) +
            Finsupp.single (QuaternionGroup.a (3 : ZMod 4)) (-(1 / 2 : ℚ))) =
          quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.a (1 : ZMod 4)) (1 / 2 : ℚ)) +
            quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.a (3 : ZMod 4)) (-(1 / 2 : ℚ))) := by
            exact quaternion_group_two_rational_comparison_algHom.map_add _ _
      _ = ((0, 0, 0, 0, rationalQuaternionBasis.i) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
            rw [quaternion_group_two_rational_comparison_algHom_single,
              quaternion_group_two_rational_comparison_algHom_single]
            ext <;> native_decide
  have h_j :
      quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_difference_j =
        ((0, 0, 0, 0, rationalQuaternionBasis.j) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
    -- Expand `j - (-j)` and recover the quaternion basis vector `j`.
    rw [quaternion_group_two_class_difference_j]
    calc
      quaternion_group_two_rational_comparison_algHom
          (Finsupp.single (QuaternionGroup.xa (0 : ZMod 4)) (1 / 2 : ℚ) +
            Finsupp.single (QuaternionGroup.xa (2 : ZMod 4)) (-(1 / 2 : ℚ))) =
          quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.xa (0 : ZMod 4)) (1 / 2 : ℚ)) +
            quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.xa (2 : ZMod 4)) (-(1 / 2 : ℚ))) := by
            exact quaternion_group_two_rational_comparison_algHom.map_add _ _
      _ = ((0, 0, 0, 0, rationalQuaternionBasis.j) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
            rw [quaternion_group_two_rational_comparison_algHom_single,
              quaternion_group_two_rational_comparison_algHom_single]
            ext <;> native_decide
  have h_k :
      quaternion_group_two_rational_comparison_algHom quaternion_group_two_class_difference_k =
        ((0, 0, 0, 0, rationalQuaternionBasis.k) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
    -- Expand `k - (-k)` and recover the quaternion basis vector `k`.
    rw [quaternion_group_two_class_difference_k]
    calc
      quaternion_group_two_rational_comparison_algHom
          (Finsupp.single (QuaternionGroup.xa (3 : ZMod 4)) (1 / 2 : ℚ) +
            Finsupp.single (QuaternionGroup.xa (1 : ZMod 4)) (-(1 / 2 : ℚ))) =
          quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.xa (3 : ZMod 4)) (1 / 2 : ℚ)) +
            quaternion_group_two_rational_comparison_algHom
              (Finsupp.single (QuaternionGroup.xa (1 : ZMod 4)) (-(1 / 2 : ℚ))) := by
            exact quaternion_group_two_rational_comparison_algHom.map_add _ _
      _ = ((0, 0, 0, 0, rationalQuaternionBasis.k) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
            rw [quaternion_group_two_rational_comparison_algHom_single,
              quaternion_group_two_rational_comparison_algHom_single]
            ext <;> native_decide
  exact ⟨h_one, h_i, h_j, h_k⟩

/-- Helper for Exercise 12-12.2-5: the four normalized class sums invert the scalar block of the
rational comparison map by the Walsh-Hadamard change of basis. -/
theorem quaternion_group_two_scalar_block_preimage
    (s0 s1 s2 s3 : ℚ) :
    quaternion_group_two_rational_comparison_algHom
        (((s0 + s1 + s2 + s3) / 4 : ℚ) • quaternion_group_two_class_sum_one +
          ((s0 + s1 - s2 - s3) / 4 : ℚ) • quaternion_group_two_class_sum_i +
          ((s0 - s1 + s2 - s3) / 4 : ℚ) • quaternion_group_two_class_sum_j +
          ((s0 - s1 - s2 + s3) / 4 : ℚ) • quaternion_group_two_class_sum_k) =
      ((s0, s1, s2, s3, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
  rcases quaternion_group_two_rational_comparison_class_sum_images with ⟨h_one, h_i, h_j, h_k⟩
  -- Expand along the four normalized class sums and solve the Walsh-Hadamard linear system.
  ext <;>
    simp [map_add, h_one, h_i, h_j, h_k] <;>
    ring

/-- Helper for Exercise 12-12.2-5: the four normalized sign-pair differences invert the
quaternion block of the rational comparison map by reading the coordinates of `q`. -/
theorem quaternion_group_two_quaternion_block_preimage
    (q : ℍ[ℚ]) :
    quaternion_group_two_rational_comparison_algHom
        (q.re • quaternion_group_two_class_difference_one +
          q.imI • quaternion_group_two_class_difference_i +
          q.imJ • quaternion_group_two_class_difference_j +
          q.imK • quaternion_group_two_class_difference_k) =
      ((0, 0, 0, 0, q) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
  rcases quaternion_group_two_rational_comparison_class_difference_images with
    ⟨h_one, h_i, h_j, h_k⟩
  -- Expand along the four normalized sign-pair differences and reassemble the quaternion
  -- coordinates in the basis `1, i, j, k`.
  ext <;>
    simp [map_add, h_one, h_i, h_j, h_k, rationalQuaternionBasis] <;>
    ring

/-- Helper for Exercise 12-12.2-5: the rational comparison map is surjective. The proof uses the
class sums `{±1}, {±i}, {±j}, {±k}` to control the four scalar slots and the corresponding class
differences to recover the quaternion coordinates independently. -/
theorem quaternion_group_two_rational_comparison_surjective :
    Function.Surjective quaternion_group_two_rational_comparison_algHom := by
  rintro ⟨s0, s1, s2, s3, q⟩
  let xScalar : ℚ[Q8] :=
    ((s0 + s1 + s2 + s3) / 4 : ℚ) • quaternion_group_two_class_sum_one +
      ((s0 + s1 - s2 - s3) / 4 : ℚ) • quaternion_group_two_class_sum_i +
      ((s0 - s1 + s2 - s3) / 4 : ℚ) • quaternion_group_two_class_sum_j +
      ((s0 - s1 - s2 + s3) / 4 : ℚ) • quaternion_group_two_class_sum_k
  let xQuaternion : ℚ[Q8] :=
    q.re • quaternion_group_two_class_difference_one +
      q.imI • quaternion_group_two_class_difference_i +
      q.imJ • quaternion_group_two_class_difference_j +
      q.imK • quaternion_group_two_class_difference_k
  have h_scalar :
      quaternion_group_two_rational_comparison_algHom xScalar =
        ((s0, s1, s2, s3, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
    -- The normalized class sums solve the scalar block independently of the quaternion block.
    unfold xScalar
    simpa using quaternion_group_two_scalar_block_preimage s0 s1 s2 s3
  have h_quaternion :
      quaternion_group_two_rational_comparison_algHom xQuaternion =
        ((0, 0, 0, 0, q) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
    -- The normalized sign-pair differences solve the quaternion block independently.
    unfold xQuaternion
    simpa using quaternion_group_two_quaternion_block_preimage q
  refine ⟨xScalar + xQuaternion, ?_⟩
  -- The scalar and quaternion preimages land in complementary blocks, so their sum hits the
  -- required five-tuple exactly.
  calc
    quaternion_group_two_rational_comparison_algHom (xScalar + xQuaternion) =
        quaternion_group_two_rational_comparison_algHom xScalar +
          quaternion_group_two_rational_comparison_algHom xQuaternion := by
            simp
    _ = ((s0, s1, s2, s3, (0 : ℍ[ℚ])) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) +
          ((0, 0, 0, 0, q) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
            rw [h_scalar, h_quaternion]
    _ = ((s0, s1, s2, s3, q) : ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
          ext <;> simp

end

end Representation
