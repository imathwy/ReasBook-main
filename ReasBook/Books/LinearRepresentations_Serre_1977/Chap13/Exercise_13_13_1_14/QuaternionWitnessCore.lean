import LinearRepresentations_Serre_1977.Chap13.Exercise_13_13_1_14.Obstruction

noncomputable section

open scoped Representation
open scoped Quaternion

namespace Representation

section

local notation "Q8" => QuaternionGroup 2
local notation "C3" => Multiplicative (ZMod 3)
local notation "G0" => Q8 × C3

local instance : Fintype Q8 := inferInstance
local instance : Fintype C3 := inferInstance
local instance : DecidableEq Q8 := inferInstance
local instance : DecidableEq C3 := inferInstance
local instance : Finite G0 := inferInstance
local instance : Fintype G0 := inferInstance
local instance : DecidableEq G0 := inferInstance
local instance : DecidableEq ℍ[ℚ] := by
  intro a b
  by_cases hre : a.re = b.re
  · by_cases himI : a.imI = b.imI
    · by_cases himJ : a.imJ = b.imJ
      · by_cases himK : a.imK = b.imK
        · exact isTrue (by ext <;> assumption)
        · exact isFalse (by
            intro h
            exact himK (congrArg QuaternionAlgebra.imK h))
      · exact isFalse (by
          intro h
          exact himJ (congrArg QuaternionAlgebra.imJ h))
    · exact isFalse (by
        intro h
        exact himI (congrArg QuaternionAlgebra.imI h))
  · exact isFalse (by
      intro h
      exact hre (congrArg QuaternionAlgebra.re h))
local instance : DecidableEq (Units ℍ[ℚ]) := fun a b =>
  if h : (a : ℍ[ℚ]) = (b : ℍ[ℚ]) then
    isTrue (Units.ext h)
  else
    isFalse fun hab ↦ h (congrArg Units.val hab)

/-- Helper for Exercise 13-13.1-14: the standard Hamilton basis on the rational quaternion
algebra `ℍ[ℚ]`. -/
def rational_quaternion_basis :
    QuaternionAlgebra.Basis ℍ[ℚ] (-1 : ℚ) 0 (-1 : ℚ) :=
  QuaternionAlgebra.Basis.self ℚ

/-- Helper for Exercise 13-13.1-14: the Hamilton basis element `i` squares to `-1`. -/
theorem rational_quaternion_i_sq :
    (rational_quaternion_basis.i : ℍ[ℚ]) * rational_quaternion_basis.i = (-1 : ℍ[ℚ]) := by
  -- This is the defining Hamilton relation in the chosen basis.
  simpa [rational_quaternion_basis] using rational_quaternion_basis.i_mul_i

/-- Helper for Exercise 13-13.1-14: the Hamilton basis element `j` squares to `-1`. -/
theorem rational_quaternion_j_sq :
    (rational_quaternion_basis.j : ℍ[ℚ]) * rational_quaternion_basis.j = (-1 : ℍ[ℚ]) := by
  -- This is the second Hamilton relation in the chosen basis.
  simpa [rational_quaternion_basis] using rational_quaternion_basis.j_mul_j

/-- Helper for Exercise 13-13.1-14: the Hamilton basis elements satisfy `ij = k`. -/
theorem rational_quaternion_i_mul_j :
    (rational_quaternion_basis.i : ℍ[ℚ]) * rational_quaternion_basis.j =
      rational_quaternion_basis.k := by
  -- This is the defining Hamilton product relation in the chosen basis.
  simpa [rational_quaternion_basis] using rational_quaternion_basis.i_mul_j

/-- Helper for Exercise 13-13.1-14: `-i` is a right inverse to the Hamilton unit `i`. -/
theorem quaternion_i_unit_val_inv :
    (rational_quaternion_basis.i : ℍ[ℚ]) * (-rational_quaternion_basis.i) = 1 := by
  -- Use `i² = -1` and pull out the minus sign.
  rw [mul_neg, rational_quaternion_i_sq]
  norm_num

/-- Helper for Exercise 13-13.1-14: `-i` is a left inverse to the Hamilton unit `i`. -/
theorem quaternion_i_unit_inv_val :
    (-rational_quaternion_basis.i : ℍ[ℚ]) * rational_quaternion_basis.i = 1 := by
  -- The same Hamilton relation gives the inverse on the other side.
  rw [neg_mul, rational_quaternion_i_sq]
  norm_num

/-- Helper for Exercise 13-13.1-14: the Hamilton basis element `i` packaged as a unit. -/
def quaternion_i_unit : Units ℍ[ℚ] where
  val := rational_quaternion_basis.i
  inv := -rational_quaternion_basis.i
  val_inv := quaternion_i_unit_val_inv
  inv_val := quaternion_i_unit_inv_val

/-- Helper for Exercise 13-13.1-14: `-j` is a right inverse to the Hamilton unit `j`. -/
theorem quaternion_j_unit_val_inv :
    (rational_quaternion_basis.j : ℍ[ℚ]) * (-rational_quaternion_basis.j) = 1 := by
  -- Use `j² = -1` and pull out the minus sign.
  rw [mul_neg, rational_quaternion_j_sq]
  norm_num

/-- Helper for Exercise 13-13.1-14: `-j` is a left inverse to the Hamilton unit `j`. -/
theorem quaternion_j_unit_inv_val :
    (-rational_quaternion_basis.j : ℍ[ℚ]) * rational_quaternion_basis.j = 1 := by
  -- The same Hamilton relation gives the inverse on the other side.
  rw [neg_mul, rational_quaternion_j_sq]
  norm_num

/-- Helper for Exercise 13-13.1-14: the Hamilton basis element `j` packaged as a unit. -/
def quaternion_j_unit : Units ℍ[ℚ] where
  val := rational_quaternion_basis.j
  inv := -rational_quaternion_basis.j
  val_inv := quaternion_j_unit_val_inv
  inv_val := quaternion_j_unit_inv_val

/-- Helper for Exercise 13-13.1-14: the Hamilton unit `k = ij`. -/
def quaternion_k_unit : Units ℍ[ℚ] :=
  quaternion_i_unit * quaternion_j_unit

/-- Helper for Exercise 13-13.1-14: the explicit eight-value quaternion-unit table realizing the
usual labels `±1, ±i, ±j, ±k`. -/
def quaternion_group_two_unit_table : Q8 → Units ℍ[ℚ]
  | QuaternionGroup.a i =>
      match i.val with
      | 0 => 1
      | 1 => quaternion_i_unit
      | 2 => -1
      | _ => -quaternion_i_unit
  | QuaternionGroup.xa i =>
      match i.val with
      | 0 => quaternion_j_unit
      | 1 => -quaternion_k_unit
      | 2 => -quaternion_j_unit
      | _ => quaternion_k_unit

/-- Helper for Exercise 13-13.1-14: the explicit `Q8` unit table sends the identity to `1`. -/
theorem quaternionGroupTwoToQuaternionUnits_map_one :
    quaternion_group_two_unit_table (1 : Q8) = 1 := by
  -- The source identity is `a 0`, and the table sends it to the unit `1`.
  change quaternion_group_two_unit_table (QuaternionGroup.a (0 : ZMod 4)) = 1
  simp [quaternion_group_two_unit_table]

/-- Helper for Exercise 13-13.1-14: the explicit `Q8` unit table respects multiplication. -/
theorem quaternionGroupTwoToQuaternionUnits_map_mul (g h : Q8) :
    quaternion_group_two_unit_table (g * h) =
      quaternion_group_two_unit_table g * quaternion_group_two_unit_table h := by
  -- Route correction: finish the explicit `Q8` model by a finite multiplication check.
  let hm : ∀ g h : Q8,
      quaternion_group_two_unit_table (g * h) =
        quaternion_group_two_unit_table g * quaternion_group_two_unit_table h := by
    native_decide
  exact hm g h

/-- The canonical embedding `Q8 → ℍ[ℚ]ˣ` sending the standard generators to Hamilton units. -/
def quaternionGroupTwoToQuaternionUnits : Q8 →* Units ℍ[ℚ] :=
  { toFun := quaternion_group_two_unit_table
    map_one' := quaternionGroupTwoToQuaternionUnits_map_one
    map_mul' := quaternionGroupTwoToQuaternionUnits_map_mul }

/-- Helper for Exercise 13-13.1-14: a chosen primitive cube root of unity in `ℍ[ℚ]`. -/
def quaternionCubeRootOfUnity : ℍ[ℚ] :=
  (⟨-(1 : ℚ) / 2, 1 / 2, 1 / 2, 1 / 2⟩ : ℍ[ℚ])

/-- Helper for Exercise 13-13.1-14: the square of the chosen cube root of unity. -/
def quaternion_cube_root_squared : ℍ[ℚ] :=
  (⟨-(1 : ℚ) / 2, -(1 : ℚ) / 2, -(1 : ℚ) / 2, -(1 : ℚ) / 2⟩ : ℍ[ℚ])

/-- Helper for Exercise 13-13.1-14: the chosen quaternion cube root is nonzero. -/
theorem quaternion_cube_root_of_unity_ne_zero :
    quaternionCubeRootOfUnity ≠ 0 := by
  -- The real coordinate is `-1 / 2`, so the quaternion cannot vanish.
  intro h
  have hre := congrArg QuaternionAlgebra.re h
  norm_num [quaternionCubeRootOfUnity] at hre

/-- Helper for Exercise 13-13.1-14: the square of the chosen quaternion cube root is nonzero. -/
theorem quaternion_cube_root_squared_ne_zero :
    quaternion_cube_root_squared ≠ 0 := by
  -- Again, the real coordinate is `-1 / 2`.
  intro h
  have hre := congrArg QuaternionAlgebra.re h
  norm_num [quaternion_cube_root_squared] at hre

/-- Helper for Exercise 13-13.1-14: the unit attached to the chosen cube root of unity. -/
def quaternion_cube_root_unit : Units ℍ[ℚ] :=
  Units.mk0 quaternionCubeRootOfUnity quaternion_cube_root_of_unity_ne_zero

/-- Helper for Exercise 13-13.1-14: the unit attached to the square of the chosen cube root. -/
def quaternion_cube_root_squared_unit : Units ℍ[ℚ] :=
  Units.mk0 quaternion_cube_root_squared quaternion_cube_root_squared_ne_zero

/-- Helper for Exercise 13-13.1-14: the explicit three-value unit table on the cyclic factor. -/
def cyclic_order_three_unit_table : C3 → Units ℍ[ℚ] := fun c =>
  match c.toAdd.val with
  | 0 => 1
  | 1 => quaternion_cube_root_unit
  | _ => quaternion_cube_root_squared_unit

/-- Helper for Exercise 13-13.1-14: the explicit `C3` unit table sends the identity to `1`. -/
theorem cyclicOrderThreeToQuaternionUnits_map_one :
    cyclic_order_three_unit_table (1 : C3) = 1 := by
  -- The group identity corresponds to the `0` residue.
  simp [cyclic_order_three_unit_table]

/-- Helper for Exercise 13-13.1-14: the explicit `C3` unit table respects multiplication. -/
theorem cyclicOrderThreeToQuaternionUnits_map_mul (g h : C3) :
    cyclic_order_three_unit_table (g * h) =
      cyclic_order_three_unit_table g * cyclic_order_three_unit_table h := by
  -- The cyclic factor has only three elements, so a finite check is enough here.
  let hm : ∀ g h : C3,
      cyclic_order_three_unit_table (g * h) =
        cyclic_order_three_unit_table g * cyclic_order_three_unit_table h := by
    native_decide
  exact hm g h

/-- The canonical embedding `C3 → ℍ[ℚ]ˣ` sending the generator to
`quaternionCubeRootOfUnity`. -/
def cyclicOrderThreeToQuaternionUnits : C3 →* Units ℍ[ℚ] :=
  { toFun := cyclic_order_three_unit_table
    map_one' := cyclicOrderThreeToQuaternionUnits_map_one
    map_mul' := cyclicOrderThreeToQuaternionUnits_map_mul }

/-- Helper for Exercise 13-13.1-14: the linear action of `Q8 × C3` on `ℍ[ℚ]` given by left
multiplication from the cyclic factor and right multiplication from the quaternion factor. -/
def quaternion_cyclic_witness_linear (g : G0) : ℍ[ℚ] →ₗ[ℚ] ℍ[ℚ] :=
  LinearMap.mulLeftRight ℚ
    ((cyclicOrderThreeToQuaternionUnits g.2 : ℍ[ℚ]),
      (quaternionGroupTwoToQuaternionUnits g.1⁻¹ : ℍ[ℚ]))

/-- Helper for Exercise 13-13.1-14: the witness action sends the identity element to the identity
linear map. -/
theorem quaternionCyclicWitnessRepresentation_map_one :
    quaternion_cyclic_witness_linear (1 : G0) = 1 := by
  -- The identity acts by multiplying on both sides with `1`.
  apply LinearMap.ext
  intro x
  change
    ((cyclicOrderThreeToQuaternionUnits 1 : Units ℍ[ℚ]) : ℍ[ℚ]) * x *
        ((quaternionGroupTwoToQuaternionUnits ((1 : Q8)⁻¹) : Units ℍ[ℚ]) : ℍ[ℚ]) = x
  simp

/-- Helper for Exercise 13-13.1-14: the witness action is multiplicative in `Q8 × C3`. -/
theorem quaternionCyclicWitnessRepresentation_map_mul (g h : G0) :
    quaternion_cyclic_witness_linear (g * h) =
      quaternion_cyclic_witness_linear g * quaternion_cyclic_witness_linear h := by
  -- Left multiplication composes in the forward order, while the right factor uses inverses and
  -- therefore lands in the correct reversed order automatically.
  apply LinearMap.ext
  intro x
  change
    ((cyclicOrderThreeToQuaternionUnits ((g * h).2) : Units ℍ[ℚ]) : ℍ[ℚ]) * x *
        ((quaternionGroupTwoToQuaternionUnits ((g * h).1⁻¹) : Units ℍ[ℚ]) : ℍ[ℚ]) =
      ((cyclicOrderThreeToQuaternionUnits g.2 : Units ℍ[ℚ]) : ℍ[ℚ]) *
          (((cyclicOrderThreeToQuaternionUnits h.2 : Units ℍ[ℚ]) : ℍ[ℚ]) * x *
            ((quaternionGroupTwoToQuaternionUnits (h.1⁻¹) : Units ℍ[ℚ]) : ℍ[ℚ])) *
        ((quaternionGroupTwoToQuaternionUnits (g.1⁻¹) : Units ℍ[ℚ]) : ℍ[ℚ])
  simp [mul_assoc]

/-- The quaternionic representation of `Q8 × C3` on `ℍ[ℚ]` where the cyclic factor acts on the
left and the quaternion factor acts on the right through inverses. -/
def quaternionCyclicWitnessRepresentation : Representation ℚ G0 ℍ[ℚ] :=
  { toFun := quaternion_cyclic_witness_linear
    map_one' := quaternionCyclicWitnessRepresentation_map_one
    map_mul' := quaternionCyclicWitnessRepresentation_map_mul }

local notation "ρ" => quaternionCyclicWitnessRepresentation

/-- Helper for Exercise 13-13.1-14: the rational character of the quaternionic witness, viewed in
`R_ℚ(Q8 × C3)`. -/
abbrev characterRingElement (τ : Representation ℚ G0 ℍ[ℚ]) : R[ℚ](G0) :=
  ⟨τ.character,
    Representation.rep_character_mem_characterRingOverField
      (K := ℚ) (G := G0) (Rep.of τ)⟩

/- The source-facing notation `χ_ρ` specialized to the quaternionic witness setting. -/
scoped[Representation] notation:max "χ_" τ:max =>
  characterRingElement τ

/-- Helper for Exercise 13-13.1-14: the witness action at the identity element is left
multiplication by `1`. -/
theorem quaternion_witness_apply_identity :
    ρ ((1 : Q8), (1 : C3)) = LinearMap.mulLeft ℚ (1 : Quaternion ℚ) := by
  -- Evaluate the representation on an arbitrary quaternion and simplify both unit factors.
  apply LinearMap.ext
  intro x
  change
    ((cyclicOrderThreeToQuaternionUnits 1 : Units (Quaternion ℚ)) : Quaternion ℚ) * x *
        ((quaternionGroupTwoToQuaternionUnits ((1 : Q8)⁻¹) : Units (Quaternion ℚ)) :
          Quaternion ℚ) =
      (1 : Quaternion ℚ) * x
  simp

/-- Helper for Exercise 13-13.1-14: the central involution `a 2 = -1` maps to `-1 ∈ ℍ[ℚ]ˣ`. -/
theorem quaternion_group_two_unit_table_a_two :
    quaternion_group_two_unit_table (QuaternionGroup.a (2 : ZMod 4)) = (-1 : Units ℍ[ℚ]) := by
  -- Reduce the `ZMod 4` index to its concrete value in the explicit table.
  have hval : (2 : ZMod 4).val = 2 := rfl
  simp [quaternion_group_two_unit_table, hval]

/-- Helper for Exercise 13-13.1-14: the packaged `Q8` embedding still sends `a 2` to `-1`. -/
theorem quaternionGroupTwoToQuaternionUnits_a_two :
    quaternionGroupTwoToQuaternionUnits (QuaternionGroup.a (2 : ZMod 4)) =
      (-1 : Units ℍ[ℚ]) := by
  -- This is the corresponding evaluation of the multiplicative package.
  exact quaternion_group_two_unit_table_a_two

/-- Helper for Exercise 13-13.1-14: the chosen generator of `C3` maps to the quaternion cube root
unit. -/
theorem cyclic_order_three_unit_table_generator :
    cyclic_order_three_unit_table (Multiplicative.ofAdd (1 : ZMod 3)) =
      quaternion_cube_root_unit := by
  -- Reduce the `ZMod 3` index to its concrete value in the explicit table.
  have hval : (1 : ZMod 3).val = 1 := rfl
  simp [cyclic_order_three_unit_table, hval]

/-- Helper for Exercise 13-13.1-14: the packaged cyclic embedding sends the chosen generator to
the quaternion cube root unit. -/
theorem cyclicOrderThreeToQuaternionUnits_generator :
    cyclicOrderThreeToQuaternionUnits (Multiplicative.ofAdd (1 : ZMod 3)) =
      quaternion_cube_root_unit := by
  -- This is the corresponding evaluation of the multiplicative package.
  exact cyclic_order_three_unit_table_generator

/-- Helper for Exercise 13-13.1-14: the `Q8` embedding sends `a 1` to the Hamilton unit `i`. -/
theorem quaternionGroupTwoToQuaternionUnits_a_one :
    ((quaternionGroupTwoToQuaternionUnits (QuaternionGroup.a (1 : ZMod 4)) : Units ℍ[ℚ]) : ℍ[ℚ]) =
      rational_quaternion_basis.i := by
  -- The explicit table identifies `a 1` with the Hamilton unit `i`.
  have hval : (1 : ZMod 4).val = 1 := rfl
  simp [quaternionGroupTwoToQuaternionUnits, quaternion_group_two_unit_table, hval,
    quaternion_i_unit, rational_quaternion_basis]

/-- Helper for Exercise 13-13.1-14: the `Q8` embedding sends `xa 0` to the Hamilton unit `j`. -/
theorem quaternionGroupTwoToQuaternionUnits_xa_zero :
    ((quaternionGroupTwoToQuaternionUnits (QuaternionGroup.xa (0 : ZMod 4)) : Units ℍ[ℚ]) : ℍ[ℚ]) =
      rational_quaternion_basis.j := by
  -- The explicit table identifies `xa 0` with the Hamilton unit `j`.
  have hval : (0 : ZMod 4).val = 0 := rfl
  simp [quaternionGroupTwoToQuaternionUnits, quaternion_group_two_unit_table, hval,
    quaternion_j_unit, rational_quaternion_basis]

/-- Helper for Exercise 13-13.1-14: the quaternionic generator `a 3` acts by right multiplication
with `i`. -/
theorem quaternionCyclicWitnessRepresentation_apply_a_three :
    quaternionCyclicWitnessRepresentation (QuaternionGroup.a (3 : ZMod 4), (1 : C3)) =
      LinearMap.mulRight ℚ rational_quaternion_basis.i := by
  -- The cyclic factor is trivial here, while `(a 3)⁻¹ = a 1` contributes the Hamilton unit `i`.
  apply LinearMap.ext
  intro x
  rw [LinearMap.mulRight_apply]
  change
    ((cyclicOrderThreeToQuaternionUnits 1 : Units ℍ[ℚ]) : ℍ[ℚ]) * x *
        ((quaternionGroupTwoToQuaternionUnits
            ((QuaternionGroup.a (3 : ZMod 4) : Q8)⁻¹) : Units ℍ[ℚ]) : ℍ[ℚ]) =
      x * rational_quaternion_basis.i
  have hinv : ((QuaternionGroup.a (3 : ZMod 4) : Q8)⁻¹) = QuaternionGroup.a (1 : ZMod 4) := by
    decide
  rw [hinv]
  rw [quaternionGroupTwoToQuaternionUnits_a_one]
  simp

/-- Helper for Exercise 13-13.1-14: the quaternionic generator `xa 2` acts by right
multiplication with `j`. -/
theorem quaternionCyclicWitnessRepresentation_apply_xa_two :
    quaternionCyclicWitnessRepresentation (QuaternionGroup.xa (2 : ZMod 4), (1 : C3)) =
      LinearMap.mulRight ℚ rational_quaternion_basis.j := by
  -- The cyclic factor is trivial here, while `(xa 2)⁻¹ = xa 0` contributes the Hamilton unit `j`.
  apply LinearMap.ext
  intro x
  rw [LinearMap.mulRight_apply]
  change
    ((cyclicOrderThreeToQuaternionUnits 1 : Units ℍ[ℚ]) : ℍ[ℚ]) * x *
        ((quaternionGroupTwoToQuaternionUnits
            ((QuaternionGroup.xa (2 : ZMod 4) : Q8)⁻¹) : Units ℍ[ℚ]) : ℍ[ℚ]) =
      x * rational_quaternion_basis.j
  have hinv : ((QuaternionGroup.xa (2 : ZMod 4) : Q8)⁻¹) = QuaternionGroup.xa (0 : ZMod 4) := by
    decide
  rw [hinv]
  rw [quaternionGroupTwoToQuaternionUnits_xa_zero]
  simp

/-- Helper for Exercise 13-13.1-14: the distinguished central involution acts by left
multiplication with `-1`. -/
theorem quaternionCyclicWitnessRepresentation_apply_central_order_two :
    quaternionCyclicWitnessRepresentation quaternion_cyclic_central_order_two =
      LinearMap.mulLeft ℚ (-1 : ℍ[ℚ]) := by
  -- The cyclic factor is trivial here, while the quaternion factor contributes the scalar `-1`.
  apply LinearMap.ext
  intro x
  change
    ((cyclicOrderThreeToQuaternionUnits 1 : Units ℍ[ℚ]) : ℍ[ℚ]) * x *
        ((quaternionGroupTwoToQuaternionUnits
            ((QuaternionGroup.a (2 : ZMod 4) : Q8)⁻¹) : Units ℍ[ℚ]) : ℍ[ℚ]) =
      (-1 : ℍ[ℚ]) * x
  have hinv : ((QuaternionGroup.a (2 : ZMod 4) : Q8)⁻¹) = QuaternionGroup.a (2 : ZMod 4) := by
    decide
  rw [hinv, quaternionGroupTwoToQuaternionUnits_a_two]
  simp

/-- Helper for Exercise 13-13.1-14: the distinguished central element of order `3` acts by left
multiplication with the chosen quaternion cube root of unity. -/
theorem quaternionCyclicWitnessRepresentation_apply_central_order_three :
    quaternionCyclicWitnessRepresentation quaternion_cyclic_central_order_three =
      LinearMap.mulLeft ℚ quaternionCubeRootOfUnity := by
  -- The quaternion factor is trivial here, and the cyclic generator supplies the left factor.
  apply LinearMap.ext
  intro x
  change
    ((cyclicOrderThreeToQuaternionUnits
        (Multiplicative.ofAdd (1 : ZMod 3)) : Units ℍ[ℚ]) : ℍ[ℚ]) * x *
        ((quaternionGroupTwoToQuaternionUnits ((1 : Q8)⁻¹) : Units ℍ[ℚ]) : ℍ[ℚ]) =
      quaternionCubeRootOfUnity * x
  rw [cyclicOrderThreeToQuaternionUnits_generator]
  simp [quaternion_cube_root_unit, quaternionCubeRootOfUnity]

/-- Helper for Exercise 13-13.1-14: the distinguished central element of order `6` acts by left
multiplication with `-quaternionCubeRootOfUnity`. -/
theorem quaternionCyclicWitnessRepresentation_apply_central_order_six :
    quaternionCyclicWitnessRepresentation quaternion_cyclic_central_order_six =
      LinearMap.mulLeft ℚ (-quaternionCubeRootOfUnity) := by
  -- This element combines the cyclic generator with the quaternionic scalar `-1`.
  apply LinearMap.ext
  intro x
  change
    ((cyclicOrderThreeToQuaternionUnits
        (Multiplicative.ofAdd (1 : ZMod 3)) : Units ℍ[ℚ]) : ℍ[ℚ]) * x *
        ((quaternionGroupTwoToQuaternionUnits
            ((QuaternionGroup.a (2 : ZMod 4) : Q8)⁻¹) : Units ℍ[ℚ]) : ℍ[ℚ]) =
      (-quaternionCubeRootOfUnity) * x
  have hinv : ((QuaternionGroup.a (2 : ZMod 4) : Q8)⁻¹) = QuaternionGroup.a (2 : ZMod 4) := by
    decide
  rw [hinv, cyclicOrderThreeToQuaternionUnits_generator, quaternionGroupTwoToQuaternionUnits_a_two]
  simp [quaternion_cube_root_unit, quaternionCubeRootOfUnity]

/-- Helper for Exercise 13-13.1-14: in the basis `1, i, j, k`, left multiplication by
`q : ℍ[ℚ]` has trace `4 * q.re`. -/
theorem rational_quaternion_left_mul_trace_eq_four_mul_re
    (q : QuaternionAlgebra ℚ (-1) 0 (-1)) :
    LinearMap.trace ℚ (QuaternionAlgebra ℚ (-1) 0 (-1))
      (LinearMap.mulLeft ℚ q) = 4 * q.re := by
  -- Compute the matrix trace explicitly in the coordinate basis `1, i, j, k`.
  let B : Module.Basis (Fin 4) ℚ (QuaternionAlgebra ℚ (-1) 0 (-1)) :=
    QuaternionAlgebra.basisOneIJK (-1 : ℚ) 0 (-1 : ℚ)
  have hB0 : (B 0 : QuaternionAlgebra ℚ (-1) 0 (-1)) = 1 := by
    apply B.equivFun.injective
    ext i
    fin_cases i <;> simp [B, QuaternionAlgebra.coe_basisOneIJK_repr]
  have hB1 :
      (B 1 : QuaternionAlgebra ℚ (-1) 0 (-1)) = (QuaternionAlgebra.Basis.self ℚ).i := by
    apply B.equivFun.injective
    ext i
    fin_cases i <;> simp [B, QuaternionAlgebra.coe_basisOneIJK_repr]
  have hB2 :
      (B 2 : QuaternionAlgebra ℚ (-1) 0 (-1)) = (QuaternionAlgebra.Basis.self ℚ).j := by
    apply B.equivFun.injective
    ext i
    fin_cases i <;> simp [B, QuaternionAlgebra.coe_basisOneIJK_repr]
  have hB3 :
      (B 3 : QuaternionAlgebra ℚ (-1) 0 (-1)) = (QuaternionAlgebra.Basis.self ℚ).k := by
    apply B.equivFun.injective
    ext i
    fin_cases i <;> simp [B, QuaternionAlgebra.coe_basisOneIJK_repr]
  rw [LinearMap.trace_eq_matrix_trace ℚ B]
  rw [Matrix.trace, Fin.sum_univ_four, Matrix.diag]
  have h00 : (Algebra.leftMulMatrix B q) 0 0 = q.re := by
    simp [Algebra.leftMulMatrix_eq_repr_mul, hB0, B]
  have h11 : (Algebra.leftMulMatrix B q) 1 1 = q.re := by
    simp [Algebra.leftMulMatrix_eq_repr_mul, hB1, B]
  have h22 : (Algebra.leftMulMatrix B q) 2 2 = q.re := by
    simp [Algebra.leftMulMatrix_eq_repr_mul, hB2, B]
  have h33 : (Algebra.leftMulMatrix B q) 3 3 = q.re := by
    simp [Algebra.leftMulMatrix_eq_repr_mul, hB3, B]
  calc
    (Algebra.leftMulMatrix B q) 0 0 + (Algebra.leftMulMatrix B q) 1 1 +
        (Algebra.leftMulMatrix B q) 2 2 + (Algebra.leftMulMatrix B q) 3 3 =
      q.re + q.re + q.re + q.re := by
        rw [h00, h11, h22, h33]
    _ = 4 * q.re := by
      ring

/-- Helper for Exercise 13-13.1-14: left multiplication by the chosen quaternion cube root of
unity has trace `-2`. -/
theorem trace_mulLeft_quaternion_cube_root_of_unity_eq_neg_two :
    LinearMap.trace ℚ ℍ[ℚ]
      (LinearMap.mulLeft ℚ quaternionCubeRootOfUnity) = -2 := by
  -- The trace formula reduces the computation to the real part `-1 / 2`.
  change
    LinearMap.trace ℚ (QuaternionAlgebra ℚ (-1) 0 (-1))
      (LinearMap.mulLeft ℚ quaternionCubeRootOfUnity) = -2
  have h := rational_quaternion_left_mul_trace_eq_four_mul_re quaternionCubeRootOfUnity
  norm_num [quaternionCubeRootOfUnity] at h ⊢
  exact h

/-- Helper for Exercise 13-13.1-14: conjugation in `Q8` sends an element either to itself or to
its inverse. -/
theorem quaternionGroupTwo_conj_eq_self_or_inv (g q : Q8) :
    g * q * g⁻¹ = q ∨ g * q * g⁻¹ = q⁻¹ := by
  -- The explicit eight-element model reduces this conjugation calculation to a finite check.
  revert q
  revert g
  native_decide

/-- Helper for Exercise 13-13.1-14: the fourth power of `(q, c) ∈ Q8 × C3` isolates the cyclic
coordinate. -/
theorem quaternion_cyclic_pow_four (n : G0) :
    n ^ 4 = (1, n.2) := by
  -- In `Q8`, every element has fourth power `1`, while in `C3` the fourth power is the element
  -- itself.
  revert n
  native_decide

/-- Helper for Exercise 13-13.1-14: every subrepresentation of the quaternionic witness is stable
under right multiplication by `star q` for arbitrary `q : ℍ[ℚ]`. -/
theorem quaternion_cyclic_mul_star_mem
    (W : Subrepresentation ρ) {x q : ℍ[ℚ]} (hx : x ∈ W.toSubmodule) :
    x * star q ∈ W.toSubmodule := by
  -- The right action of the two quaternionic generators gives stability under the Hamilton basis,
  -- and the explicit coordinate formula for `star q` finishes by linearity.
  have hi : x * rational_quaternion_basis.i ∈ W.toSubmodule := by
    simpa [quaternionCyclicWitnessRepresentation_apply_a_three] using
      W.apply_mem_toSubmodule (QuaternionGroup.a (3 : ZMod 4), (1 : C3)) hx
  have hj : x * rational_quaternion_basis.j ∈ W.toSubmodule := by
    simpa [quaternionCyclicWitnessRepresentation_apply_xa_two] using
      W.apply_mem_toSubmodule (QuaternionGroup.xa (2 : ZMod 4), (1 : C3)) hx
  have hk_step : (x * rational_quaternion_basis.i) * rational_quaternion_basis.j ∈ W.toSubmodule := by
    simpa [quaternionCyclicWitnessRepresentation_apply_xa_two] using
      W.apply_mem_toSubmodule (QuaternionGroup.xa (2 : ZMod 4), (1 : C3)) hi
  have hk : x * rational_quaternion_basis.k ∈ W.toSubmodule := by
    simpa [mul_assoc, rational_quaternion_i_mul_j] using hk_step
  have hstar :
      x * star q =
        q.re • x - q.imI • (x * rational_quaternion_basis.i) -
          q.imJ • (x * rational_quaternion_basis.j) -
            q.imK • (x * rational_quaternion_basis.k) := by
    ext <;> simp [rational_quaternion_basis, sub_eq_add_neg] <;> ring
  rw [hstar]
  exact W.toSubmodule.sub_mem
    (W.toSubmodule.sub_mem
      (W.toSubmodule.sub_mem
        (W.toSubmodule.smul_mem q.re hx)
        (W.toSubmodule.smul_mem q.imI hi))
      (W.toSubmodule.smul_mem q.imJ hj))
    (W.toSubmodule.smul_mem q.imK hk)

/-- Helper for Exercise 13-13.1-14: a nonzero subrepresentation of the quaternionic witness is the
whole quaternion space. -/
theorem quaternion_cyclic_subrepresentation_eq_top_of_ne_bot
    (W : Subrepresentation ρ) (hW : W ≠ ⊥) :
    W = ⊤ := by
  -- A nonzero vector in `W` can be right-multiplied to `1`, and then `1` generates all of
  -- `ℍ[ℚ]` under the same right quaternion action.
  have hWsub : W.toSubmodule ≠ ⊥ := by
    intro hbot
    exact hW (Subrepresentation.toSubmodule_injective hbot)
  rcases W.toSubmodule.ne_bot_iff.mp hWsub with ⟨w, hw, hw0⟩
  let u : Units ℍ[ℚ] := Units.mk0 w hw0
  have h_one_aux :
      w * ((u⁻¹ : Units ℍ[ℚ]) : ℍ[ℚ]) ∈ W.toSubmodule := by
    simpa [star_star] using
      quaternion_cyclic_mul_star_mem (W := W) (x := w)
        (q := star (((u⁻¹ : Units ℍ[ℚ]) : ℍ[ℚ]))) hw
  have h_one : (1 : ℍ[ℚ]) ∈ W.toSubmodule := by
    have hmul : w * ((u⁻¹ : Units ℍ[ℚ]) : ℍ[ℚ]) = (1 : ℍ[ℚ]) := by
      simpa [u] using u.val_inv
    exact hmul ▸ h_one_aux
  apply Subrepresentation.toSubmodule_injective
  ext y
  constructor
  · intro hy
    exact Submodule.mem_top
  · intro hy
    simpa [star_star] using
      quaternion_cyclic_mul_star_mem (W := W) (x := (1 : ℍ[ℚ]))
        (q := star y) h_one

/-- Helper for Exercise 13-13.1-14: the quaternionic witness representation is irreducible
over `ℚ`. -/
theorem quaternion_cyclic_witness_isIrreducible :
    (ρ).IsIrreducible := by
  letI : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  refine IsSimpleOrder.of_forall_eq_top fun W hW ↦ ?_
  exact quaternion_cyclic_subrepresentation_eq_top_of_ne_bot W hW

end

end Representation
