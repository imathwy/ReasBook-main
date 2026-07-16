import LinearRepresentations_Serre_1977.Serre.Chap13.Exercise_13_13_1_14.QuaternionWitnessCore

noncomputable section

open scoped Representation
open scoped Quaternion

namespace Representation

section

local notation "Q8" => QuaternionGroup 2
local notation "C3" => Multiplicative (ZMod 3)
local notation "G0" => Q8 × C3
local notation "ρ" => quaternionCyclicWitnessRepresentation

local instance anonInst_IntertwinerCubicPlane_1 : Fintype Q8 := inferInstance
local instance anonInst_IntertwinerCubicPlane_2 : Fintype C3 := inferInstance
local instance anonInst_IntertwinerCubicPlane_3 : DecidableEq Q8 := inferInstance
local instance anonInst_IntertwinerCubicPlane_4 : DecidableEq C3 := inferInstance
local instance anonInst_IntertwinerCubicPlane_5 : Finite G0 := inferInstance
local instance anonInst_IntertwinerCubicPlane_6 : Fintype G0 := inferInstance
local instance anonInst_IntertwinerCubicPlane_7 : DecidableEq G0 := inferInstance

/-- Helper for Exercise 13-13.1-14: the explicit cubic plane inside `ℍ[ℚ]`, written in the basis
`1, i, j, k` as the quaternions with equal `i`, `j`, and `k` coordinates. -/
def quaternion_cubic_pair_to_quaternion (p : ℚ × ℚ) : ℍ[ℚ] :=
  p.1 • (1 : ℍ[ℚ]) + p.2 • rational_quaternion_basis.i +
    p.2 • rational_quaternion_basis.j + p.2 • rational_quaternion_basis.k

/-- Helper for Exercise 13-13.1-14: the explicit cubic-plane parametrization records the expected
real and `i`-coordinates. -/
theorem quaternion_cubic_pair_to_quaternion_re_imI (p : ℚ × ℚ) :
    (quaternion_cubic_pair_to_quaternion p).re = p.1 ∧
      (quaternion_cubic_pair_to_quaternion p).imI = p.2 := by
  -- Read off the coefficients of `1` and `i` from the explicit basis expression.
  constructor <;> simp [quaternion_cubic_pair_to_quaternion, rational_quaternion_basis]

/-- Helper for Exercise 13-13.1-14: the cubic-plane parametrization also forces the `j` and `k`
coordinates to match the same second parameter. -/
theorem quaternion_cubic_pair_to_quaternion_imJ_imK (p : ℚ × ℚ) :
    (quaternion_cubic_pair_to_quaternion p).imJ = p.2 ∧
      (quaternion_cubic_pair_to_quaternion p).imK = p.2 := by
  -- The same coordinate computation works for the remaining Hamilton basis vectors.
  constructor <;> simp [quaternion_cubic_pair_to_quaternion, rational_quaternion_basis]

/-- Helper for Exercise 13-13.1-14: commuting with the left action of the cube root of unity is
equivalent to lying in the explicit cubic plane. -/
theorem commutes_with_quaternion_cube_root_iff_equal_im_coordinates
    (q : ℍ[ℚ]) :
    q * quaternionCubeRootOfUnity = quaternionCubeRootOfUnity * q ↔
      q.imI = q.imJ ∧ q.imJ = q.imK := by
  -- Compare the `1`, `i`, `j`, and `k` coordinates of `qω` and `ωq`.
  constructor
  · intro h
    have hre := congrArg QuaternionAlgebra.re h
    have hi := congrArg QuaternionAlgebra.imI h
    have hj := congrArg QuaternionAlgebra.imJ h
    have hk := congrArg QuaternionAlgebra.imK h
    norm_num [quaternionCubeRootOfUnity] at hre hi hj hk
    constructor
    · linarith
    · linarith
  · rintro ⟨hij, hjk⟩
    ext <;> simp [quaternionCubeRootOfUnity, hij, hjk] <;> ring

/-- Helper for Exercise 13-13.1-14: once the three imaginary coordinates agree, the quaternion is
recovered from its real part and common imaginary coordinate. -/
theorem quaternion_eq_cubic_pair_of_equal_im_coordinates
    (q : ℍ[ℚ]) (hij : q.imI = q.imJ) (hjk : q.imJ = q.imK) :
    q = quaternion_cubic_pair_to_quaternion (q.re, q.imI) := by
  -- Extensionality in the Hamilton basis turns the reconstruction into coordinate identities.
  ext <;> simp [quaternion_cubic_pair_to_quaternion, rational_quaternion_basis, hij, hjk]

/-- Helper for Exercise 13-13.1-14: every self-intertwiner is already determined by its value at
`1`, because the right `Q8`-action generates the Hamilton basis. -/
theorem quaternion_cyclic_intertwiner_apply_eq
    (T : (ρ).IntertwiningMap (ρ)) (g : G0) (x : ℍ[ℚ]) :
    T (ρ g x) = ρ g (T x) := by
  -- Evaluate the defining intertwining identity at the vector `x`.
  simpa using congrArg (fun f : ℍ[ℚ] →ₗ[ℚ] ℍ[ℚ] ↦ f x) (T.isIntertwining' g)

/-- Helper for Exercise 13-13.1-14: every self-intertwiner is already determined by its value at
`1`, because the right `Q8`-action generates the Hamilton basis. -/
theorem quaternion_cyclic_intertwiner_eq_mulLeft_of_eval_one
    (T : (ρ).IntertwiningMap (ρ)) :
    T.toLinearMap = LinearMap.mulLeft ℚ (T (1 : ℍ[ℚ])) := by
  -- Evaluate equivariance on the two quaternionic generators to identify the images of `i`, `j`,
  -- and then `k`.
  apply LinearMap.ext
  intro x
  have hi :
      T rational_quaternion_basis.i = T (1 : ℍ[ℚ]) * rational_quaternion_basis.i := by
    simpa [quaternionCyclicWitnessRepresentation_apply_a_three] using
      quaternion_cyclic_intertwiner_apply_eq T
        (QuaternionGroup.a (3 : ZMod 4), (1 : C3)) (1 : ℍ[ℚ])
  have hj :
      T rational_quaternion_basis.j = T (1 : ℍ[ℚ]) * rational_quaternion_basis.j := by
    simpa [quaternionCyclicWitnessRepresentation_apply_xa_two] using
      quaternion_cyclic_intertwiner_apply_eq T
        (QuaternionGroup.xa (2 : ZMod 4), (1 : C3)) (1 : ℍ[ℚ])
  have hk :
      T rational_quaternion_basis.k = T (1 : ℍ[ℚ]) * rational_quaternion_basis.k := by
    have h :=
      quaternion_cyclic_intertwiner_apply_eq T (QuaternionGroup.xa (2 : ZMod 4), (1 : C3))
        rational_quaternion_basis.i
    simpa [quaternionCyclicWitnessRepresentation_apply_xa_two, hi, mul_assoc,
      rational_quaternion_i_mul_j] using h
  have hscalar : ∀ a : ℚ, T (a : ℍ[ℚ]) = a • T (1 : ℍ[ℚ]) := by
    -- Scalars are the right multiples of `1`, so linearity reduces them to the value at `1`.
    intro a
    simpa using T.map_smul a (1 : ℍ[ℚ])
  have hx :
      x = (x.re : ℍ[ℚ]) + x.imI • rational_quaternion_basis.i +
        x.imJ • rational_quaternion_basis.j + x.imK • rational_quaternion_basis.k := by
    -- Separate the scalar part from the three pure quaternion coordinates.
    ext <;> simp [rational_quaternion_basis] <;> ring
  have hscalar_x : T.toLinearMap (x.re : ℍ[ℚ]) = x.re • T (1 : ℍ[ℚ]) := by
    simpa using hscalar x.re
  have hi' : T.toLinearMap rational_quaternion_basis.i = T (1 : ℍ[ℚ]) * rational_quaternion_basis.i := by
    simpa using hi
  have hj' : T.toLinearMap rational_quaternion_basis.j = T (1 : ℍ[ℚ]) * rational_quaternion_basis.j := by
    simpa using hj
  have hk' : T.toLinearMap rational_quaternion_basis.k = T (1 : ℍ[ℚ]) * rational_quaternion_basis.k := by
    simpa using hk
  rw [hx]
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul]
  rw [hscalar_x, hi', hj', hk']
  change
    x.re • T (1 : ℍ[ℚ]) + x.imI • (T (1 : ℍ[ℚ]) * rational_quaternion_basis.i) +
        x.imJ • (T (1 : ℍ[ℚ]) * rational_quaternion_basis.j) +
          x.imK • (T (1 : ℍ[ℚ]) * rational_quaternion_basis.k) =
      T (1 : ℍ[ℚ]) *
        ((x.re : ℍ[ℚ]) + x.imI • rational_quaternion_basis.i +
          x.imJ • rational_quaternion_basis.j + x.imK • rational_quaternion_basis.k)
  ext <;> simp [rational_quaternion_basis, sub_eq_add_neg] <;> ring

/-- Helper for Exercise 13-13.1-14: the value at `1` of a self-intertwiner commutes with the
distinguished cubic root of unity. -/
theorem quaternion_cyclic_intertwiner_eval_one_commutes_with_quaternion_cube_root
    (T : (ρ).IntertwiningMap (ρ)) :
    T (1 : ℍ[ℚ]) * quaternionCubeRootOfUnity =
      quaternionCubeRootOfUnity * T (1 : ℍ[ℚ]) := by
  -- Compare the central order-`3` equivariance relation with the previously identified
  -- left-multiplication description of `T`.
  have hmul :=
    LinearMap.congr_fun
      (quaternion_cyclic_intertwiner_eq_mulLeft_of_eval_one T)
      quaternionCubeRootOfUnity
  have hcentral :
      T quaternionCubeRootOfUnity =
        quaternionCubeRootOfUnity * T (1 : ℍ[ℚ]) := by
    simpa [quaternionCyclicWitnessRepresentation_apply_central_order_three] using
      quaternion_cyclic_intertwiner_apply_eq T quaternion_cyclic_central_order_three (1 : ℍ[ℚ])
  calc
    T (1 : ℍ[ℚ]) * quaternionCubeRootOfUnity = T quaternionCubeRootOfUnity := by
      simpa using hmul.symm
    _ = quaternionCubeRootOfUnity * T (1 : ℍ[ℚ]) := hcentral

/-- Helper for Exercise 13-13.1-14: the square of the chosen quaternionic cube root has the
expected explicit coordinate description. -/
theorem quaternion_cube_root_squared_eq :
    quaternion_cube_root_squared = quaternionCubeRootOfUnity * quaternionCubeRootOfUnity := by
  -- This is a direct coordinate computation in the Hamilton basis.
  ext <;> norm_num [quaternion_cube_root_squared, quaternionCubeRootOfUnity]

/-- Helper for Exercise 13-13.1-14: the identity element of `C3` acts as the unit quaternion. -/
theorem cyclicOrderThreeToQuaternionUnits_one_val :
    ((cyclicOrderThreeToQuaternionUnits (1 : C3) : Units ℍ[ℚ]) : ℍ[ℚ]) = 1 := by
  simp [cyclicOrderThreeToQuaternionUnits, cyclic_order_three_unit_table]

/-- Helper for Exercise 13-13.1-14: the square of the chosen generator of `C3` acts as
`quaternion_cube_root_squared`. -/
theorem cyclicOrderThreeToQuaternionUnits_two_val :
    ((cyclicOrderThreeToQuaternionUnits
        (Multiplicative.ofAdd (2 : ZMod 3)) : Units ℍ[ℚ]) : ℍ[ℚ]) =
      quaternion_cube_root_squared := by
  have hval : (2 : ZMod 3).val = 2 := rfl
  simp [cyclicOrderThreeToQuaternionUnits, cyclic_order_three_unit_table, hval,
    quaternion_cube_root_squared_unit]

/-- Helper for Exercise 13-13.1-14: the explicit cubic-plane elements commute with every element
coming from the cyclic factor `C3`. -/
theorem quaternion_cubic_pair_to_quaternion_commutes_with_cyclic_image
    (p : ℚ × ℚ) (c : C3) :
    quaternion_cubic_pair_to_quaternion p *
        ((cyclicOrderThreeToQuaternionUnits c : Units ℍ[ℚ]) : ℍ[ℚ]) =
      ((cyclicOrderThreeToQuaternionUnits c : Units ℍ[ℚ]) : ℍ[ℚ]) *
        quaternion_cubic_pair_to_quaternion p := by
  -- It is enough to commute with the generator `ω`; the other two cyclic elements are `1` and
  -- `ω²`.
  have hω :
      quaternion_cubic_pair_to_quaternion p * quaternionCubeRootOfUnity =
        quaternionCubeRootOfUnity * quaternion_cubic_pair_to_quaternion p := by
    refine
      (commutes_with_quaternion_cube_root_iff_equal_im_coordinates
        (q := quaternion_cubic_pair_to_quaternion p)).2 ?_
    constructor
    · have hp := quaternion_cubic_pair_to_quaternion_imJ_imK p
      have hpi := quaternion_cubic_pair_to_quaternion_re_imI p
      exact hpi.2.trans hp.1.symm
    · exact (quaternion_cubic_pair_to_quaternion_imJ_imK p).1.trans
        (quaternion_cubic_pair_to_quaternion_imJ_imK p).2.symm
  have hc' :
      ∀ c : C3,
        c = (1 : C3) ∨ c = Multiplicative.ofAdd (1 : ZMod 3) ∨
          c = Multiplicative.ofAdd (2 : ZMod 3) := by
    intro c
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hc :
      c = (1 : C3) ∨ c = Multiplicative.ofAdd (1 : ZMod 3) ∨
        c = Multiplicative.ofAdd (2 : ZMod 3) :=
    hc' c
  rcases hc with rfl | rfl | rfl
  · rw [cyclicOrderThreeToQuaternionUnits_one_val]
    simp
  · simpa [cyclicOrderThreeToQuaternionUnits, cyclic_order_three_unit_table,
      quaternion_cube_root_unit] using hω
  · calc
      quaternion_cubic_pair_to_quaternion p *
          ((cyclicOrderThreeToQuaternionUnits
              (Multiplicative.ofAdd (2 : ZMod 3)) : Units ℍ[ℚ]) : ℍ[ℚ])
        = quaternion_cubic_pair_to_quaternion p *
            quaternion_cube_root_squared := by
              rw [cyclicOrderThreeToQuaternionUnits_two_val]
      _ = (quaternion_cubic_pair_to_quaternion p * quaternionCubeRootOfUnity) *
            quaternionCubeRootOfUnity := by
              rw [quaternion_cube_root_squared_eq]
              simp [mul_assoc]
      _ = (quaternionCubeRootOfUnity * quaternion_cubic_pair_to_quaternion p) *
            quaternionCubeRootOfUnity := by
              rw [hω]
      _ = quaternionCubeRootOfUnity *
            (quaternion_cubic_pair_to_quaternion p * quaternionCubeRootOfUnity) := by
              simp [mul_assoc]
      _ = quaternionCubeRootOfUnity *
            (quaternionCubeRootOfUnity * quaternion_cubic_pair_to_quaternion p) := by
              rw [hω]
      _ = quaternion_cube_root_squared * quaternion_cubic_pair_to_quaternion p := by
              rw [quaternion_cube_root_squared_eq]
              simp [mul_assoc]
      _ = ((cyclicOrderThreeToQuaternionUnits
              (Multiplicative.ofAdd (2 : ZMod 3)) : Units ℍ[ℚ]) : ℍ[ℚ]) *
            quaternion_cubic_pair_to_quaternion p := by
              rw [cyclicOrderThreeToQuaternionUnits_two_val]

/-- Helper for Exercise 13-13.1-14: left multiplication by an element of the explicit cubic plane
is a self-intertwiner of `ρ`. -/
theorem quaternion_cubic_pair_intertwining
    (p : ℚ × ℚ) :
    ∀ g : G0, ∀ x : ℍ[ℚ],
      (LinearMap.mulLeft ℚ (quaternion_cubic_pair_to_quaternion p)) (ρ g x) =
        ρ g ((LinearMap.mulLeft ℚ (quaternion_cubic_pair_to_quaternion p)) x) := by
  -- Right multiplication always commutes with left multiplication, so only the cyclic left factor
  -- needs the cubic-plane commutation check.
  intro g x
  have hcomm := quaternion_cubic_pair_to_quaternion_commutes_with_cyclic_image p g.2
  calc
    (LinearMap.mulLeft ℚ (quaternion_cubic_pair_to_quaternion p)) (ρ g x)
      = quaternion_cubic_pair_to_quaternion p *
          (((cyclicOrderThreeToQuaternionUnits g.2 : Units ℍ[ℚ]) : ℍ[ℚ]) * x *
            ((quaternionGroupTwoToQuaternionUnits g.1⁻¹ : Units ℍ[ℚ]) : ℍ[ℚ])) := by
          rfl
    _ = (quaternion_cubic_pair_to_quaternion p *
          ((cyclicOrderThreeToQuaternionUnits g.2 : Units ℍ[ℚ]) : ℍ[ℚ])) * x *
          ((quaternionGroupTwoToQuaternionUnits g.1⁻¹ : Units ℍ[ℚ]) : ℍ[ℚ]) := by
          simp [mul_assoc]
    _ = (((cyclicOrderThreeToQuaternionUnits g.2 : Units ℍ[ℚ]) : ℍ[ℚ]) *
          quaternion_cubic_pair_to_quaternion p) * x *
          ((quaternionGroupTwoToQuaternionUnits g.1⁻¹ : Units ℍ[ℚ]) : ℍ[ℚ]) := by
          rw [hcomm]
    _ = ((cyclicOrderThreeToQuaternionUnits g.2 : Units ℍ[ℚ]) : ℍ[ℚ]) *
          (quaternion_cubic_pair_to_quaternion p * x) *
          ((quaternionGroupTwoToQuaternionUnits g.1⁻¹ : Units ℍ[ℚ]) : ℍ[ℚ]) := by
          simp [mul_assoc]
    _ = ρ g ((LinearMap.mulLeft ℚ (quaternion_cubic_pair_to_quaternion p)) x) := by
          rfl

/-- Helper for Exercise 13-13.1-14: package the explicit cubic-plane left action as a
self-intertwiner of `ρ`. -/
def quaternion_cubic_pair_to_intertwiner (p : ℚ × ℚ) : (ρ).IntertwiningMap (ρ) :=
  (LinearMap.mulLeft ℚ (quaternion_cubic_pair_to_quaternion p)).intertwiningMap_of_isIntertwiningMap
    ρ ρ (quaternion_cubic_pair_intertwining p)

/-- Helper for Exercise 13-13.1-14: the packaged cubic-plane intertwiner is exactly left
multiplication by the corresponding quaternion. -/
theorem quaternion_cubic_pair_to_intertwiner_apply (p : ℚ × ℚ) (x : ℍ[ℚ]) :
    quaternion_cubic_pair_to_intertwiner p x =
      quaternion_cubic_pair_to_quaternion p * x := by
  rfl

/-- Helper for Exercise 13-13.1-14: the chosen quaternionic cube root is the cubic-plane element
with real coordinate `-1 / 2` and common imaginary coordinate `1 / 2`. -/
theorem quaternion_cube_root_eq_cubic_pair :
    quaternionCubeRootOfUnity =
      quaternion_cubic_pair_to_quaternion (-(1 : ℚ) / 2, 1 / 2) := by
  -- Compare the four Hamilton coordinates of the two explicit formulas.
  ext <;> norm_num [quaternionCubeRootOfUnity, quaternion_cubic_pair_to_quaternion,
    rational_quaternion_basis]

/-- Helper for Exercise 13-13.1-14: the square of the chosen quaternionic cube root is the cubic-
plane element with real coordinate `-1 / 2` and common imaginary coordinate `-1 / 2`. -/
theorem quaternion_cube_root_squared_eq_cubic_pair :
    quaternion_cube_root_squared =
      quaternion_cubic_pair_to_quaternion (-(1 : ℚ) / 2, -(1 : ℚ) / 2) := by
  -- Compare the four Hamilton coordinates after expanding both explicit formulas.
  ext <;> norm_num [quaternion_cube_root_squared, quaternion_cubic_pair_to_quaternion,
    rational_quaternion_basis]

/-- Helper for Exercise 13-13.1-14: every cubic-plane quaternion is an affine-linear combination of
`1` and the chosen cube root of unity. -/
theorem quaternion_cubic_pair_eq_smul_one_add_smul_cube_root (p : ℚ × ℚ) :
    quaternion_cubic_pair_to_quaternion p =
      (p.1 + p.2 : ℚ) • (1 : ℍ[ℚ]) + (2 * p.2 : ℚ) • quaternionCubeRootOfUnity := by
  -- The coefficient of `ω` controls the common imaginary coordinate, while the scalar term fixes
  -- the real coordinate.
  ext <;> simp [quaternion_cubic_pair_to_quaternion, quaternionCubeRootOfUnity,
    rational_quaternion_basis] <;> ring

/-- Helper for Exercise 13-13.1-14: left multiplication by the chosen cube root of unity packaged
as a self-intertwiner. -/
def quaternion_cube_root_intertwiner : (ρ).IntertwiningMap (ρ) :=
  quaternion_cubic_pair_to_intertwiner (-(1 : ℚ) / 2, 1 / 2)

/-- Helper for Exercise 13-13.1-14: the cube-root intertwiner acts by left multiplication with
`quaternionCubeRootOfUnity`. -/
theorem quaternion_cube_root_intertwiner_apply (x : ℍ[ℚ]) :
    quaternion_cube_root_intertwiner x = quaternionCubeRootOfUnity * x := by
  -- Unfold the packaged cubic-plane action and replace the cubic-pair element by the explicit
  -- quaternionic cube root.
  simp [quaternion_cube_root_intertwiner, quaternion_cubic_pair_to_intertwiner_apply,
    quaternion_cube_root_eq_cubic_pair]

/-- Helper for Exercise 13-13.1-14: the packaged cubic-plane intertwiner is always a linear
combination of the identity and the cube-root intertwiner. -/
theorem quaternion_cubic_pair_to_intertwiner_eq_smul_id_add_smul_cube_root
    (p : ℚ × ℚ) :
    quaternion_cubic_pair_to_intertwiner p =
      (p.1 + p.2 : ℚ) • (1 : (ρ).IntertwiningMap (ρ)) +
        (2 * p.2 : ℚ) • quaternion_cube_root_intertwiner := by
  -- Rewrite the acting quaternion in the `1, ω` basis, then evaluate both intertwiners on an
  -- arbitrary quaternion.
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change quaternion_cubic_pair_to_quaternion p * x =
    (p.1 + p.2 : ℚ) • ((1 : (ρ).IntertwiningMap (ρ)) x) +
      (2 * p.2 : ℚ) • (quaternion_cube_root_intertwiner x)
  rw [quaternion_cube_root_intertwiner_apply, quaternion_cubic_pair_eq_smul_one_add_smul_cube_root]
  simp [add_mul, Algebra.smul_def, mul_assoc]

/-- Helper for Exercise 13-13.1-14: every rational quaternion decomposes as a cubic-plane element
plus another cubic-plane element multiplied on the right by `j`. -/
theorem quaternion_exists_cubic_pair_add_mul_j (x : ℍ[ℚ]) :
    ∃ a b : ℚ × ℚ,
      x = quaternion_cubic_pair_to_quaternion a +
        quaternion_cubic_pair_to_quaternion b * rational_quaternion_basis.j := by
  -- Use the explicit Hamilton coordinates to solve for the two cubic-plane coefficients.
  refine
    ⟨(x.re + (x.imK - x.imI) / 2, (x.imI + x.imK) / 2),
      (x.imJ - (x.imI + x.imK) / 2, (x.imK - x.imI) / 2), ?_⟩
  ext <;> simp [quaternion_cubic_pair_to_quaternion, rational_quaternion_basis] <;> ring

/-- Helper for Exercise 13-13.1-14: the elements of `ℍ[ℚ]` commuting with the chosen cube root
form a genuine subfield. -/
def quaternion_cubic_subfield : Subfield ℍ[ℚ] := by
  -- This is the commutative coefficient field predicted by the source proof: the centralizer of
  -- `ω = quaternionCubeRootOfUnity` inside Hamilton's division algebra.
  let S : Subring ℍ[ℚ] :=
    { carrier := {q | q * quaternionCubeRootOfUnity = quaternionCubeRootOfUnity * q}
      zero_mem' := by simp [quaternionCubeRootOfUnity]
      add_mem' := by
        intro a b ha hb
        calc
          (a + b) * quaternionCubeRootOfUnity
              = a * quaternionCubeRootOfUnity + b * quaternionCubeRootOfUnity := by
                  simp [add_mul]
          _ = quaternionCubeRootOfUnity * a + quaternionCubeRootOfUnity * b := by
                rw [ha, hb]
          _ = quaternionCubeRootOfUnity * (a + b) := by
                simp [mul_add]
      one_mem' := by simp [quaternionCubeRootOfUnity]
      mul_mem' := by
        intro a b ha hb
        calc
          (a * b) * quaternionCubeRootOfUnity = a * (b * quaternionCubeRootOfUnity) := by
                simp [mul_assoc]
          _ = a * (quaternionCubeRootOfUnity * b) := by
                rw [hb]
          _ = (a * quaternionCubeRootOfUnity) * b := by
                simp [mul_assoc]
          _ = (quaternionCubeRootOfUnity * a) * b := by
                rw [ha]
          _ = quaternionCubeRootOfUnity * (a * b) := by
                simp [mul_assoc]
      neg_mem' := by
        intro a ha
        calc
          (-a) * quaternionCubeRootOfUnity = -(a * quaternionCubeRootOfUnity) := by
                simp
          _ = -(quaternionCubeRootOfUnity * a) := by
                rw [ha]
          _ = quaternionCubeRootOfUnity * (-a) := by
                simp }
  exact S.toSubfield (by
    intro a ha
    -- Inverses stay in the centralizer because commutation is preserved under inversion in a
    -- division ring.
    have hcomm : Commute a quaternionCubeRootOfUnity := ha
    simpa using hcomm.inv_left₀.eq)

/-- Helper for Exercise 13-13.1-14: the explicit cubic centralizer inside `ℍ[ℚ]` is
commutative. -/
theorem quaternion_cubic_subfield_mul_comm
    (x y : ↥quaternion_cubic_subfield) :
    x * y = y * x := by
  -- Rewrite both cubic-subfield elements in the explicit two-coordinate cubic plane, then compare
  -- the Hamilton coordinates of the products.
  have hxcoords :
      (x : ℍ[ℚ]).imI = (x : ℍ[ℚ]).imJ ∧
        (x : ℍ[ℚ]).imJ = (x : ℍ[ℚ]).imK :=
    (commutes_with_quaternion_cube_root_iff_equal_im_coordinates (q := (x : ℍ[ℚ]))).1 x.2
  have hycoords :
      (y : ℍ[ℚ]).imI = (y : ℍ[ℚ]).imJ ∧
        (y : ℍ[ℚ]).imJ = (y : ℍ[ℚ]).imK :=
    (commutes_with_quaternion_cube_root_iff_equal_im_coordinates (q := (y : ℍ[ℚ]))).1 y.2
  have hxpair :
      (x : ℍ[ℚ]) =
        quaternion_cubic_pair_to_quaternion ((x : ℍ[ℚ]).re, (x : ℍ[ℚ]).imI) :=
    quaternion_eq_cubic_pair_of_equal_im_coordinates
      (q := (x : ℍ[ℚ])) hxcoords.1 hxcoords.2
  have hypair :
      (y : ℍ[ℚ]) =
        quaternion_cubic_pair_to_quaternion ((y : ℍ[ℚ]).re, (y : ℍ[ℚ]).imI) :=
    quaternion_eq_cubic_pair_of_equal_im_coordinates
      (q := (y : ℍ[ℚ])) hycoords.1 hycoords.2
  apply Subtype.ext
  change (x : ℍ[ℚ]) * (y : ℍ[ℚ]) = (y : ℍ[ℚ]) * (x : ℍ[ℚ])
  rw [hxpair, hypair]
  ext <;> simp [quaternion_cubic_pair_to_quaternion, rational_quaternion_basis] <;> ring

/-- Helper for Exercise 13-13.1-14: the cubic centralizer is a commutative ring. -/
instance quaternion_cubic_subfield_commRing : CommRing ↥quaternion_cubic_subfield :=
  -- Route correction: package the cubic centralizer as a commutative coefficient field before
  -- attempting the density and cyclotomic steps.
  { quaternion_cubic_subfield.toDivisionRing with
    mul_comm := quaternion_cubic_subfield_mul_comm }

/-- Helper for Exercise 13-13.1-14: the cubic centralizer is a commutative field over `ℚ`. -/
instance quaternion_cubic_subfield_commField_over_Q : Field ↥quaternion_cubic_subfield :=
  { quaternion_cubic_subfield.toDivisionRing, quaternion_cubic_subfield_commRing with
    mul_comm := quaternion_cubic_subfield_mul_comm }

/-- Helper for Exercise 13-13.1-14: the cubic centralizer inherits characteristic zero from the
rational quaternions. -/
instance quaternion_cubic_subfield_charZero : CharZero ↥quaternion_cubic_subfield := by
  -- Compare natural-number scalars through the real coordinate of the ambient quaternion algebra.
  refine charZero_of_inj_zero ?_
  intro n hn
  have hre : (n : ℚ) = 0 := by
    have hre' := congrArg QuaternionAlgebra.re (congrArg Subtype.val hn)
    simpa using hre'
  exact Nat.cast_injective (R := ℚ) hre

/-- Helper for Exercise 13-13.1-14: the chosen cube root itself lies in the cubic coefficient
subfield. -/
theorem quaternion_cube_root_mem_cubic_subfield :
    quaternionCubeRootOfUnity ∈ quaternion_cubic_subfield := by
  -- The generator commutes with itself.
  change quaternionCubeRootOfUnity * quaternionCubeRootOfUnity =
    quaternionCubeRootOfUnity * quaternionCubeRootOfUnity
  rfl

/-- Helper for Exercise 13-13.1-14: the square of the chosen cube root still lies in the cubic
coefficient subfield. -/
theorem quaternion_cube_root_squared_mem_cubic_subfield :
    quaternion_cube_root_squared ∈ quaternion_cubic_subfield := by
  -- Route correction: package `ω²` through the new subfield owner instead of treating it only as
  -- an ambient quaternion.
  rw [quaternion_cube_root_squared_eq]
  exact Subfield.mul_mem quaternion_cubic_subfield
    quaternion_cube_root_mem_cubic_subfield
    quaternion_cube_root_mem_cubic_subfield

/-- Helper for Exercise 13-13.1-14: every explicit cubic-pair quaternion belongs to the cubic
coefficient subfield. -/
theorem quaternion_cubic_pair_to_quaternion_mem_cubic_subfield (p : ℚ × ℚ) :
    quaternion_cubic_pair_to_quaternion p ∈ quaternion_cubic_subfield := by
  -- The coordinate characterization of the centralizer shows that these are exactly the elements
  -- with equal `i`, `j`, and `k` coordinates.
  change quaternion_cubic_pair_to_quaternion p * quaternionCubeRootOfUnity =
    quaternionCubeRootOfUnity * quaternion_cubic_pair_to_quaternion p
  exact
    (commutes_with_quaternion_cube_root_iff_equal_im_coordinates
      (q := quaternion_cubic_pair_to_quaternion p)).2 <| by
        constructor
        · exact (quaternion_cubic_pair_to_quaternion_re_imI p).2.trans
            ((quaternion_cubic_pair_to_quaternion_imJ_imK p).1.symm)
        · exact (quaternion_cubic_pair_to_quaternion_imJ_imK p).1.trans
            (quaternion_cubic_pair_to_quaternion_imJ_imK p).2.symm

/-- Helper for Exercise 13-13.1-14: every rational quaternion decomposes as `a + b j` with
coefficients `a` and `b` lying in the cubic coefficient subfield. -/
theorem quaternion_exists_cubic_subfield_add_mul_j (x : ℍ[ℚ]) :
    ∃ a b : quaternion_cubic_subfield,
      x = (a : ℍ[ℚ]) + (b : ℍ[ℚ]) * rational_quaternion_basis.j := by
  -- Upgrade the earlier coordinate decomposition from raw pairs to actual elements of the
  -- coefficient subfield.
  rcases quaternion_exists_cubic_pair_add_mul_j x with ⟨a, b, hx⟩
  refine
    ⟨⟨quaternion_cubic_pair_to_quaternion a,
        quaternion_cubic_pair_to_quaternion_mem_cubic_subfield a⟩,
      ⟨quaternion_cubic_pair_to_quaternion b,
        quaternion_cubic_pair_to_quaternion_mem_cubic_subfield b⟩,
      ?_⟩
  exact hx

/-- Helper for Exercise 13-13.1-14: the cubic coefficient field spans `ℍ[ℚ]` with basis-shaped
generators `1` and `j`. -/
theorem quaternion_cubic_subfield_span_one_j :
    Submodule.span quaternion_cubic_subfield
        ({(1 : ℍ[ℚ]), rational_quaternion_basis.j} : Set ℍ[ℚ]) =
      ⊤ := by
  -- The upgraded `a + b j` decomposition shows every quaternion lies in the span of these two
  -- vectors over the new coefficient field.
  rw [eq_top_iff]
  intro x hx
  rcases quaternion_exists_cubic_subfield_add_mul_j x with ⟨a, b, rfl⟩
  apply Submodule.add_mem
  · have h1 :
        (1 : ℍ[ℚ]) ∈
          Submodule.span quaternion_cubic_subfield
            ({(1 : ℍ[ℚ]), rational_quaternion_basis.j} : Set ℍ[ℚ]) := by
      exact Submodule.subset_span (by simp)
    have ha1 : (a : ℍ[ℚ]) = a • (1 : ℍ[ℚ]) := by
      change (a : ℍ[ℚ]) = (a : ℍ[ℚ]) * 1
      simp
    rw [ha1]
    exact
      Submodule.smul_mem
        (Submodule.span quaternion_cubic_subfield
          ({(1 : ℍ[ℚ]), rational_quaternion_basis.j} : Set ℍ[ℚ]))
        a h1
  · have hj :
        rational_quaternion_basis.j ∈
          Submodule.span quaternion_cubic_subfield
            ({(1 : ℍ[ℚ]), rational_quaternion_basis.j} : Set ℍ[ℚ]) := by
      exact Submodule.subset_span (by simp)
    have hbj :
        (b : ℍ[ℚ]) * rational_quaternion_basis.j =
          b • rational_quaternion_basis.j := by
      change (b : ℍ[ℚ]) * rational_quaternion_basis.j =
        (b : ℍ[ℚ]) * rational_quaternion_basis.j
      rfl
    rw [hbj]
    exact
      Submodule.smul_mem
        (Submodule.span quaternion_cubic_subfield
          ({(1 : ℍ[ℚ]), rational_quaternion_basis.j} : Set ℍ[ℚ]))
        b hj

/-- Helper for Exercise 13-13.1-14: the decomposition `a + b j` over the cubic coefficient field
is unique. -/
theorem quaternion_cubic_subfield_add_mul_j_eq_zero_iff
    (a b : quaternion_cubic_subfield) :
    (a : ℍ[ℚ]) + (b : ℍ[ℚ]) * rational_quaternion_basis.j = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    -- Compare the Hamilton coordinates of `a + b j = 0`; the cubic-subfield relations force
    -- both coefficients to vanish.
    have ha_coords :=
      (commutes_with_quaternion_cube_root_iff_equal_im_coordinates (q := (a : ℍ[ℚ]))).1 a.property
    have hb_coords :=
      (commutes_with_quaternion_cube_root_iff_equal_im_coordinates (q := (b : ℍ[ℚ]))).1 b.property
    have hre : (a : ℍ[ℚ]).re + -(b : ℍ[ℚ]).imJ = 0 := by
      simpa [rational_quaternion_basis] using congrArg QuaternionAlgebra.re h
    have hi : (a : ℍ[ℚ]).imI + -(b : ℍ[ℚ]).imK = 0 := by
      simpa [rational_quaternion_basis] using congrArg QuaternionAlgebra.imI h
    have hj : (a : ℍ[ℚ]).imJ + (b : ℍ[ℚ]).re = 0 := by
      simpa [rational_quaternion_basis] using congrArg QuaternionAlgebra.imJ h
    have hk : (a : ℍ[ℚ]).imK + (b : ℍ[ℚ]).imI = 0 := by
      simpa [rational_quaternion_basis] using congrArg QuaternionAlgebra.imK h
    have hb_im_zero : (b : ℍ[ℚ]).imI = 0 := by
      linarith [ha_coords.1, ha_coords.2, hb_coords.1, hb_coords.2, hi, hk]
    have ha_im_zero : (a : ℍ[ℚ]).imI = 0 := by
      linarith [hb_coords.1, hb_coords.2, hi, hb_im_zero]
    have ha_re_zero : (a : ℍ[ℚ]).re = 0 := by
      linarith [hb_coords.1, hre, hb_im_zero]
    have hb_re_zero : (b : ℍ[ℚ]).re = 0 := by
      linarith [ha_coords.1, hj, ha_im_zero]
    have ha_imJ_zero : (a : ℍ[ℚ]).imJ = 0 := by
      linarith [ha_coords.1, ha_im_zero]
    have ha_imK_zero : (a : ℍ[ℚ]).imK = 0 := by
      linarith [ha_coords.2, ha_imJ_zero]
    have hb_imJ_zero : (b : ℍ[ℚ]).imJ = 0 := by
      linarith [hb_coords.1, hb_im_zero]
    have hb_imK_zero : (b : ℍ[ℚ]).imK = 0 := by
      linarith [hb_coords.2, hb_imJ_zero]
    have ha_val : (a : ℍ[ℚ]) = 0 := by
      ext <;> simp [ha_re_zero, ha_im_zero, ha_imJ_zero, ha_imK_zero]
    have hb_val : (b : ℍ[ℚ]) = 0 := by
      ext <;> simp [hb_re_zero, hb_im_zero, hb_imJ_zero, hb_imK_zero]
    constructor
    · exact Subtype.ext ha_val
    · exact Subtype.ext hb_val
  · rintro ⟨rfl, rfl⟩
    -- The converse is immediate once both coefficients are zero.
    simp

/-- Helper for Exercise 13-13.1-14: the vectors `1` and `j` are linearly independent over the
cubic coefficient field. -/
theorem quaternion_cubic_subfield_linearIndependent_one_j :
    LinearIndependent ↥quaternion_cubic_subfield
      ![(1 : ℍ[ℚ]), rational_quaternion_basis.j] := by
  -- Convert a two-term linear relation into the uniqueness statement for `a + b j`.
  rw [LinearIndependent.pair_iff]
  intro a b h
  have h' : (a : ℍ[ℚ]) + (b : ℍ[ℚ]) * rational_quaternion_basis.j = 0 := by
    change (a : ℍ[ℚ]) * (1 : ℍ[ℚ]) + (b : ℍ[ℚ]) * rational_quaternion_basis.j = 0 at h
    simpa using h
  exact (quaternion_cubic_subfield_add_mul_j_eq_zero_iff a b).1 h'

/-- Helper for Exercise 13-13.1-14: the cubic coefficient field acts on `ℍ[ℚ]` with basis
`{1, j}`. -/
theorem quaternion_cubic_subfield_basis_one_j_exists :
    Nonempty (Module.Basis (Fin 2) ↥quaternion_cubic_subfield ℍ[ℚ]) := by
  -- Combine the spanning statement with the new uniqueness lemma to package the desired basis.
  have hrange :
      (Set.range ![(1 : ℍ[ℚ]), rational_quaternion_basis.j]) =
        ({(1 : ℍ[ℚ]), rational_quaternion_basis.j} : Set ℍ[ℚ]) := by
    -- The ordered pair `[1, j]` has exactly the same image set as the two-element set `{1, j}`.
    ext x
    simp [or_comm]
  refine ⟨Module.Basis.mk quaternion_cubic_subfield_linearIndependent_one_j ?_⟩
  rw [hrange, quaternion_cubic_subfield_span_one_j]

/-- Helper for Exercise 13-13.1-14: a chosen basis of `ℍ[ℚ]` over the cubic coefficient field,
ordered as `1, j`. -/
noncomputable def quaternion_cubic_subfield_basis_one_j :
    Module.Basis (Fin 2) ↥quaternion_cubic_subfield ℍ[ℚ] :=
  Classical.choice quaternion_cubic_subfield_basis_one_j_exists

/-- Helper for Exercise 13-13.1-14: over the cubic coefficient field, the quaternion algebra has
dimension `2`. -/
theorem quaternion_cubic_subfield_finrank_eq_two :
    Module.finrank ↥quaternion_cubic_subfield ℍ[ℚ] = 2 := by
  -- The chosen `{1, j}` basis has cardinality `2`.
  let B := quaternion_cubic_subfield_basis_one_j
  change Module.finrank ↥quaternion_cubic_subfield ℍ[ℚ] = Fintype.card (Fin 2)
  exact Module.finrank_eq_card_basis B

/-- Helper for Exercise 13-13.1-14: the Hamilton basis element `i` is `ω + ω² j` in the
`{1, j}` decomposition over the cubic plane. -/
theorem rational_quaternion_i_eq_cube_root_add_cube_root_squared_mul_j :
    (rational_quaternion_basis.i : ℍ[ℚ]) =
      quaternionCubeRootOfUnity +
        quaternion_cube_root_squared * rational_quaternion_basis.j := by
  -- This is the source-proof coordinate identity used to compute the right-action matrices.
  rw [quaternion_cube_root_eq_cubic_pair, quaternion_cube_root_squared_eq_cubic_pair]
  ext <;> norm_num [quaternion_cubic_pair_to_quaternion, rational_quaternion_basis]

/-- Helper for Exercise 13-13.1-14: the product `j i` is `ω² - ω j` in the same cubic-plane
coordinates. -/
theorem rational_quaternion_j_mul_i_eq_cube_root_squared_sub_cube_root_mul_j :
    (rational_quaternion_basis.j : ℍ[ℚ]) * rational_quaternion_basis.i =
      quaternion_cube_root_squared -
        quaternionCubeRootOfUnity * rational_quaternion_basis.j := by
  -- This is the companion coordinate identity for the second basis vector `j`.
  rw [quaternion_cube_root_eq_cubic_pair, quaternion_cube_root_squared_eq_cubic_pair]
  ext <;> norm_num [quaternion_cubic_pair_to_quaternion, rational_quaternion_basis]

/-- Helper for Exercise 13-13.1-14: every element of the cubic coefficient subfield commutes with
the explicit cyclic-image quaternion. -/
theorem quaternion_cubic_subfield_commutes_with_cyclic_image
    (x : quaternion_cubic_subfield) (c : C3) :
    (x : ℍ[ℚ]) * ((cyclicOrderThreeToQuaternionUnits c : Units ℍ[ℚ]) : ℍ[ℚ]) =
      ((cyclicOrderThreeToQuaternionUnits c : Units ℍ[ℚ]) : ℍ[ℚ]) * (x : ℍ[ℚ]) := by
  -- It is enough to commute with the chosen cube root `ω`; the three cyclic values are `1`, `ω`,
  -- and `ω²`.
  have hω :
      (x : ℍ[ℚ]) * quaternionCubeRootOfUnity =
        quaternionCubeRootOfUnity * (x : ℍ[ℚ]) := x.property
  have hc' :
      ∀ c : C3,
        c = (1 : C3) ∨ c = Multiplicative.ofAdd (1 : ZMod 3) ∨
          c = Multiplicative.ofAdd (2 : ZMod 3) := by
    intro c'
    fin_cases c'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases hc' c with rfl | rfl | rfl
  · rw [cyclicOrderThreeToQuaternionUnits_one_val]
    simp
  · simpa [cyclicOrderThreeToQuaternionUnits, cyclic_order_three_unit_table,
      quaternion_cube_root_unit] using hω
  · calc
      (x : ℍ[ℚ]) *
          ((cyclicOrderThreeToQuaternionUnits
              (Multiplicative.ofAdd (2 : ZMod 3)) : Units ℍ[ℚ]) : ℍ[ℚ])
        = (x : ℍ[ℚ]) * quaternion_cube_root_squared := by
            rw [cyclicOrderThreeToQuaternionUnits_two_val]
      _ = ((x : ℍ[ℚ]) * quaternionCubeRootOfUnity) * quaternionCubeRootOfUnity := by
            rw [quaternion_cube_root_squared_eq]
            simp [mul_assoc]
      _ = (quaternionCubeRootOfUnity * (x : ℍ[ℚ])) * quaternionCubeRootOfUnity := by
            rw [hω]
      _ = quaternionCubeRootOfUnity * ((x : ℍ[ℚ]) * quaternionCubeRootOfUnity) := by
            simp [mul_assoc]
      _ = quaternionCubeRootOfUnity * (quaternionCubeRootOfUnity * (x : ℍ[ℚ])) := by
            rw [hω]
      _ = quaternion_cube_root_squared * (x : ℍ[ℚ]) := by
            rw [quaternion_cube_root_squared_eq]
            simp [mul_assoc]
      _ = ((cyclicOrderThreeToQuaternionUnits
              (Multiplicative.ofAdd (2 : ZMod 3)) : Units ℍ[ℚ]) : ℍ[ℚ]) *
            (x : ℍ[ℚ]) := by
            rw [cyclicOrderThreeToQuaternionUnits_two_val]

/-- Helper for Exercise 13-13.1-14: left multiplication by a cubic-subfield element is a
self-intertwiner of the witness representation. -/
theorem quaternion_cubic_subfield_left_mul_intertwining
    (x : quaternion_cubic_subfield) :
    ∀ g : G0, ∀ y : ℍ[ℚ],
      (LinearMap.mulLeft ℚ (x : ℍ[ℚ])) (ρ g y) =
        ρ g ((LinearMap.mulLeft ℚ (x : ℍ[ℚ])) y) := by
  -- Right multiplication always commutes with left multiplication, so only the cyclic left factor
  -- requires the cubic-subfield commutation relation.
  intro g y
  have hcomm := quaternion_cubic_subfield_commutes_with_cyclic_image x g.2
  calc
    (LinearMap.mulLeft ℚ (x : ℍ[ℚ])) (ρ g y)
      = (x : ℍ[ℚ]) *
          (((cyclicOrderThreeToQuaternionUnits g.2 : Units ℍ[ℚ]) : ℍ[ℚ]) * y *
            ((quaternionGroupTwoToQuaternionUnits g.1⁻¹ : Units ℍ[ℚ]) : ℍ[ℚ])) := by
            rfl
    _ = (((x : ℍ[ℚ]) *
          ((cyclicOrderThreeToQuaternionUnits g.2 : Units ℍ[ℚ]) : ℍ[ℚ])) * y) *
          ((quaternionGroupTwoToQuaternionUnits g.1⁻¹ : Units ℍ[ℚ]) : ℍ[ℚ]) := by
            simp [mul_assoc]
    _ = ((((cyclicOrderThreeToQuaternionUnits g.2 : Units ℍ[ℚ]) : ℍ[ℚ]) *
          (x : ℍ[ℚ])) * y) *
          ((quaternionGroupTwoToQuaternionUnits g.1⁻¹ : Units ℍ[ℚ]) : ℍ[ℚ]) := by
            rw [hcomm]
    _ = ((cyclicOrderThreeToQuaternionUnits g.2 : Units ℍ[ℚ]) : ℍ[ℚ]) *
          (((x : ℍ[ℚ]) * y) *
            ((quaternionGroupTwoToQuaternionUnits g.1⁻¹ : Units ℍ[ℚ]) : ℍ[ℚ])) := by
            simp [mul_assoc]
    _ = ((cyclicOrderThreeToQuaternionUnits g.2 : Units ℍ[ℚ]) : ℍ[ℚ]) *
          (((LinearMap.mulLeft ℚ (x : ℍ[ℚ])) y) *
            ((quaternionGroupTwoToQuaternionUnits g.1⁻¹ : Units ℍ[ℚ]) : ℍ[ℚ])) := by
            rfl
    _ = ρ g ((LinearMap.mulLeft ℚ (x : ℍ[ℚ])) y) := by
            simp [quaternionCyclicWitnessRepresentation, quaternion_cyclic_witness_linear,
              mul_assoc]

/-- Helper for Exercise 13-13.1-14: package cubic-subfield left multiplication as a self-
intertwiner of `ρ`. -/
def quaternion_cubic_subfield_to_intertwiner
    (x : quaternion_cubic_subfield) : (ρ).IntertwiningMap (ρ) :=
  (LinearMap.mulLeft ℚ (x : ℍ[ℚ])).intertwiningMap_of_isIntertwiningMap
    ρ ρ (quaternion_cubic_subfield_left_mul_intertwining x)

/-- Helper for Exercise 13-13.1-14: the cubic-subfield intertwiner acts by the expected left
multiplication formula. -/
theorem quaternion_cubic_subfield_to_intertwiner_apply
    (x : quaternion_cubic_subfield) (y : ℍ[ℚ]) :
    quaternion_cubic_subfield_to_intertwiner x y = (x : ℍ[ℚ]) * y := by
  rfl

/-- Helper for Exercise 13-13.1-14: an intertwiner commutes with the full image of the group
algebra action, not just with the group elements themselves. -/
theorem quaternion_cyclic_intertwiner_map_asAlgebraHom
    (T : (ρ).IntertwiningMap (ρ)) (r : MonoidAlgebra ℚ G0) (x : ℍ[ℚ]) :
    T.toLinearMap ((Representation.asAlgebraHom ρ r) x) =
      (Representation.asAlgebraHom ρ r) (T.toLinearMap x) := by
  -- Extend the intertwining relation from the group basis to arbitrary group-algebra elements by
  -- linearity.
  induction r using MonoidAlgebra.induction_linear with
  | zero =>
      simp [Representation.asAlgebraHom]
  | add r s hr hs =>
      simpa [map_add, hr, hs]
  | single g a =>
      simp [Representation.asAlgebraHom_single, T.isIntertwining, LinearMap.map_smul]

/-- Helper for Exercise 13-13.1-14: a self-intertwiner is recovered from its value at `1` as the
corresponding cubic-plane left multiplication map. -/
theorem quaternion_cyclic_intertwiner_eq_cubic_pair_to_intertwiner
    (T : (ρ).IntertwiningMap (ρ)) :
    T = quaternion_cubic_pair_to_intertwiner ((T (1 : ℍ[ℚ])).re, (T (1 : ℍ[ℚ])).imI) := by
  -- Route correction: use the already-established left-multiplication description of every
  -- self-intertwiner instead of introducing a second commutant model.
  have hcomm :=
    quaternion_cyclic_intertwiner_eval_one_commutes_with_quaternion_cube_root T
  have hcoords :
      (T (1 : ℍ[ℚ])).imI = (T (1 : ℍ[ℚ])).imJ ∧
        (T (1 : ℍ[ℚ])).imJ = (T (1 : ℍ[ℚ])).imK :=
    (commutes_with_quaternion_cube_root_iff_equal_im_coordinates
      (q := T (1 : ℍ[ℚ]))).1 hcomm
  have hq :
      T (1 : ℍ[ℚ]) =
        quaternion_cubic_pair_to_quaternion
          ((T (1 : ℍ[ℚ])).re, (T (1 : ℍ[ℚ])).imI) := by
    exact quaternion_eq_cubic_pair_of_equal_im_coordinates
      (q := T (1 : ℍ[ℚ])) hcoords.1 hcoords.2
  let p : ℚ × ℚ := ((T (1 : ℍ[ℚ])).re, (T (1 : ℍ[ℚ])).imI)
  have hp : T (1 : ℍ[ℚ]) = quaternion_cubic_pair_to_quaternion p := by
    simpa [p] using hq
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  calc
    T x = (LinearMap.mulLeft ℚ (T (1 : ℍ[ℚ]))) x := by
      exact congrArg (fun f : ℍ[ℚ] →ₗ[ℚ] ℍ[ℚ] ↦ f x)
        (quaternion_cyclic_intertwiner_eq_mulLeft_of_eval_one T)
    _ = (LinearMap.mulLeft ℚ (quaternion_cubic_pair_to_quaternion p)) x := by
          rw [hp]
    _ = quaternion_cubic_pair_to_quaternion p * x := by
          rfl
    _ = quaternion_cubic_pair_to_intertwiner p x := by
          symm
          exact quaternion_cubic_pair_to_intertwiner_apply p x

/-- Helper for Exercise 13-13.1-14: every self-intertwiner already lies in the `ℚ`-span of the
identity and the cube-root intertwiner. -/
theorem quaternion_cyclic_intertwiner_eq_smul_id_add_smul_cube_root
    (T : (ρ).IntertwiningMap (ρ)) :
    ∃ a b : ℚ,
      T = a • (1 : (ρ).IntertwiningMap (ρ)) + b • quaternion_cube_root_intertwiner := by
  -- Extract the cubic-plane coordinates of `T 1`, then convert that cubic-plane element to the
  -- `1, ω` basis.
  refine
    ⟨(T (1 : ℍ[ℚ])).re + (T (1 : ℍ[ℚ])).imI, 2 * (T (1 : ℍ[ℚ])).imI, ?_⟩
  calc
    T = quaternion_cubic_pair_to_intertwiner ((T (1 : ℍ[ℚ])).re, (T (1 : ℍ[ℚ])).imI) := by
          exact quaternion_cyclic_intertwiner_eq_cubic_pair_to_intertwiner T
    _ =
        ((T (1 : ℍ[ℚ])).re + (T (1 : ℍ[ℚ])).imI : ℚ) • (1 : (ρ).IntertwiningMap (ρ)) +
          (2 * (T (1 : ℍ[ℚ])).imI : ℚ) • quaternion_cube_root_intertwiner := by
            exact quaternion_cubic_pair_to_intertwiner_eq_smul_id_add_smul_cube_root
              ((T (1 : ℍ[ℚ])).re, (T (1 : ℍ[ℚ])).imI)

/-- Helper for Exercise 13-13.1-14: the chosen quaternionic cube root satisfies its defining
quadratic relation. -/
theorem quaternion_cube_root_mul_self_add_self_add_one :
    quaternionCubeRootOfUnity * quaternionCubeRootOfUnity + quaternionCubeRootOfUnity + 1 = 0 := by
  -- This is the polynomial identity `ω² + ω + 1 = 0` checked in Hamilton coordinates.
  ext <;> norm_num [quaternionCubeRootOfUnity]

/-- Helper for Exercise 13-13.1-14: evaluation at `1` identifies the self-intertwiner space with
the explicit two-dimensional cubic plane. -/
theorem quaternion_cyclic_self_intertwining_equiv_cubic_pair_exists :
    Nonempty ((ρ).IntertwiningMap (ρ) ≃ₗ[ℚ] ℚ × ℚ) := by
  -- Route correction: compute `End_G(ρ)` directly by evaluation at `1`, instead of waiting for the
  -- full image-algebra identification.
  refine ⟨{
      toFun := fun T ↦ ((T (1 : ℍ[ℚ])).re, (T (1 : ℍ[ℚ])).imI)
      invFun := quaternion_cubic_pair_to_intertwiner
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_ }⟩
  · intro T S
    ext <;> simp
  · intro a T
    ext <;> simp
  · intro T
    -- Reconstruct `T 1` from its cubic-plane coordinates, then appeal to the left-multiplication
    -- description of every self-intertwiner.
    have hcomm :=
      quaternion_cyclic_intertwiner_eval_one_commutes_with_quaternion_cube_root T
    have hcoords :
        (T (1 : ℍ[ℚ])).imI = (T (1 : ℍ[ℚ])).imJ ∧
          (T (1 : ℍ[ℚ])).imJ = (T (1 : ℍ[ℚ])).imK :=
      (commutes_with_quaternion_cube_root_iff_equal_im_coordinates
        (q := T (1 : ℍ[ℚ]))).1 hcomm
    have hq :
        T (1 : ℍ[ℚ]) =
          quaternion_cubic_pair_to_quaternion
            ((T (1 : ℍ[ℚ])).re, (T (1 : ℍ[ℚ])).imI) := by
      exact quaternion_eq_cubic_pair_of_equal_im_coordinates
        (q := T (1 : ℍ[ℚ])) hcoords.1 hcoords.2
    apply IntertwiningMap.ext
    calc
      (quaternion_cubic_pair_to_intertwiner
          ((T (1 : ℍ[ℚ])).re, (T (1 : ℍ[ℚ])).imI)).toLinearMap
        =
          LinearMap.mulLeft ℚ
            (quaternion_cubic_pair_to_quaternion
              ((T (1 : ℍ[ℚ])).re, (T (1 : ℍ[ℚ])).imI)) := by
                rfl
      _ = LinearMap.mulLeft ℚ (T (1 : ℍ[ℚ])) := by
            rw [← hq]
      _ = T.toLinearMap := (quaternion_cyclic_intertwiner_eq_mulLeft_of_eval_one T).symm
  · intro p
    -- Evaluating the constructed left-multiplication intertwiner at `1` recovers the two cubic
    -- coordinates by inspection.
    ext <;> simp [quaternion_cubic_pair_to_intertwiner_apply,
      quaternion_cubic_pair_to_quaternion_re_imI]

/-- Helper for Exercise 13-13.1-14: a chosen explicit linear equivalence between the self-
intertwiner space of `ρ` and the cubic plane `ℚ²`. -/
noncomputable def quaternion_cyclic_self_intertwining_equiv_cubic_pair :
    (ρ).IntertwiningMap (ρ) ≃ₗ[ℚ] ℚ × ℚ :=
  Classical.choice quaternion_cyclic_self_intertwining_equiv_cubic_pair_exists

/-- Helper for Exercise 13-13.1-14: the self-intertwiner algebra of `ρ` is two-dimensional over
`ℚ`. -/
theorem quaternion_cyclic_self_intertwining_finrank_eq_two :
    Module.finrank ℚ ((ρ).IntertwiningMap (ρ)) = 2 := by
  -- Transport the calculation through the explicit linear equivalence with `ℚ²`.
  let e := quaternion_cyclic_self_intertwining_equiv_cubic_pair
  calc
    Module.finrank ℚ ((ρ).IntertwiningMap (ρ)) = Module.finrank ℚ (ℚ × ℚ) := e.finrank_eq
    _ = 2 := by
          norm_num

/-- Helper for Exercise 13-13.1-14: the rational quaternion space has dimension `4` over `ℚ`. -/
theorem rational_quaternion_finrank_eq_four :
    Module.finrank ℚ ℍ[ℚ] = 4 := by
  -- Use the standard Hamilton basis `1, i, j, k`.
  let B : Module.Basis (Fin 4) ℚ ℍ[ℚ] :=
    QuaternionAlgebra.basisOneIJK (-1 : ℚ) 0 (-1 : ℚ)
  simpa [B] using Module.finrank_eq_card_basis B

/-- Helper for Exercise 13-13.1-14: the image algebra of the witness representation inside
`Endℚ(ℍ[ℚ])`. -/
abbrev quaternion_cyclic_imageSubalgebra : Subalgebra ℚ (Module.End ℚ ℍ[ℚ]) :=
  (ρ).asAlgebraHom.range

/-- Helper for Exercise 13-13.1-14: `ℍ[ℚ]` carries the tautological module structure over the
image algebra of `ρ`. -/
instance quaternion_cyclic_imageSubalgebra_module :
    Module quaternion_cyclic_imageSubalgebra ℍ[ℚ] :=
  Module.compHom ℍ[ℚ] (Subalgebra.val quaternion_cyclic_imageSubalgebra).toRingHom

/-- Helper for Exercise 13-13.1-14: the image-algebra action is compatible with the ambient
`ℚ`-linear structure. -/
instance quaternion_cyclic_imageSubalgebra_isScalarTower :
    IsScalarTower ℚ quaternion_cyclic_imageSubalgebra ℍ[ℚ] := by
  refine ⟨?_⟩
  intro q b x
  rfl

/-- Helper for Exercise 13-13.1-14: simplicity descends along a surjective ring homomorphism
when the two scalar actions are compared by the identity semilinear map. -/
theorem isSimpleModule_of_ringHom_surjective
    {R A M : Type*} [Ring R] [Ring A] [AddCommGroup M] [Module A M]
    (q : R →+* A) (hq : Function.Surjective q)
    (hM : let _ : Module R M := Module.compHom M q
      IsSimpleModule R M) :
    IsSimpleModule A M := by
  -- Restriction of scalars along a surjection does not change the lattice of submodules.
  let _ : Module R M := Module.compHom M q
  letI : RingHomSurjective q := ⟨hq⟩
  let l : M →ₛₗ[q] M :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hbij : Function.Bijective l := by
    constructor
    · intro x y hxy
      exact hxy
    · intro x
      exact ⟨x, rfl⟩
  exact (l.isSimpleModule_iff_of_bijective hbij).mp hM

/-- Helper for Exercise 13-13.1-14: the image algebra acts simply on `ℍ[ℚ]`. -/
theorem quaternion_cyclic_imageSubalgebra_isSimpleModule :
    IsSimpleModule quaternion_cyclic_imageSubalgebra ℍ[ℚ] := by
  -- Descend the simple `ℚ[G]`-module structure of `ρ` along the surjective range map.
  have hsimple :
      let _ : Module (MonoidAlgebra ℚ G0) ℍ[ℚ] :=
        Module.compHom ℍ[ℚ]
          ((Subalgebra.val quaternion_cyclic_imageSubalgebra).toRingHom.comp
            (AlgHom.rangeRestrict (Representation.asAlgebraHom ρ)).toRingHom)
      IsSimpleModule (MonoidAlgebra ℚ G0) ℍ[ℚ] := by
    simpa [quaternion_cyclic_imageSubalgebra] using
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp
        quaternion_cyclic_witness_isIrreducible
  exact
    isSimpleModule_of_ringHom_surjective
      (q := (AlgHom.rangeRestrict (Representation.asAlgebraHom ρ)).toRingHom)
      (hq := AlgHom.rangeRestrict_surjective (Representation.asAlgebraHom ρ))
      hsimple

/-- Helper for Exercise 13-13.1-14: a `quaternion_cyclic_imageSubalgebra`-linear endomorphism of
`ℍ[ℚ]` is automatically a self-intertwiner of the original representation `ρ`. -/
def quaternion_cyclic_end_to_intertwiner
    (T : Module.End quaternion_cyclic_imageSubalgebra ℍ[ℚ]) : (ρ).IntertwiningMap (ρ) :=
  (T.restrictScalars ℚ).intertwiningMap_of_isIntertwiningMap ρ ρ <| by
    -- Every group operator already lies in the image algebra, so `T` commutes with it by
    -- `quaternion_cyclic_imageSubalgebra`-linearity.
    intro g x
    let bg : quaternion_cyclic_imageSubalgebra :=
      ⟨ρ g, ⟨MonoidAlgebra.of ℚ G0 g, by
        simpa [Representation.asAlgebraHom_single]⟩⟩
    change T (bg • x) = bg • T x
    exact T.map_smul bg x

/-- Helper for Exercise 13-13.1-14: the previous conversion does not change the underlying
function on `ℍ[ℚ]`. -/
theorem quaternion_cyclic_end_to_intertwiner_apply
    (T : Module.End quaternion_cyclic_imageSubalgebra ℍ[ℚ]) (x : ℍ[ℚ]) :
    quaternion_cyclic_end_to_intertwiner T x = T x := by
  rfl

/-- Helper for Exercise 13-13.1-14: left multiplication by a cubic-subfield element is already
linear over the image algebra. -/
def quaternion_cubic_subfield_to_end
    (x : ↥quaternion_cubic_subfield) :
    Module.End quaternion_cyclic_imageSubalgebra ℍ[ℚ] where
  toFun := fun y ↦ (x : ℍ[ℚ]) * y
  map_add' _ _ := by simp [mul_add]
  map_smul' := by
    -- Commute the left multiplication map past an arbitrary image-algebra element by lifting that
    -- element back to the group algebra and using the intertwiner identity already proved above.
    intro b y
    rcases b with ⟨b, hb⟩
    rcases hb with ⟨r, rfl⟩
    simpa [quaternion_cubic_subfield_to_intertwiner_apply] using
      quaternion_cyclic_intertwiner_map_asAlgebraHom
        (T := quaternion_cubic_subfield_to_intertwiner x) r y

/-- Helper for Exercise 13-13.1-14: the `quaternion_cyclic_imageSubalgebra`-linear endomorphism
coming from a cubic-subfield element acts by the expected left-multiplication formula. -/
theorem quaternion_cubic_subfield_to_end_apply
    (x : ↥quaternion_cubic_subfield) (y : ℍ[ℚ]) :
    quaternion_cubic_subfield_to_end x y = (x : ℍ[ℚ]) * y := by
  rfl

/-- Helper for Exercise 13-13.1-14: evaluation at `1` identifies the commutant of the image
algebra with the explicit cubic subfield. -/
def quaternion_cyclic_end_ringEquiv_cubic_subfield :
    Module.End quaternion_cyclic_imageSubalgebra ℍ[ℚ] ≃+* ↥quaternion_cubic_subfield where
  toFun := fun T ↦
    ⟨T 1,
      quaternion_cyclic_intertwiner_eval_one_commutes_with_quaternion_cube_root
        (quaternion_cyclic_end_to_intertwiner T)⟩
  invFun := quaternion_cubic_subfield_to_end
  left_inv := by
    intro T
    -- Compare both endomorphisms pointwise after identifying every intertwiner with left
    -- multiplication by its value at `1`.
    apply DFunLike.ext
    intro x
    calc
      quaternion_cubic_subfield_to_end
          ⟨T 1,
            quaternion_cyclic_intertwiner_eval_one_commutes_with_quaternion_cube_root
              (quaternion_cyclic_end_to_intertwiner T)⟩ x
        = (T 1) * x := by
            rfl
      _ = quaternion_cyclic_end_to_intertwiner T x := by
            symm
            exact congrArg (fun f : ℍ[ℚ] →ₗ[ℚ] ℍ[ℚ] ↦ f x)
              (quaternion_cyclic_intertwiner_eq_mulLeft_of_eval_one
                (quaternion_cyclic_end_to_intertwiner T))
      _ = T x := by
            simp [quaternion_cyclic_end_to_intertwiner_apply]
  right_inv := by
    intro x
    -- Evaluating the left-multiplication endomorphism at `1` recovers the original cubic-field
    -- element.
    apply Subtype.ext
    change (x : ℍ[ℚ]) * (1 : ℍ[ℚ]) = (x : ℍ[ℚ])
    simp
  map_mul' := by
    intro T S
    -- Multiplication on the commutant side is composition, so evaluation at `1` turns it into
    -- multiplication in the cubic field.
    apply Subtype.ext
    change (T * S) 1 = (T 1 : ℍ[ℚ]) * (S 1 : ℍ[ℚ])
    calc
      (T * S) 1 = T (S 1) := by
        rfl
      _ = quaternion_cyclic_end_to_intertwiner T (S 1) := by
            simp [quaternion_cyclic_end_to_intertwiner_apply]
      _ = (T 1 : ℍ[ℚ]) * S 1 := by
            have hmul := congrArg (fun f : ℍ[ℚ] →ₗ[ℚ] ℍ[ℚ] ↦ f (S 1))
              (quaternion_cyclic_intertwiner_eq_mulLeft_of_eval_one
                (quaternion_cyclic_end_to_intertwiner T))
            simpa [quaternion_cyclic_end_to_intertwiner_apply] using hmul
  map_add' := by
    intro T S
    rfl

/-- Helper for Exercise 13-13.1-14: an image-algebra endomorphism acts by left multiplication with
its cubic-subfield scalar. -/
theorem quaternion_cyclic_end_ringEquiv_cubic_subfield_smul_eq_apply
    (T : Module.End quaternion_cyclic_imageSubalgebra ℍ[ℚ]) (y : ℍ[ℚ]) :
    (((quaternion_cyclic_end_ringEquiv_cubic_subfield T : quaternion_cubic_subfield) : ℍ[ℚ]) * y =
      T y) := by
  -- Evaluate the inverse side of the commutant equivalence at `y` and unfold the explicit
  -- left-multiplication model.
  have h :=
    congrArg (fun S : Module.End quaternion_cyclic_imageSubalgebra ℍ[ℚ] ↦ S y)
      (quaternion_cyclic_end_ringEquiv_cubic_subfield.left_inv T)
  change
    quaternion_cubic_subfield_to_end (quaternion_cyclic_end_ringEquiv_cubic_subfield T) y =
      T y at h
  simpa [quaternion_cubic_subfield_to_end_apply] using h

/-- Helper for Exercise 13-13.1-14: every `quaternion_cubic_subfield`-linear endomorphism is
automatically linear over the commutant `End_A(ℍ[ℚ])`. -/
def quaternion_cyclic_cubic_linear_to_end_linear
    (f : Module.End ↥quaternion_cubic_subfield ℍ[ℚ]) :
    Module.End (Module.End quaternion_cyclic_imageSubalgebra ℍ[ℚ]) ℍ[ℚ] where
  toFun := f
  map_add' x y := f.map_add x y
  map_smul' := by
    intro T y
    -- Rewrite the commutant scalar action as left multiplication by its cubic-field element, then
    -- use the original `quaternion_cubic_subfield`-linearity of `f`.
    change f (T y) = T (f y)
    rw [← quaternion_cyclic_end_ringEquiv_cubic_subfield_smul_eq_apply T y]
    rw [← quaternion_cyclic_end_ringEquiv_cubic_subfield_smul_eq_apply T (f y)]
    exact f.map_smul (quaternion_cyclic_end_ringEquiv_cubic_subfield T) y

/-- Helper for Exercise 13-13.1-14: the image algebra action commutes with the cubic-subfield
left action on `ℍ[ℚ]`. -/
instance quaternion_cyclic_imageSubalgebra_smulCommClass_cubic_subfield :
    SMulCommClass quaternion_cyclic_imageSubalgebra ↥quaternion_cubic_subfield ℍ[ℚ] where
  smul_comm a x y := by
    -- Lift an image-algebra element back to the group algebra and use the already proved
    -- intertwining relation for left multiplication by a cubic-subfield element.
    rcases a with ⟨a, ha⟩
    rcases ha with ⟨r, rfl⟩
    change
      (Representation.asAlgebraHom quaternionCyclicWitnessRepresentation r)
          ((x : ℍ[ℚ]) * y) =
        (x : ℍ[ℚ]) *
          (Representation.asAlgebraHom quaternionCyclicWitnessRepresentation r y)
    symm
    simpa [quaternion_cubic_subfield_to_intertwiner_apply] using
      quaternion_cyclic_intertwiner_map_asAlgebraHom
        (T := quaternion_cubic_subfield_to_intertwiner x) r y

end

end Representation
