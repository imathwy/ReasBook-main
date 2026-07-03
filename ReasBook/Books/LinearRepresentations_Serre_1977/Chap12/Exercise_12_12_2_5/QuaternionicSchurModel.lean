import Mathlib
import LinearRepresentations_Serre_1977.Chap12.Corollary_12_12_2_2

noncomputable section

open scoped MonoidAlgebra Quaternion TensorProduct

universe u v w

namespace Representation

section

variable {G : Type u} [Group G]

/-- The subfield of `ℂ` generated over `ℚ` by the values of the complex character `χ`. -/
abbrev characterField (χ : G → ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range χ)

def RealizableOverCharacterField (χ : G → ℂ) (m : ℕ+) : Prop :=
  ∃ (τ : Rep.{w} (characterField χ) G) (_ : FiniteDimensional (characterField χ) τ),
    (fun g ↦ algebraMap (characterField χ) ℂ ((τ.ρ.character) g)) =
      (((m : ℕ) : ℂ) • χ)

/-- A complex character has Schur index `m` if `m χ` is realizable over the character field and
`m` is minimal with this property. -/
def HasSchurIndex (χ : G → ℂ) (m : ℕ+) : Prop :=
  RealizableOverCharacterField.{u, w} χ m ∧
    ∀ n : ℕ+, RealizableOverCharacterField.{u, w} χ n → m ≤ n

/-- Unfolding `HasSchurIndex χ m` identifies it with realizability of `m χ` over the character
field of `χ`, together with minimality of the positive integer `m`. -/
theorem hasSchurIndex_iff (χ : G → ℂ) (m : ℕ+) :
    HasSchurIndex.{u, w} χ m ↔
      (∃ (τ : Rep.{w} (characterField χ) G) (_ : FiniteDimensional (characterField χ) τ),
        (fun g ↦ algebraMap (characterField χ) ℂ ((τ.ρ.character) g)) =
          (((m : ℕ) : ℂ) • χ)) ∧
        ∀ n : ℕ+, (∃ (τ : Rep.{w} (characterField χ) G)
          (_ : FiniteDimensional (characterField χ) τ),
          (fun g ↦ algebraMap (characterField χ) ℂ ((τ.ρ.character) g)) =
            (((n : ℕ) : ℂ) • χ)) → m ≤ n :=
  by
    rfl

end

section

local notation "Q8" => QuaternionGroup 2

/-- The complex irreducible character attached to the quaternionic simple component of `ℚ[Q8]`. -/
def quaternionGroupTwoQuaternionCharacter : Q8 → ℂ
  | QuaternionGroup.a i => if i = 0 then 2 else if i = 2 then -2 else 0
  | QuaternionGroup.xa _ => 0

/-- Helper for Exercise 12-12.2-5: every value of the quaternionic `Q8` character already lies in
the image of `ℚ → ℂ`. -/
theorem quaternionGroupTwoQuaternionCharacter_is_rational_valued (s : Q8) :
    ∃ q : ℚ, algebraMap ℚ ℂ q = quaternionGroupTwoQuaternionCharacter s := by
  -- Split over the two normal forms in `Q8` and read off the values `2`, `-2`, and `0`.
  cases s with
  | a i =>
      -- On the `a i` branch only the cases `i = 0` and `i = 2` contribute nonzero values.
      by_cases h0 : i = 0
      · subst h0
        refine ⟨2, ?_⟩
        simp [quaternionGroupTwoQuaternionCharacter]
      · by_cases h2 : i = 2
        · subst h2
          refine ⟨-2, ?_⟩
          simp [quaternionGroupTwoQuaternionCharacter, h0]
        · refine ⟨0, ?_⟩
          simp [quaternionGroupTwoQuaternionCharacter, h0, h2]
  | xa i =>
      -- The `xa i` branch vanishes identically.
      refine ⟨0, ?_⟩
      simp [quaternionGroupTwoQuaternionCharacter]

/-- Helper for Exercise 12-12.2-5: the standard Hamilton basis on the rational quaternion algebra
`ℍ[ℚ]`. -/
def rationalQuaternionBasis :
    QuaternionAlgebra.Basis ℍ[ℚ] (-1 : ℚ) 0 (-1 : ℚ) :=
  QuaternionAlgebra.Basis.self ℚ

/-- Helper for Exercise 12-12.2-5: the rational quaternion basis element `i` squares to `-1`. -/
theorem rational_quaternion_i_sq :
    (rationalQuaternionBasis.i : ℍ[ℚ]) * rationalQuaternionBasis.i = (-1 : ℍ[ℚ]) := by
  -- This is the Hamilton relation built into the canonical quaternion basis.
  simpa [rationalQuaternionBasis] using rationalQuaternionBasis.i_mul_i

/-- Helper for Exercise 12-12.2-5: the rational quaternion basis element `j` squares to `-1`. -/
theorem rational_quaternion_j_sq :
    (rationalQuaternionBasis.j : ℍ[ℚ]) * rationalQuaternionBasis.j = (-1 : ℍ[ℚ]) := by
  -- This is the second Hamilton relation built into the canonical quaternion basis.
  simpa [rationalQuaternionBasis] using rationalQuaternionBasis.j_mul_j

/-- Helper for Exercise 12-12.2-5: the rational quaternion basis satisfies `ij = k`. -/
theorem rational_quaternion_i_mul_j :
    (rationalQuaternionBasis.i : ℍ[ℚ]) * rationalQuaternionBasis.j =
      rationalQuaternionBasis.k := by
  -- The basis is chosen so that the source-side generator relation is literal.
  simpa [rationalQuaternionBasis] using rationalQuaternionBasis.i_mul_j

/-- Helper for Exercise 12-12.2-5: the rational quaternion basis satisfies `ji = -k`. -/
theorem rational_quaternion_j_mul_i :
    (rationalQuaternionBasis.j : ℍ[ℚ]) * rationalQuaternionBasis.i =
      -rationalQuaternionBasis.k := by
  -- This is the anticommutation relation needed for the quaternionic `Q8` model.
  simpa [rationalQuaternionBasis] using rationalQuaternionBasis.j_mul_i

/-- Helper for Exercise 12-12.2-5: the rational quaternion basis element `i` is a unit. -/
def quaternionIUnit : Units ℍ[ℚ] where
  val := rationalQuaternionBasis.i
  inv := -rationalQuaternionBasis.i
  val_inv := by
    -- Use `i² = -1` to identify the inverse with `-i`.
    rw [mul_neg, rational_quaternion_i_sq]
    norm_num
  inv_val := by
    -- The same Hamilton relation gives the inverse on the other side.
    rw [neg_mul, rational_quaternion_i_sq]
    norm_num

/-- Helper for Exercise 12-12.2-5: the rational quaternion basis element `j` is a unit. -/
def quaternionJUnit : Units ℍ[ℚ] where
  val := rationalQuaternionBasis.j
  inv := -rationalQuaternionBasis.j
  val_inv := by
    -- Use `j² = -1` to identify the inverse with `-j`.
    rw [mul_neg, rational_quaternion_j_sq]
    norm_num
  inv_val := by
    -- The same Hamilton relation gives the inverse on the other side.
    rw [neg_mul, rational_quaternion_j_sq]
    norm_num

/-- Helper for Exercise 12-12.2-5: the unit `i` in `ℍ[ℚ]ˣ` has square `-1`. -/
theorem quaternionIUnit_sq :
    quaternionIUnit ^ 2 = (-1 : Units ℍ[ℚ]) := by
  -- Compare the four quaternion coordinates after expanding the square.
  ext <;> norm_num [pow_two, quaternionIUnit, rationalQuaternionBasis, rational_quaternion_i_sq]

/-- Helper for Exercise 12-12.2-5: the unit `j` in `ℍ[ℚ]ˣ` has square `-1`. -/
theorem quaternionJUnit_sq :
    quaternionJUnit ^ 2 = (-1 : Units ℍ[ℚ]) := by
  -- Compare the four quaternion coordinates after expanding the square.
  ext <;> norm_num [pow_two, quaternionJUnit, rationalQuaternionBasis, rational_quaternion_j_sq]

/-- Helper for Exercise 12-12.2-5: the quaternionic generators anticommute in `ℍ[ℚ]ˣ`. -/
theorem quaternion_units_anticommute :
    quaternionJUnit * quaternionIUnit = -(quaternionIUnit * quaternionJUnit) := by
  -- Compare the four quaternion coordinates after expanding both products.
  ext <;> norm_num [quaternionIUnit, quaternionJUnit, rationalQuaternionBasis,
    rational_quaternion_i_mul_j, rational_quaternion_j_mul_i]

/-- Helper for Exercise 12-12.2-5: the quaternionic unit `k = ij` inside `ℍ[ℚ]ˣ`. -/
def quaternionKUnit : Units ℍ[ℚ] :=
  quaternionIUnit * quaternionJUnit

/-- Helper for Exercise 12-12.2-5: the underlying quaternion of `k = ij` is the basis element
`k`. -/
@[simp] theorem quaternionKUnit_val :
    ((quaternionKUnit : Units ℍ[ℚ]) : ℍ[ℚ]) = rationalQuaternionBasis.k := by
  -- Unfold `k = ij` and use the Hamilton relation on the chosen quaternion basis.
  change ((quaternionIUnit : Units ℍ[ℚ]) : ℍ[ℚ]) * ((quaternionJUnit : Units ℍ[ℚ]) : ℍ[ℚ]) =
    rationalQuaternionBasis.k
  simpa [quaternionIUnit, quaternionJUnit] using rational_quaternion_i_mul_j

/-- Helper for Exercise 12-12.2-5: the explicit eight-value table in `ℍ[ℚ]ˣ` matching the usual
quaternion labels `±1, ±i, ±j, ±k`. -/
def quaternionGroupTwoUnitTable : Q8 → Units ℍ[ℚ]
  | QuaternionGroup.a i =>
      match i.val with
      | 0 => 1
      | 1 => quaternionIUnit
      | 2 => -1
      | _ => -quaternionIUnit
  | QuaternionGroup.xa i =>
      match i.val with
      | 0 => quaternionJUnit
      | 1 => -quaternionKUnit
      | 2 => -quaternionJUnit
      | _ => quaternionKUnit

/-- Helper for Exercise 12-12.2-5: the table sends `a 1` to the quaternion unit `i`. -/
theorem quaternionGroupTwoUnitTable_a_one :
    quaternionGroupTwoUnitTable (QuaternionGroup.a (1 : ZMod 4)) = quaternionIUnit := by
  -- Reduce the `ZMod 4` index to its concrete value in the explicit source-side table.
  have hval : (1 : ZMod 4).val = 1 := rfl
  simp [quaternionGroupTwoUnitTable, hval]

/-- Helper for Exercise 12-12.2-5: the table sends the central involution `a 2` to `-1`. -/
theorem quaternionGroupTwoUnitTable_a_two :
    quaternionGroupTwoUnitTable (QuaternionGroup.a (2 : ZMod 4)) = (-1 : Units ℍ[ℚ]) := by
  -- This is the source-side identification of `-1 ∈ Q8` with `-1 ∈ ℍ[ℚ]ˣ`.
  have hval : (2 : ZMod 4).val = 2 := rfl
  simp [quaternionGroupTwoUnitTable, hval]

/-- Helper for Exercise 12-12.2-5: the table sends `a 3 = -i` to the negative quaternion unit
`-i`. -/
theorem quaternionGroupTwoUnitTable_a_three :
    quaternionGroupTwoUnitTable (QuaternionGroup.a (3 : ZMod 4)) = -quaternionIUnit := by
  -- The final `a`-entry in the explicit table is the negative of `i`.
  have hval : (3 : ZMod 4).val = 3 := rfl
  simp [quaternionGroupTwoUnitTable, hval]

/-- Helper for Exercise 12-12.2-5: the table sends `xa 0` to the quaternion unit `j`. -/
theorem quaternionGroupTwoUnitTable_xa_zero :
    quaternionGroupTwoUnitTable (QuaternionGroup.xa (0 : ZMod 4)) = quaternionJUnit := by
  -- The `xa` branch starts from `j` before adding powers of `i`.
  have hval : (0 : ZMod 4).val = 0 := rfl
  simp [quaternionGroupTwoUnitTable, hval]

/-- Helper for Exercise 12-12.2-5: the table sends `xa 1 = x a` to `-k = ji`. -/
theorem quaternionGroupTwoUnitTable_xa_one :
    quaternionGroupTwoUnitTable (QuaternionGroup.xa (1 : ZMod 4)) = -quaternionKUnit := by
  -- The source-side relation `x a = j i = -k` fixes the orientation of the table.
  have hval : (1 : ZMod 4).val = 1 := rfl
  simp [quaternionGroupTwoUnitTable, hval]

/-- Helper for Exercise 12-12.2-5: the table sends `xa 2 = -j` to the negative quaternion unit
`-j`. -/
theorem quaternionGroupTwoUnitTable_xa_two :
    quaternionGroupTwoUnitTable (QuaternionGroup.xa (2 : ZMod 4)) = -quaternionJUnit := by
  -- The third `xa`-entry is the negative of `j`.
  have hval : (2 : ZMod 4).val = 2 := rfl
  simp [quaternionGroupTwoUnitTable, hval]

/-- Helper for Exercise 12-12.2-5: the table sends `xa 3 = x a^3` to the quaternion unit `k`. -/
theorem quaternionGroupTwoUnitTable_xa_three :
    quaternionGroupTwoUnitTable (QuaternionGroup.xa (3 : ZMod 4)) = quaternionKUnit := by
  -- The final `xa` entry in the explicit table is the positive quaternion unit `k = ij`.
  have hval : (3 : ZMod 4).val = 3 := rfl
  simp [quaternionGroupTwoUnitTable, hval]

/-- Helper for Exercise 12-12.2-5: the source-side quaternion unit `k = ij` also squares to
`-1`. -/
theorem quaternionKUnit_sq :
    quaternionKUnit ^ 2 = (-1 : Units ℍ[ℚ]) := by
  -- Compare the four quaternion coordinates after expanding `(ij)^2`.
  ext <;> norm_num [quaternionKUnit, pow_two, quaternionIUnit, quaternionJUnit,
    rationalQuaternionBasis, rational_quaternion_i_sq, rational_quaternion_j_sq,
    rational_quaternion_i_mul_j, rational_quaternion_j_mul_i]

/-- Helper for Exercise 12-12.2-5: the unit `k = ij` multiplies with itself to `-1`. -/
@[simp] theorem quaternionKUnit_mul_self :
    quaternionKUnit * quaternionKUnit = (-1 : Units ℍ[ℚ]) := by
  -- Rewrite the square into the already established power relation.
  simpa [pow_two] using quaternionKUnit_sq

/-- Helper for Exercise 12-12.2-5: the quaternionic unit `k` is the product `ij`. -/
@[simp] theorem quaternionIUnit_mul_jUnit :
    quaternionIUnit * quaternionJUnit = quaternionKUnit := by
  rfl

/-- Helper for Exercise 12-12.2-5: the Hamilton relation `ji = -k` in `ℍ[ℚ]ˣ`. -/
@[simp] theorem quaternionJUnit_mul_iUnit :
    quaternionJUnit * quaternionIUnit = -quaternionKUnit := by
  -- Compare quaternion coordinates after expanding both sides.
  ext <;> norm_num [quaternionKUnit, quaternionIUnit, quaternionJUnit, rationalQuaternionBasis,
    rational_quaternion_i_mul_j, rational_quaternion_j_mul_i]

/-- Helper for Exercise 12-12.2-5: the Hamilton relation `ik = -j` in `ℍ[ℚ]ˣ`. -/
@[simp] theorem quaternionIUnit_mul_kUnit :
    quaternionIUnit * quaternionKUnit = -quaternionJUnit := by
  -- Compare quaternion coordinates after expanding `i * (ij)`.
  ext <;> norm_num [quaternionKUnit, quaternionIUnit, quaternionJUnit, rationalQuaternionBasis,
    rational_quaternion_i_sq, rational_quaternion_j_sq, rational_quaternion_i_mul_j,
    rational_quaternion_j_mul_i]

/-- Helper for Exercise 12-12.2-5: the Hamilton relation `ki = j` in `ℍ[ℚ]ˣ`. -/
@[simp] theorem quaternionKUnit_mul_iUnit :
    quaternionKUnit * quaternionIUnit = quaternionJUnit := by
  -- Compare quaternion coordinates after expanding `(ij) * i`.
  ext <;> norm_num [quaternionKUnit, quaternionIUnit, quaternionJUnit, rationalQuaternionBasis,
    rational_quaternion_i_sq, rational_quaternion_j_sq, rational_quaternion_i_mul_j,
    rational_quaternion_j_mul_i]

/-- Helper for Exercise 12-12.2-5: the Hamilton relation `jk = i` in `ℍ[ℚ]ˣ`. -/
@[simp] theorem quaternionJUnit_mul_kUnit :
    quaternionJUnit * quaternionKUnit = quaternionIUnit := by
  -- Compare quaternion coordinates after expanding `j * (ij)`.
  ext <;> norm_num [quaternionKUnit, quaternionIUnit, quaternionJUnit, rationalQuaternionBasis,
    rational_quaternion_i_sq, rational_quaternion_j_sq, rational_quaternion_i_mul_j,
    rational_quaternion_j_mul_i]

/-- Helper for Exercise 12-12.2-5: the Hamilton relation `kj = -i` in `ℍ[ℚ]ˣ`. -/
@[simp] theorem quaternionKUnit_mul_jUnit :
    quaternionKUnit * quaternionJUnit = -quaternionIUnit := by
  -- Compare quaternion coordinates after expanding `(ij) * j`.
  ext <;> norm_num [quaternionKUnit, quaternionIUnit, quaternionJUnit, rationalQuaternionBasis,
    rational_quaternion_i_sq, rational_quaternion_j_sq, rational_quaternion_i_mul_j,
    rational_quaternion_j_mul_i]

/-- Helper for Exercise 12-12.2-5: the explicit table already satisfies the source relation
`(a 1)^2 = a 2`. -/
theorem quaternionGroupTwoUnitTable_a_one_sq :
    quaternionGroupTwoUnitTable (QuaternionGroup.a (1 : ZMod 4)) ^
        2 =
      quaternionGroupTwoUnitTable (QuaternionGroup.a (2 : ZMod 4)) := by
  -- Rewrite both sides to the quaternion units `i` and `-1`.
  rw [quaternionGroupTwoUnitTable_a_one, quaternionGroupTwoUnitTable_a_two, quaternionIUnit_sq]

/-- Helper for Exercise 12-12.2-5: the explicit table already satisfies the source relation
`(xa 0)^2 = a 2`. -/
theorem quaternionGroupTwoUnitTable_xa_zero_sq :
    quaternionGroupTwoUnitTable (QuaternionGroup.xa (0 : ZMod 4)) ^
        2 =
      quaternionGroupTwoUnitTable (QuaternionGroup.a (2 : ZMod 4)) := by
  -- Rewrite both sides to the quaternion units `j` and `-1`.
  rw [quaternionGroupTwoUnitTable_xa_zero, quaternionGroupTwoUnitTable_a_two, quaternionJUnit_sq]

/-- Helper for Exercise 12-12.2-5: the explicit table sends `xa 0 * a 1` to `xa 1`. -/
theorem quaternionGroupTwoUnitTable_xa_zero_mul_a_one :
    quaternionGroupTwoUnitTable (QuaternionGroup.xa (0 : ZMod 4)) *
        quaternionGroupTwoUnitTable (QuaternionGroup.a (1 : ZMod 4)) =
      quaternionGroupTwoUnitTable (QuaternionGroup.xa (1 : ZMod 4)) := by
  -- This is the source-level identity `j * i = -k = x a`.
  rw [quaternionGroupTwoUnitTable_xa_zero, quaternionGroupTwoUnitTable_a_one,
    quaternionGroupTwoUnitTable_xa_one]
  ext <;> norm_num [quaternionKUnit, quaternionIUnit, quaternionJUnit, rationalQuaternionBasis,
    rational_quaternion_i_mul_j, rational_quaternion_j_mul_i]

/-- Helper for Exercise 12-12.2-5: the explicit eight-value quaternion table is multiplicative,
so it packages the source-side embedding `Q8 → ℍ[ℚ]ˣ`. -/
def quaternionGroupTwoToQuaternionUnits : Q8 →* Units ℍ[ℚ] where
  toFun := quaternionGroupTwoUnitTable
  map_one' := by
    -- The source identity is `a 0`, and the table sends it to the unit `1`.
    change quaternionGroupTwoUnitTable (QuaternionGroup.a (0 : ZMod 4)) = 1
    simp [quaternionGroupTwoUnitTable]
  map_mul' := by
    rintro (i | i) (j | j)
    -- Route correction: package the already proved explicit table by a complete finite
    -- `Q8` multiplication check, instead of waiting for a generator-presentation API.
    · -- Check the `a * a` multiplication table on the four residues modulo `4`.
      fin_cases i <;> fin_cases j <;>
        apply Units.ext <;>
        ext <;>
        native_decide
    · -- Check the `a * xa` multiplication table on the four residues modulo `4`.
      fin_cases i <;> fin_cases j <;>
        apply Units.ext <;>
        ext <;>
        native_decide
    · -- Check the `xa * a` multiplication table on the four residues modulo `4`.
      fin_cases i <;> fin_cases j <;>
        apply Units.ext <;>
        ext <;>
        native_decide
    · -- Check the `xa * xa` multiplication table on the four residues modulo `4`.
      fin_cases i <;> fin_cases j <;>
        apply Units.ext <;>
        ext <;>
        native_decide

/-- Helper for Exercise 12-12.2-5: the explicit quaternion embedding of `Q8` gives a rational
representation on `ℍ[ℚ]` by left multiplication. -/
def quaternionGroupTwoHamiltonRepresentation :
    Representation ℚ Q8 ℍ[ℚ] where
  toFun := fun g ↦ LinearMap.mulLeft ℚ (quaternionGroupTwoToQuaternionUnits g : ℍ[ℚ])
  map_one' := by
    -- The identity element acts by multiplication with `1`, hence trivially.
    apply LinearMap.ext
    intro x
    simp
  map_mul' := by
    intro g h
    -- Composition of the action maps is just associativity of quaternion multiplication.
    apply LinearMap.ext
    intro x
    change ((quaternionGroupTwoToQuaternionUnits (g * h) : Units ℍ[ℚ]) : ℍ[ℚ]) * x =
      (((quaternionGroupTwoToQuaternionUnits g : Units ℍ[ℚ]) : ℍ[ℚ]) *
        (((quaternionGroupTwoToQuaternionUnits h : Units ℍ[ℚ]) : ℍ[ℚ]) * x))
    rw [map_mul]
    simp [mul_assoc]

/-- Helper for Exercise 12-12.2-5: evaluating the Hamilton model representation is literally left
multiplication by the corresponding quaternion unit. -/
@[simp] theorem quaternionGroupTwoHamiltonRepresentation_apply
    (g : Q8) (x : ℍ[ℚ]) :
    quaternionGroupTwoHamiltonRepresentation g x =
      ((quaternionGroupTwoToQuaternionUnits g : Units ℍ[ℚ]) : ℍ[ℚ]) * x := by
  -- This is definitional from the `LinearMap.mulLeft` model.
  rfl

/-- Helper for Exercise 12-12.2-5: the quaternion-valued quotient map from the rational group
algebra of `Q8` induced by the explicit embedding `Q8 → ℍ[ℚ]ˣ`. -/
def quaternionGroupTwoGroupAlgebraToQuaternion : ℚ[Q8] →ₐ[ℚ] ℍ[ℚ] :=
  MonoidAlgebra.lift ℚ ℍ[ℚ] Q8
    ((Units.coeHom ℍ[ℚ]).comp quaternionGroupTwoToQuaternionUnits)

/-- Helper for Exercise 12-12.2-5: on a basis element `single g r`, the quaternion quotient map
returns the expected scalar multiple of the quaternion unit attached to `g`. -/
theorem quaternionGroupTwoGroupAlgebraToQuaternion_single
    (g : Q8) (r : ℚ) :
    quaternionGroupTwoGroupAlgebraToQuaternion (Finsupp.single g r) =
      r • ((quaternionGroupTwoToQuaternionUnits g : Units ℍ[ℚ]) : ℍ[ℚ]) := by
  -- This is the defining computation rule for `MonoidAlgebra.lift`.
  simpa [quaternionGroupTwoGroupAlgebraToQuaternion] using
    (MonoidAlgebra.lift_single
      (((Units.coeHom ℍ[ℚ]).comp quaternionGroupTwoToQuaternionUnits)) g r)

/-- Helper for Exercise 12-12.2-5: the explicit quaternion quotient map `ℚ[Q8] → ℍ[ℚ]` is
surjective because the basis elements `1, i, j, k` already lie in its image. -/
theorem quaternionGroupTwoGroupAlgebraToQuaternion_surjective :
    Function.Surjective quaternionGroupTwoGroupAlgebraToQuaternion := by
  intro q
  let x0 : ℚ[Q8] := Finsupp.single 1 q.re
  let x1 : ℚ[Q8] := Finsupp.single (QuaternionGroup.a (1 : ZMod 4)) q.imI
  let x2 : ℚ[Q8] := Finsupp.single (QuaternionGroup.xa (0 : ZMod 4)) q.imJ
  let x3 : ℚ[Q8] := Finsupp.single (QuaternionGroup.xa (3 : ZMod 4)) q.imK
  have h_one : quaternionGroupTwoGroupAlgebraToQuaternion x0 = (q.re : ℍ[ℚ]) := by
    -- The group identity contributes the scalar basis vector `1`.
    rw [show x0 = Finsupp.single 1 q.re by rfl,
      quaternionGroupTwoGroupAlgebraToQuaternion_single, map_one]
    simp
  have h_i : quaternionGroupTwoGroupAlgebraToQuaternion x1 = q.imI • rationalQuaternionBasis.i := by
    -- The source element `a 1` maps to the quaternion basis vector `i`.
    rw [show x1 = Finsupp.single (QuaternionGroup.a (1 : ZMod 4)) q.imI by rfl,
      quaternionGroupTwoGroupAlgebraToQuaternion_single]
    simpa [quaternionGroupTwoToQuaternionUnits] using
      congrArg (fun u : Units ℍ[ℚ] ↦ q.imI • ((u : Units ℍ[ℚ]) : ℍ[ℚ]))
        quaternionGroupTwoUnitTable_a_one
  have h_j : quaternionGroupTwoGroupAlgebraToQuaternion x2 = q.imJ • rationalQuaternionBasis.j := by
    -- The source element `xa 0` maps to the quaternion basis vector `j`.
    rw [show x2 = Finsupp.single (QuaternionGroup.xa (0 : ZMod 4)) q.imJ by rfl,
      quaternionGroupTwoGroupAlgebraToQuaternion_single]
    simpa [quaternionGroupTwoToQuaternionUnits] using
      congrArg (fun u : Units ℍ[ℚ] ↦ q.imJ • ((u : Units ℍ[ℚ]) : ℍ[ℚ]))
        quaternionGroupTwoUnitTable_xa_zero
  have h_k : quaternionGroupTwoGroupAlgebraToQuaternion x3 = q.imK • rationalQuaternionBasis.k := by
    -- The source element `xa 3` maps to the quaternion basis vector `k`.
    rw [show x3 = Finsupp.single (QuaternionGroup.xa (3 : ZMod 4)) q.imK by rfl,
      quaternionGroupTwoGroupAlgebraToQuaternion_single]
    simpa [quaternionGroupTwoToQuaternionUnits, quaternionKUnit_val] using
      congrArg (fun u : Units ℍ[ℚ] ↦ q.imK • ((u : Units ℍ[ℚ]) : ℍ[ℚ]))
        quaternionGroupTwoUnitTable_xa_three
  refine ⟨x0 + x1 + x2 + x3, ?_⟩
  -- Summing the four source basis elements reconstructs the quaternion coordinates of `q`.
  calc
    quaternionGroupTwoGroupAlgebraToQuaternion (x0 + x1 + x2 + x3) =
        quaternionGroupTwoGroupAlgebraToQuaternion x0 +
          quaternionGroupTwoGroupAlgebraToQuaternion x1 +
          quaternionGroupTwoGroupAlgebraToQuaternion x2 +
          quaternionGroupTwoGroupAlgebraToQuaternion x3 := by
            simp [map_add, add_assoc]
    _ = (q.re : ℍ[ℚ]) + q.imI • rationalQuaternionBasis.i + q.imJ • rationalQuaternionBasis.j +
          q.imK • rationalQuaternionBasis.k := by
            rw [h_one, h_i, h_j, h_k]
    _ = q := by
          ext <;> simp [rationalQuaternionBasis]

/-- Helper for Exercise 12-12.2-5: the rational group algebra `ℚ[Q8]` has dimension `8`. -/
theorem quaternionGroupTwo_groupAlgebra_finrank_eight :
    Module.finrank ℚ ℚ[Q8] = 8 := by
  -- The group algebra is the finitely supported function space on the `8`-element group `Q8`.
  calc
    Module.finrank ℚ ℚ[Q8] = Fintype.card Q8 := by
      change Module.finrank ℚ (Q8 →₀ ℚ) = Fintype.card Q8
      exact Module.finrank_finsupp_self (R := ℚ) (ι := Q8)
    _ = 8 := by
      simpa using (QuaternionGroup.card (n := 2))

/-- Helper for Exercise 12-12.2-5: the proposed Artin-Wedderburn target has total rational
dimension `8`. -/
theorem quaternionGroupTwo_rational_target_finrank_eight :
    Module.finrank ℚ (ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) = 8 := by
  -- Add the four scalar dimensions to the quaternionic dimension `4`.
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, Module.finrank_prod]
  simp [Quaternion.finrank_eq_four]

/-- Helper for Exercise 12-12.2-5: in the coordinate basis `1, i, j, k`, left multiplication by
`q : ℍ[ℚ]` has trace `4 * q.re`. -/
theorem rational_quaternion_left_mul_trace_eq_four_mul_re
    (q : ℍ[ℚ]) :
    LinearMap.trace ℚ (ℍ[ℚ]) (LinearMap.mulLeft ℚ q) = 4 * q.re := by
  change
    LinearMap.trace ℚ (QuaternionAlgebra ℚ (-1) 0 (-1))
      (LinearMap.mulLeft ℚ q) = 4 * q.re
  let B : Module.Basis (Fin 4) ℚ (QuaternionAlgebra ℚ (-1) 0 (-1)) :=
    QuaternionAlgebra.basisOneIJK (-1 : ℚ) 0 (-1 : ℚ)
  have hB0 : (B 0 : ℍ[ℚ]) = 1 := by
    -- Compare coordinates in the standard quaternion basis to identify the first basis vector.
    apply B.equivFun.injective
    ext i
    fin_cases i <;> simp [B, QuaternionAlgebra.coe_basisOneIJK_repr]
  have hB1 : (B 1 : ℍ[ℚ]) = (QuaternionAlgebra.Basis.self ℚ).i := by
    -- The second basis vector is the Hamilton basis element `i`.
    apply B.equivFun.injective
    ext i
    fin_cases i <;> simp [B, QuaternionAlgebra.coe_basisOneIJK_repr]
  have hB2 : (B 2 : ℍ[ℚ]) = (QuaternionAlgebra.Basis.self ℚ).j := by
    -- The third basis vector is the Hamilton basis element `j`.
    apply B.equivFun.injective
    ext i
    fin_cases i <;> simp [B, QuaternionAlgebra.coe_basisOneIJK_repr]
  have hB3 : (B 3 : ℍ[ℚ]) = (QuaternionAlgebra.Basis.self ℚ).k := by
    -- The fourth basis vector is the Hamilton basis element `k`.
    apply B.equivFun.injective
    ext i
    fin_cases i <;> simp [B, QuaternionAlgebra.coe_basisOneIJK_repr]
  rw [LinearMap.trace_eq_matrix_trace ℚ B]
  rw [Matrix.trace, Fin.sum_univ_four, Matrix.diag]
  have h00 : (Algebra.leftMulMatrix B q) 0 0 = q.re := by
    -- Left multiplication sends the first basis vector `1` to `q`, whose first coordinate is
    -- precisely `q.re`.
    simp [Algebra.leftMulMatrix_eq_repr_mul, hB0, B]
  have h11 : (Algebra.leftMulMatrix B q) 1 1 = q.re := by
    -- Multiplying `i` by `q` still contributes `q.re` on the `i`-coordinate.
    simp [Algebra.leftMulMatrix_eq_repr_mul, hB1, B]
  have h22 : (Algebra.leftMulMatrix B q) 2 2 = q.re := by
    -- The same coordinate computation holds on the `j`-basis vector.
    simp [Algebra.leftMulMatrix_eq_repr_mul, hB2, B]
  have h33 : (Algebra.leftMulMatrix B q) 3 3 = q.re := by
    -- And likewise on the `k`-basis vector.
    simp [Algebra.leftMulMatrix_eq_repr_mul, hB3, B]
  calc
    (Algebra.leftMulMatrix B q) 0 0 + (Algebra.leftMulMatrix B q) 1 1 +
        (Algebra.leftMulMatrix B q) 2 2 + (Algebra.leftMulMatrix B q) 3 3 =
      q.re + q.re + q.re + q.re := by
        rw [h00, h11, h22, h33]
    _ = 4 * q.re := by
      ring

/-- Helper for Exercise 12-12.2-5: over `ℚ`, `-1` is not a sum of two squares. -/
theorem rat_neg_one_not_sum_two_squares :
    ¬ ∃ a b : ℚ, -(1 : ℚ) = a ^ 2 + b ^ 2 := by
  rintro ⟨a, b, hab⟩
  -- Route correction: use the ordered-field obstruction directly instead of a quaternionic detour.
  have hnonneg : 0 ≤ a ^ 2 + b ^ 2 := add_nonneg (sq_nonneg a) (sq_nonneg b)
  linarith

/-- Helper for Exercise 12-12.2-5: the Hamilton left-regular `Q8` representation has the expected
trace table `4, -4, 0` on `1`, `-1`, and the remaining six elements. -/
theorem quaternionGroupTwoHamilton_character_table (s : Q8) :
    quaternionGroupTwoHamiltonRepresentation.character s =
      if s = 1 then 4 else if s = QuaternionGroup.a (2 : ZMod 4) then -4 else 0 := by
  -- First rewrite the character as the trace of left multiplication by the corresponding
  -- quaternion unit.
  calc
    quaternionGroupTwoHamiltonRepresentation.character s =
        4 * (((quaternionGroupTwoToQuaternionUnits s : Units ℍ[ℚ]) : ℍ[ℚ]).re) := by
          simpa [Representation.character, quaternionGroupTwoHamiltonRepresentation_apply] using
            rational_quaternion_left_mul_trace_eq_four_mul_re
              (((quaternionGroupTwoToQuaternionUnits s : Units ℍ[ℚ]) : ℍ[ℚ]))
    _ = if s = 1 then 4 else if s = QuaternionGroup.a (2 : ZMod 4) then -4 else 0 := by
          -- The explicit eight-element quaternion table makes the real part computation finite.
          cases s with
          | a i =>
              fin_cases i <;> native_decide
          | xa i =>
              fin_cases i <;> native_decide

/-- Helper for Exercise 12-12.2-5: after extending scalars to `ℂ`, the Hamilton left-regular
representation realizes exactly `2 • ψ`. -/
theorem quaternionGroupTwo_leftRegularOnHamilton_character :
    (fun s ↦ algebraMap ℚ ℂ (quaternionGroupTwoHamiltonRepresentation.character s)) =
      (((2 : ℕ) : ℂ) • quaternionGroupTwoQuaternionCharacter) := by
  -- The trace table already isolates the only two nonzero classes, so two case splits suffice.
  ext s
  rw [quaternionGroupTwoHamilton_character_table]
  by_cases hs1 : s = 1
  · subst hs1
    have hχ : (((2 : ℕ) : ℂ) • quaternionGroupTwoQuaternionCharacter) (1 : Q8) = 4 := by
      change ((2 : ℂ) * quaternionGroupTwoQuaternionCharacter (QuaternionGroup.a (0 : ZMod 4))) =
        4
      norm_num [quaternionGroupTwoQuaternionCharacter]
    simpa using hχ.symm
  · by_cases hs2 : s = QuaternionGroup.a (2 : ZMod 4)
    · subst hs2
      have h20 : (2 : ZMod 4) ≠ 0 := by
        native_decide
      have hχ :
          (((2 : ℕ) : ℂ) • quaternionGroupTwoQuaternionCharacter)
            (QuaternionGroup.a (2 : ZMod 4)) = -4 := by
        change ((2 : ℂ) * quaternionGroupTwoQuaternionCharacter (QuaternionGroup.a (2 : ZMod 4))) =
          -4
        norm_num [quaternionGroupTwoQuaternionCharacter, h20]
      simpa [hs1, h20] using hχ.symm
    · have hχ : (((2 : ℕ) : ℂ) • quaternionGroupTwoQuaternionCharacter) s = 0 := by
          change ((2 : ℂ) * quaternionGroupTwoQuaternionCharacter s) = 0
          have hs_zero : quaternionGroupTwoQuaternionCharacter s = 0 := by
            -- Outside `1` and `-1 = a 2`, the defining character formula is identically zero.
            cases s with
            | a i =>
                by_cases h0 : i = 0
                · exfalso
                  exact hs1 (by simp [h0, QuaternionGroup.a_zero])
                · by_cases h2 : i = 2
                  · exfalso
                    exact hs2 (by simp [h2])
                  · simp [quaternionGroupTwoQuaternionCharacter, h0, h2]
            | xa i =>
                simp [quaternionGroupTwoQuaternionCharacter]
          simp [hs_zero]
      simpa [hs1, hs2] using hχ.symm

/-- Helper for Exercise 12-12.2-5: scalar extension transports a character by applying the
coefficient map. -/
theorem scalarExtension_character_eq_map_local
    {K : Type v} [Field K]
    {L : Type w} [Field L] [Algebra K L]
    {H : Type u} [Group H]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K H W) :
    (Representation.scalarExtension (k := L) τ).character =
      fun h ↦ algebraMap K L (τ.character h) := by
  -- Trace commutes with scalar extension, so the character values are mapped coefficientwise.
  ext h
  exact LinearMap.trace_baseChange (τ h) L

/-- Helper for Exercise 12-12.2-5: the quaternionic character is rational-valued, so its
character field is the bottom intermediate field `ℚ ⊆ ℂ`. -/
theorem quaternionGroupTwoQuaternionCharacter_characterField_eq_bot :
    characterField quaternionGroupTwoQuaternionCharacter =
      (⊥ : IntermediateField ℚ ℂ) := by
  -- Every value of the character already lies in the image of `ℚ → ℂ`.
  rw [show characterField quaternionGroupTwoQuaternionCharacter =
      IntermediateField.adjoin ℚ (Set.range quaternionGroupTwoQuaternionCharacter) by rfl]
  rw [IntermediateField.adjoin_eq_bot_iff]
  intro z hz
  rcases hz with ⟨s, rfl⟩
  rcases quaternionGroupTwoQuaternionCharacter_is_rational_valued s with ⟨q, hq⟩
  rw [← hq]
  simpa using IntermediateField.algebraMap_mem (⊥ : IntermediateField ℚ ℂ) q

/-- Helper for Exercise 12-12.2-5: scalar-extending the rational Hamilton model to the character
field realizes `2 • ψ`. -/
theorem quaternionGroupTwoQuaternionCharacter_two_realizableOver_characterField :
    ∃ (τ : Rep.{w} (characterField quaternionGroupTwoQuaternionCharacter) Q8)
      (_ : FiniteDimensional (characterField quaternionGroupTwoQuaternionCharacter) τ),
      (fun s ↦
        algebraMap (characterField quaternionGroupTwoQuaternionCharacter) ℂ
          ((τ.ρ.character) s)) =
        (((2 : ℕ) : ℂ) • quaternionGroupTwoQuaternionCharacter) := by
  -- Rewrite the character field as the bottom intermediate field generated by `ℚ`.
  rw [quaternionGroupTwoQuaternionCharacter_characterField_eq_bot]
  let τ₀ :
      Representation ↥(⊥ : IntermediateField ℚ ℂ) Q8
        (↥(⊥ : IntermediateField ℚ ℂ) ⊗[ℚ] ℍ[ℚ]) :=
    Representation.scalarExtension (k := ↥(⊥ : IntermediateField ℚ ℂ))
      quaternionGroupTwoHamiltonRepresentation
  let τ :=
    Rep.of
      (MonoidHom.comp
        ((LinearEquiv.conjRingEquiv
          (ULift.moduleEquiv.symm :
            (↥(⊥ : IntermediateField ℚ ℂ) ⊗[ℚ] ℍ[ℚ]) ≃ₗ[↥(⊥ : IntermediateField ℚ ℂ)]
              ULift.{w} (↥(⊥ : IntermediateField ℚ ℂ) ⊗[ℚ] ℍ[ℚ]))).toMonoidHom)
        τ₀)
  refine ⟨τ, inferInstance, ?_⟩
  ext s
  have htrace :
      τ.ρ.character s = τ₀.character s := by
    -- Conjugating the action by `ULift.moduleEquiv` does not change the trace.
    change
      LinearMap.trace ↥(⊥ : IntermediateField ℚ ℂ)
        (ULift.{w} (↥(⊥ : IntermediateField ℚ ℂ) ⊗[ℚ] ℍ[ℚ]))
        ((ULift.moduleEquiv.symm :
            (↥(⊥ : IntermediateField ℚ ℂ) ⊗[ℚ] ℍ[ℚ]) ≃ₗ[↥(⊥ : IntermediateField ℚ ℂ)]
              ULift.{w} (↥(⊥ : IntermediateField ℚ ℂ) ⊗[ℚ] ℍ[ℚ])).conj (τ₀ s)) =
      LinearMap.trace ↥(⊥ : IntermediateField ℚ ℂ)
        (↥(⊥ : IntermediateField ℚ ℂ) ⊗[ℚ] ℍ[ℚ]) (τ₀ s)
    exact LinearMap.trace_conj' (τ₀ s)
      (ULift.moduleEquiv.symm :
        (↥(⊥ : IntermediateField ℚ ℂ) ⊗[ℚ] ℍ[ℚ]) ≃ₗ[↥(⊥ : IntermediateField ℚ ℂ)]
          ULift.{w} (↥(⊥ : IntermediateField ℚ ℂ) ⊗[ℚ] ℍ[ℚ]))
  have hscalar :
      τ₀.character s =
        (IntermediateField.botEquiv ℚ ℂ).symm
          (quaternionGroupTwoHamiltonRepresentation.character s) := by
    simpa [τ₀] using
      congrFun
        (scalarExtension_character_eq_map_local
          (K := ℚ) (L := ↥(⊥ : IntermediateField ℚ ℂ))
          (τ := quaternionGroupTwoHamiltonRepresentation)) s
  calc
    algebraMap ↥(⊥ : IntermediateField ℚ ℂ) ℂ (τ.ρ.character s)
        = algebraMap ↥(⊥ : IntermediateField ℚ ℂ) ℂ (τ₀.character s) := by
            rw [htrace]
    _ =
        algebraMap ↥(⊥ : IntermediateField ℚ ℂ) ℂ
          ((IntermediateField.botEquiv ℚ ℂ).symm
            (quaternionGroupTwoHamiltonRepresentation.character s)) := by
          rw [hscalar]
    _ = algebraMap ℚ ℂ (quaternionGroupTwoHamiltonRepresentation.character s) := by
          simp [IntermediateField.botEquiv_symm]
    _ = (((2 : ℕ) : ℂ) • quaternionGroupTwoQuaternionCharacter) s := by
          simpa using congrFun quaternionGroupTwo_leftRegularOnHamilton_character s

/-- Helper for Exercise 12-12.2-5: a trace-zero `2 × 2` matrix squares to `-det(M)` times the
identity matrix. -/
theorem matrix_fin_two_sq_of_trace_zero
    {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R)
    (htr : M.trace = 0) :
    M * M = (-M.det) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  -- Expand the four entries and eliminate the second diagonal term with the trace-zero relation.
  ext i j
  fin_cases i <;> fin_cases j
  · have hdiag : M 1 1 = -M 0 0 := by
      exact eq_neg_of_add_eq_zero_right (by simpa [Matrix.trace_fin_two] using htr)
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, hdiag]
    ring
  · have hdiag : M 1 1 = -M 0 0 := by
      exact eq_neg_of_add_eq_zero_right (by simpa [Matrix.trace_fin_two] using htr)
    simp [Matrix.mul_apply, Fin.sum_univ_two, hdiag]
    ring
  · have hdiag : M 1 1 = -M 0 0 := by
      exact eq_neg_of_add_eq_zero_right (by simpa [Matrix.trace_fin_two] using htr)
    simp [Matrix.mul_apply, Fin.sum_univ_two, hdiag]
    ring
  · have hdiag : M 1 1 = -M 0 0 := by
      exact eq_neg_of_add_eq_zero_right (by simpa [Matrix.trace_fin_two] using htr)
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, hdiag]
    ring

/-- Helper for Exercise 12-12.2-5: in dimension `2`, a trace-zero endomorphism whose square has
trace `-2` must itself satisfy `f² = -1`. -/
theorem square_eq_neg_one_of_trace_zero_of_square_trace_neg_two
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hdim : Module.finrank K V = 2) (f : V →ₗ[K] V)
    (htr : LinearMap.trace K V f = 0)
    (hsqtr : LinearMap.trace K V (f * f) = (-2 : K)) :
    f * f = (-1 : K) • LinearMap.id := by
  -- Route correction: instead of diagonalizing the involution first, pass to any `2 × 2`
  -- matrix model and use the trace-zero square identity to force the scalar `-1`.
  set e : Module.Basis (Fin 2) K V :=
    (Module.finBasis K V).reindex (Fintype.equivFinOfCardEq (by simpa using hdim))
  let M : Matrix (Fin 2) (Fin 2) K := (LinearMap.toMatrix e e) f
  have hMtr : Matrix.trace M = 0 := by
    rw [show M = (LinearMap.toMatrix e e) f by rfl]
    rw [← LinearMap.trace_eq_matrix_trace K e f]
    exact htr
  have hMsq : M * M = (-M.det) • (1 : Matrix (Fin 2) (Fin 2) K) :=
    matrix_fin_two_sq_of_trace_zero M hMtr
  have hM2tr : Matrix.trace (M * M) = (-2 : K) := by
    -- Identify the trace of `M²` with the trace of `f²`.
    calc
      Matrix.trace (M * M) = Matrix.trace ((LinearMap.toMatrix e e) (f * f)) := by
        rw [show M = (LinearMap.toMatrix e e) f by rfl]
        simp [LinearMap.toMatrix_mul]
      _ = LinearMap.trace K V (f * f) := by
        symm
        simpa using LinearMap.trace_eq_matrix_trace K e (f * f)
      _ = (-2 : K) := hsqtr
  have hdet : M.det = 1 := by
    -- Taking traces of the square identity determines the determinant.
    rw [hMsq] at hM2tr
    have hminusTwo : (-((2 : K))) ≠ 0 := by
      exact neg_ne_zero.mpr (two_ne_zero : (2 : K) ≠ 0)
    have h' : (-((2 : K))) * M.det = (-((2 : K))) * 1 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hM2tr
    exact mul_left_cancel₀ hminusTwo h'
  apply (LinearMap.toMatrix e e).injective
  have hMsq' : M * M = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    simpa [hdet] using hMsq
  simpa [M, LinearMap.toMatrix_mul, LinearMap.toMatrix_id] using hMsq'

/-- Helper for Exercise 12-12.2-5: the expression obtained by anticommuting a quaternionic basis
vector has the expected swapped linear-combination form. -/
theorem neg_linear_combination_eq_swap
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (a b : K) (v w : V) :
    -(a • w + b • ((-(1 : K)) • v)) = b • v - a • w := by
  simp [sub_eq_add_neg]

/-- Helper for Exercise 12-12.2-5: in dimension `2`, two endomorphisms squaring to `-1` and
anticommuting force `-1` to be a sum of two squares in the base field. -/
theorem neg_one_sum_two_squares_of_anticommuting_square_neg_one
    {k : Type*} [Field k] [CharZero k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hdim : Module.finrank k V = 2)
    (A B : V →ₗ[k] V)
    (hA2 : A * A = (-1 : k) • LinearMap.id)
    (hB2 : B * B = (-1 : k) • LinearMap.id)
    (hBA : B * A = -(A * B)) :
    ∃ a b : k, -(1 : k) = a ^ 2 + b ^ 2 := by
  have hpos : 0 < Module.finrank k V := by
    simpa [hdim] using (show 0 < 2 by norm_num)
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hA2v : A (A v) = -(1 : k) • v := by
    -- Evaluate the square relation for `A` on the chosen nonzero vector.
    simpa using congrArg (fun f : V →ₗ[k] V ↦ f v) hA2
  by_cases hdep : ∃ a : k, A v = a • v
  · rcases hdep with ⟨a, ha⟩
    -- If `v` is an eigenvector for `A`, then `A² = -1` already gives the required square.
    have haSq : a ^ 2 = -(1 : k) := by
      apply smul_left_injective k hv
      simpa [ha, pow_two, smul_smul] using hA2v
    refine ⟨a, 0, ?_⟩
    simpa [pow_two, haSq]
  · have hlin : LinearIndependent k ![v, A v] := by
      -- Otherwise `v` and `A v` form a basis of the `2`-dimensional space.
      apply (LinearIndependent.pair_iff' hv).2
      intro a ha
      exact hdep ⟨a, ha.symm⟩
    let e : Module.Basis (Fin 2) k V :=
      basisOfLinearIndependentOfCardEqFinrank hlin (by simpa using hdim.symm)
    have he :
        ⇑e = ![v, A v] :=
      coe_basisOfLinearIndependentOfCardEqFinrank hlin (by simpa using hdim.symm)
    have he0 : e 0 = v := by
      simpa using congrFun he 0
    have he1 : e 1 = A v := by
      simpa using congrFun he 1
    let a : k := e.repr (B v) 0
    let b : k := e.repr (B v) 1
    have hBv : B v = a • v + b • A v := by
      -- Read the coordinates of `B v` in the basis `(v, A v)`.
      simpa [a, b, he, Fin.sum_univ_two] using (e.sum_repr (B v)).symm
    have hBAv : B (A v) = b • v - a • A v := by
      -- Anticommuting `B` past `A` swaps the two basis vectors with the expected signs.
      calc
        B (A v) = -(A (B v)) := by
          simpa using congrArg (fun f : V →ₗ[k] V ↦ f v) hBA
        _ = -(A (a • v + b • A v)) := by rw [hBv]
        _ = -(a • A v + b • ((-(1 : k)) • v)) := by
              rw [map_add, map_smul, map_smul, hA2v]
        _ = b • v - a • A v := neg_linear_combination_eq_swap a b v (A v)
    have hB2v : B (B v) = -(1 : k) • v := by
      -- Evaluate the square relation for `B` on the same vector.
      simpa using congrArg (fun f : V →ₗ[k] V ↦ f v) hB2
    have hcoord : a ^ 2 + b ^ 2 = -(1 : k) := by
      -- The first basis coordinate of `B² v` is exactly `a² + b²`.
      have hrepr_v0 : e.repr v 0 = 1 := by
        simpa [he0] using e.repr_self_apply (i := (0 : Fin 2)) (j := (0 : Fin 2))
      have hrepr_Av0 : e.repr (A v) 0 = 0 := by
        simpa [he1] using e.repr_self_apply (i := (1 : Fin 2)) (j := (0 : Fin 2))
      have hleft : e.repr (B (B v)) 0 = a ^ 2 + b ^ 2 := by
        rw [hBv, map_add, map_smul, map_smul, hBv, hBAv]
        simp [hrepr_v0, hrepr_Av0, a, b, pow_two]
      have hright : e.repr (B (B v)) 0 = -(1 : k) := by
        simpa [hrepr_v0] using congrArg (fun x : V ↦ e.repr x 0) hB2v
      rw [hleft] at hright
      exact hright
    exact ⟨a, b, hcoord.symm⟩

/-- Helper for Exercise 12-12.2-5: a rational realization of the quaternionic `Q8` character
forces `-1` to be a sum of two rational squares. -/
theorem quaternionGroupTwoQuaternionCharacter_realizable_over_rat_implies_neg_one_sum_two_squares
    (hreal :
      ∃ (τ : Rep.{w} ↥(⊥ : IntermediateField ℚ ℂ) Q8)
        (_ : FiniteDimensional ↥(⊥ : IntermediateField ℚ ℂ) τ),
        (fun s ↦ algebraMap ↥(⊥ : IntermediateField ℚ ℂ) ℂ ((τ.ρ.character) s)) =
          quaternionGroupTwoQuaternionCharacter) :
    ∃ a b : ℚ, -(1 : ℚ) = a ^ 2 + b ^ 2 := by
  rcases hreal with ⟨τ, hτfd, hτchar⟩
  let k := ↥(⊥ : IntermediateField ℚ ℂ)
  let A : τ →ₗ[k] τ := τ.ρ (QuaternionGroup.a (1 : ZMod 4))
  let B : τ →ₗ[k] τ := τ.ρ (QuaternionGroup.xa (0 : ZMod 4))
  have hchar_one : τ.ρ.character (1 : Q8) = (2 : k) := by
    -- The realizing character has degree `2`.
    apply Subtype.ext
    simpa [quaternionGroupTwoQuaternionCharacter] using congrFun hτchar (1 : Q8)
  have hdim : Module.finrank k τ = 2 := by
    -- The character value at the identity is the dimension of the representation.
    have hraw := congrFun hτchar (1 : Q8)
    change (((τ.ρ.character (1 : Q8)) : k) : ℂ) =
      quaternionGroupTwoQuaternionCharacter (1 : Q8) at hraw
    have hfinrank : (((Module.finrank k τ : ℕ) : k) : ℂ) = (2 : ℂ) := by
      simpa [Representation.char_one (ρ := τ.ρ), quaternionGroupTwoQuaternionCharacter] using hraw
    have hfinrank' : (Module.finrank k τ : k) = (2 : k) := by
      exact Subtype.ext hfinrank
    exact Nat.cast_injective hfinrank'
  have hchar_a_one : τ.ρ.character (QuaternionGroup.a (1 : ZMod 4)) = (0 : k) := by
    -- The quaternionic character vanishes away from `±1`.
    have h10 : (1 : ZMod 4) ≠ 0 := by decide
    have h12 : (1 : ZMod 4) ≠ 2 := by decide
    have h :
        (((τ.ρ.character (QuaternionGroup.a (1 : ZMod 4))) : k) : ℂ) = (0 : ℂ) := by
      have hraw := congrFun hτchar (QuaternionGroup.a (1 : ZMod 4))
      change (((τ.ρ.character (QuaternionGroup.a (1 : ZMod 4))) : k) : ℂ) =
        quaternionGroupTwoQuaternionCharacter (QuaternionGroup.a (1 : ZMod 4)) at hraw
      simpa [quaternionGroupTwoQuaternionCharacter, h10, h12] using hraw
    exact Subtype.ext h
  have hchar_xa_zero : τ.ρ.character (QuaternionGroup.xa (0 : ZMod 4)) = (0 : k) := by
    -- The same vanishing holds for the `j`-generator.
    have h :
        (((τ.ρ.character (QuaternionGroup.xa (0 : ZMod 4))) : k) : ℂ) = (0 : ℂ) := by
      have hraw := congrFun hτchar (QuaternionGroup.xa (0 : ZMod 4))
      change (((τ.ρ.character (QuaternionGroup.xa (0 : ZMod 4))) : k) : ℂ) =
        quaternionGroupTwoQuaternionCharacter (QuaternionGroup.xa (0 : ZMod 4)) at hraw
      simpa [quaternionGroupTwoQuaternionCharacter] using hraw
    exact Subtype.ext h
  have hchar_a_two : τ.ρ.character (QuaternionGroup.a (2 : ZMod 4)) = (-2 : k) := by
    -- The central involution has character value `-2`.
    have h20 : (2 : ZMod 4) ≠ 0 := by decide
    have h :
        (((τ.ρ.character (QuaternionGroup.a (2 : ZMod 4))) : k) : ℂ) = (-2 : ℂ) := by
      have hraw := congrFun hτchar (QuaternionGroup.a (2 : ZMod 4))
      change (((τ.ρ.character (QuaternionGroup.a (2 : ZMod 4))) : k) : ℂ) =
        quaternionGroupTwoQuaternionCharacter (QuaternionGroup.a (2 : ZMod 4)) at hraw
      simpa [quaternionGroupTwoQuaternionCharacter, h20] using hraw
    exact Subtype.ext h
  have ha_sq :
      (QuaternionGroup.a (1 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4) =
        QuaternionGroup.a (2 : ZMod 4) := by
    native_decide
  have hxa_sq :
      (QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.xa (0 : ZMod 4) =
        QuaternionGroup.a (2 : ZMod 4) := by
    native_decide
  have hanticomm_group :
      (QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4) =
        QuaternionGroup.a (2 : ZMod 4) *
          (QuaternionGroup.a (1 : ZMod 4) * QuaternionGroup.xa (0 : ZMod 4)) := by
    native_decide
  have hA_sq_trace : LinearMap.trace k τ (A * A) = (-2 : k) := by
    -- Squaring `a 1` gives the central involution `a 2`.
    calc
      LinearMap.trace k τ (A * A) =
          τ.ρ.character
            ((QuaternionGroup.a (1 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4)) := by
              change LinearMap.trace k τ (τ.ρ (QuaternionGroup.a (1 : ZMod 4)) *
                τ.ρ (QuaternionGroup.a (1 : ZMod 4))) =
                LinearMap.trace k τ (τ.ρ
                  ((QuaternionGroup.a (1 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4)))
              rw [(τ.ρ.map_mul _ _).symm]
      _ = τ.ρ.character (QuaternionGroup.a (2 : ZMod 4)) := by rw [ha_sq]
      _ = (-2 : k) := hchar_a_two
  have hB_sq_trace : LinearMap.trace k τ (B * B) = (-2 : k) := by
    -- Squaring `xa 0` gives the same central involution.
    calc
      LinearMap.trace k τ (B * B) =
          τ.ρ.character
            ((QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.xa (0 : ZMod 4)) := by
              change LinearMap.trace k τ (τ.ρ (QuaternionGroup.xa (0 : ZMod 4)) *
                τ.ρ (QuaternionGroup.xa (0 : ZMod 4))) =
                LinearMap.trace k τ (τ.ρ
                  ((QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.xa (0 : ZMod 4)))
              rw [(τ.ρ.map_mul _ _).symm]
      _ = τ.ρ.character (QuaternionGroup.a (2 : ZMod 4)) := by rw [hxa_sq]
      _ = (-2 : k) := hchar_a_two
  have hA2 : A * A = (-1 : k) • LinearMap.id := by
    -- The trace-zero square lemma upgrades the character data to the exact relation `A² = -1`.
    exact square_eq_neg_one_of_trace_zero_of_square_trace_neg_two
      (K := k) (V := τ) hdim A hchar_a_one hA_sq_trace
  have hB2 : B * B = (-1 : k) • LinearMap.id := by
    -- The same argument applies to `B = τ(xa 0)`.
    exact square_eq_neg_one_of_trace_zero_of_square_trace_neg_two
      (K := k) (V := τ) hdim B hchar_xa_zero hB_sq_trace
  have hcentral : τ.ρ (QuaternionGroup.a (2 : ZMod 4)) = (-1 : k) • LinearMap.id := by
    -- The central involution acts by `-1` because it is the square of `a 1`.
    calc
      τ.ρ (QuaternionGroup.a (2 : ZMod 4)) =
          τ.ρ ((QuaternionGroup.a (1 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4)) := by
            rw [ha_sq]
      _ = A * A := by
            simpa [A] using (τ.ρ.map_mul (QuaternionGroup.a (1 : ZMod 4))
              (QuaternionGroup.a (1 : ZMod 4)))
      _ = (-1 : k) • LinearMap.id := hA2
  have hBA : B * A = -(A * B) := by
    -- Route correction: use the `Q8` multiplication relation `ji = (-1) (ij)` and identify
    -- the central involution with `-1` through `A² = -1`.
    calc
      B * A =
          τ.ρ
            ((QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4)) := by
              simpa [A, B] using (τ.ρ.map_mul (QuaternionGroup.xa (0 : ZMod 4))
                (QuaternionGroup.a (1 : ZMod 4))).symm
      _ =
          τ.ρ
            (QuaternionGroup.a (2 : ZMod 4) *
              (QuaternionGroup.a (1 : ZMod 4) * QuaternionGroup.xa (0 : ZMod 4))) := by
                rw [hanticomm_group]
      _ = τ.ρ (QuaternionGroup.a (2 : ZMod 4)) * (A * B) := by
            rw [τ.ρ.map_mul, τ.ρ.map_mul]
      _ = ((-1 : k) • LinearMap.id) * (A * B) := by rw [hcentral]
      _ = (-1 : k) • (A * B) := by
            ext x
            rfl
      _ = -(A * B) := by simp
  rcases neg_one_sum_two_squares_of_anticommuting_square_neg_one
      (hdim := hdim) (A := A) (B := B) hA2 hB2 hBA with ⟨a, b, hab⟩
  refine ⟨(IntermediateField.botEquiv ℚ ℂ a),
    (IntermediateField.botEquiv ℚ ℂ b), ?_⟩
  -- Transport the square identity from the bottom intermediate field back to `ℚ`.
  simpa using congrArg (IntermediateField.botEquiv ℚ ℂ) hab


end

end Representation
