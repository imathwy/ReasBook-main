import Mathlib
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_12_12_2_5 (from Chap12) -/
noncomputable section

open scoped MonoidAlgebra Quaternion TensorProduct

universe u v w

namespace Representation

open CategoryTheory

section

local notation "Q8" => QuaternionGroup 2

-- Proof sketch: use the four linear characters of `Q8` together with the quotient map from
-- `ℚ[Q8]` to the rational quaternion division algebra `ℍ[ℚ]`, then apply Artin-Wedderburn to
-- identify the remaining simple factor.
/-- Exercise 12-12.2-5 (1): the rational group algebra of `Q8 = QuaternionGroup 2` decomposes as
four copies of `ℚ` together with the rational quaternion division algebra `ℍ[ℚ]`. -/
theorem quaternionGroupTwo_rational_group_algebra_decomposition :
    Nonempty (ℚ[Q8] ≃ₐ[ℚ] ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) :=
  by
    let Φ := quaternion_group_two_rational_comparison_algHom
    have hsurj : Function.Surjective Φ := quaternion_group_two_rational_comparison_surjective
    have hdim :
        Module.finrank ℚ ℚ[Q8] = Module.finrank ℚ (ℚ × ℚ × ℚ × ℚ × ℍ[ℚ]) := by
      rw [quaternionGroupTwo_groupAlgebra_finrank_eight,
        quaternionGroupTwo_rational_target_finrank_eight]
    have hinjLinear : Function.Injective Φ.toLinearMap := by
      -- Equal finite dimension upgrades surjectivity of the comparison map to injectivity.
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := Φ.toLinearMap) hdim).2 hsurj
    have hinj : Function.Injective Φ := hinjLinear
    exact ⟨AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩

-- Proof sketch: identify `quaternionGroupTwoQuaternionCharacter` with the irreducible complex
-- character coming from the quaternionic simple factor in the Artin-Wedderburn decomposition, and
-- verify that `2` is the minimal scaling factor making it realizable over `ℚ`.
/-- Exercise 12-12.2-5 (2): the character corresponding to the quaternionic simple component has
Schur index `2`. -/
theorem quaternionGroupTwoQuaternionCharacter_hasSchurIndexTwo :
    HasSchurIndex quaternionGroupTwoQuaternionCharacter 2 := by
  -- Route correction: the realizability half is already closed by the Hamilton model, so the
  -- remaining work is to rule out a genuine `m = 1` realization over the character field `ℚ`.
  rw [hasSchurIndex_iff (χ := quaternionGroupTwoQuaternionCharacter) (m := 2)]
  refine ⟨quaternionGroupTwoQuaternionCharacter_two_realizableOver_characterField, ?_⟩
  intro n hn
  have hpos : 1 ≤ (n : ℕ) := Nat.succ_le_of_lt n.2
  have hone_or_two : (n : ℕ) = 1 ∨ 2 ≤ (n : ℕ) := by
    omega
  rcases hone_or_two with hn_one | hn_two
  · -- For `n = 1`, the realizing model is already rational and forces a forbidden sum of two
    -- rational squares.
    rw [quaternionGroupTwoQuaternionCharacter_characterField_eq_bot] at hn
    rcases quaternionGroupTwoQuaternionCharacter_realizable_over_rat_implies_neg_one_sum_two_squares
      (by
        rcases hn with ⟨τ, hτfd, hτchar⟩
        refine ⟨τ, hτfd, ?_⟩
        simpa [hn_one] using hτchar) with ⟨a, b, hab⟩
    exfalso
    exact rat_neg_one_not_sum_two_squares ⟨a, b, hab⟩
  · exact hn_two

-- Proof sketch: inspect the explicit values of the character on the two central elements
-- `1, -1` and on the six remaining elements of `Q8`.
/-- Exercise 12-12.2-5 (3): the corresponding character takes the value `2` at `1`, the value
`-2` at the central involution `-1 = a 2`, and vanishes on every other element of `Q8`. -/
theorem quaternionGroupTwoQuaternionCharacter_apply (s : Q8) :
    quaternionGroupTwoQuaternionCharacter s =
      if s = 1 then 2 else if s = QuaternionGroup.a (2 : ZMod 4) then -2 else 0 := by
  -- Split over the explicit normal forms in `QuaternionGroup 2`.
  cases s with
  | a i =>
      -- On the `a i` branch the character only distinguishes `i = 0` and `i = 2`.
      by_cases h0 : i = 0
      · subst h0
        simp [quaternionGroupTwoQuaternionCharacter]
      · by_cases h2 : i = 2
        · subst h2
          have h_ne_one : (QuaternionGroup.a (2 : ZMod 4) : Q8) ≠ 1 := by
            intro h
            rw [← QuaternionGroup.a_zero] at h
            injection h with h'
            exact h0 h'
          calc
            quaternionGroupTwoQuaternionCharacter (QuaternionGroup.a (2 : ZMod 4)) = -2 := by
              simp [quaternionGroupTwoQuaternionCharacter, h0]
            _ = if (QuaternionGroup.a (2 : ZMod 4) : Q8) = 1 then 2
                  else if (QuaternionGroup.a (2 : ZMod 4) : Q8) =
                      QuaternionGroup.a (2 : ZMod 4) then -2 else 0 := by
                simp [h_ne_one]
        · have h_ne_one : QuaternionGroup.a i ≠ (1 : Q8) := by
            intro h
            rw [← QuaternionGroup.a_zero] at h
            injection h with h'
            exact h0 h'
          calc
            quaternionGroupTwoQuaternionCharacter (QuaternionGroup.a i) = 0 := by
              simp [quaternionGroupTwoQuaternionCharacter, h0, h2]
            _ = if (QuaternionGroup.a i : Q8) = 1 then 2
                  else if (QuaternionGroup.a i : Q8) = QuaternionGroup.a (2 : ZMod 4)
                    then -2 else 0 := by
                simp [h_ne_one, h2]
  | xa i =>
      -- On the `xa i` branch the character vanishes and these elements are never `1` or `a 2`.
      have h_ne_one : QuaternionGroup.xa i ≠ (1 : Q8) := by
        intro h
        rw [← QuaternionGroup.a_zero] at h
        cases h
      calc
        quaternionGroupTwoQuaternionCharacter (QuaternionGroup.xa i) = 0 := by
          simp [quaternionGroupTwoQuaternionCharacter]
        _ = if (QuaternionGroup.xa i : Q8) = 1 then 2
              else if (QuaternionGroup.xa i : Q8) = QuaternionGroup.a (2 : ZMod 4) then -2 else 0 := by
            simp [h_ne_one]

section

variable (K : Type) [Field K] [Algebra ℚ K]

/-- Helper for Exercise 12-12.2-5: a one-dimensional `K`-representation attached to a scalar-valued
group homomorphism. -/
def scalarMonoidRepresentation {H : Type*} [Group H] (β : H →* K) :
    Representation K H K where
  toFun h := LinearMap.lsmul K K (β h)
  map_one' := by
    -- The identity acts by scalar multiplication with `1`.
    ext x
    simp [LinearMap.lsmul_apply]
  map_mul' x y := by
    -- Composition of scalar-multiplication maps multiplies the underlying scalars.
    ext z
    simp [LinearMap.lsmul_apply, mul_assoc]

/-- Helper for Exercise 12-12.2-5: the character of a scalar one-dimensional representation is the
underlying scalar-valued homomorphism. -/
theorem scalarMonoidRepresentation_character_apply
    {H : Type*} [Group H] (β : H →* K) (h : H) :
    (scalarMonoidRepresentation (K := K) β).character h = β h := by
  -- Expand the trace in the unique basis of `K` over itself.
  rw [Representation.character]
  let b := Module.Free.chooseBasis K K
  rw [LinearMap.trace_eq_matrix_trace K b]
  have hmat :
      LinearMap.toMatrix b b ((scalarMonoidRepresentation (K := K) β) h) =
        Matrix.diagonal fun _ ↦ β h := by
    convert (Algebra.toMatrix_lsmul (b := b) (β h)) using 1
  rw [hmat]
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex K K) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex K K, Module.finrank_self]
  simp [Matrix.trace, hcard]

omit [Algebra ℚ K] in
/-- Helper for Exercise 12-12.2-5: a `1`-dimensional representation over any field is
irreducible. -/
theorem representation_isIrreducible_of_finrank_eq_one
    {H : Type*} [Group H] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K H V) (hV : Module.finrank K V = 1) :
    ρ.IsIrreducible := by
  letI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  letI : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  letI : IsSimpleOrder (Submodule K V) :=
    (isSimpleModule_iff K V).1 ((isSimpleModule_iff_finrank_eq_one).2 hV)
  refine IsSimpleOrder.of_forall_eq_top fun σ hσ ↦ ?_
  have hσtop : σ.toSubmodule = ⊤ := by
    rcases eq_bot_or_eq_top σ.toSubmodule with hσbot | hσtop
    · exact False.elim <| hσ <| Subrepresentation.toSubmodule_injective (by simpa using hσbot)
    · exact hσtop
  exact Subrepresentation.toSubmodule_injective (by simpa using hσtop)

/-- Helper for Exercise 12-12.2-5: the four rational linear characters of `Q8`, viewed over `K`
through the coefficient map `ℚ → K`. -/
def quaternionGroupTwoLinearCharacterOver (n : Fin 4) : Q8 →* K :=
  (algebraMap ℚ K).toMonoidHom.comp (quaternion_group_two_rational_linear_character_family n)

/-- Helper for Exercise 12-12.2-5: the `n`-th linear `K`-representation of `Q8`. -/
def quaternionGroupTwoLinearRepresentation (n : Fin 4) : FDRep K Q8 :=
  FDRep.of (scalarMonoidRepresentation (K := K) (quaternionGroupTwoLinearCharacterOver (K := K) n))

/-- Helper for Exercise 12-12.2-5: the character of the `n`-th linear slot is the coefficientwise
image of the rational sign character. -/
theorem quaternionGroupTwoLinearRepresentation_character_apply
    (n : Fin 4) (g : Q8) :
    (quaternionGroupTwoLinearRepresentation (K := K) n).character g =
      algebraMap ℚ K (quaternion_group_two_rational_linear_character_family n g) := by
  -- The scalar one-dimensional model records the sign character verbatim.
  simpa [quaternionGroupTwoLinearRepresentation, quaternionGroupTwoLinearCharacterOver] using
    scalarMonoidRepresentation_character_apply
      (K := K) (β := quaternionGroupTwoLinearCharacterOver (K := K) n) g

/-- Helper for Exercise 12-12.2-5: each linear slot of `Q8` is simple over `K`. -/
theorem quaternionGroupTwoLinearRepresentation_simple (n : Fin 4) :
    CategoryTheory.Simple (quaternionGroupTwoLinearRepresentation (K := K) n) := by
  have hfinrank :
      Module.finrank K (quaternionGroupTwoLinearRepresentation (K := K) n) = 1 := by
    -- The underlying carrier of the linear slot is just `K` itself.
    change Module.finrank K K = 1
    simp
  have hirr :
      Representation.IsIrreducible
        (quaternionGroupTwoLinearRepresentation (K := K) n).ρ := by
    -- The carrier is the one-dimensional vector space `K`.
    exact representation_isIrreducible_of_finrank_eq_one
      (K := K) (ρ := (quaternionGroupTwoLinearRepresentation (K := K) n).ρ)
      hfinrank
  letI :
      Representation.IsIrreducible
        (quaternionGroupTwoLinearRepresentation (K := K) n).ρ := hirr
  exact FDRep.simple_of_isIrreducible (quaternionGroupTwoLinearRepresentation (K := K) n)

omit [Algebra ℚ K] in
/-- Helper for Exercise 12-12.2-5: in the algebraic closure of any base field, `-1` is a sum of
two squares. -/
theorem neg_one_sum_two_squares_in_algebraicClosure :
    ∃ a b : AlgebraicClosure K, -(1 : AlgebraicClosure K) = a ^ 2 + b ^ 2 := by
  -- A square root of `-1` exists in every algebraically closed field.
  obtain ⟨b, hb⟩ :=
    IsAlgClosed.exists_pow_nat_eq (k := AlgebraicClosure K) (-(1 : AlgebraicClosure K))
      (by decide : 0 < 2)
  refine ⟨0, b, ?_⟩
  -- Choosing `a = 0` turns the witness `b² = -1` into the required sum-of-squares identity.
  simp [pow_two, hb]

/-- Helper for Exercise 12-12.2-5: the explicit split quaternion model transports the source
embedding `Q8 → ℍ[ℚ]ˣ` into `GL₂(K)` once `-1 = a² + b²`. -/
def quaternionGroupTwoToSplitMatrixUnits
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    Q8 →* Units (Matrix (Fin 2) (Fin 2) K) where
  toFun g :=
    Units.map (quaternion_split_algHom (K := K) a b h).toMonoidHom <|
      Units.map (rationalQuaternionToScalarExtension (K := K)).toMonoidHom
        (quaternionGroupTwoToQuaternionUnits g)
  map_one' := by
    -- Both unit transports preserve the source identity.
    simp
  map_mul' g g' := by
    -- Multiplicativity is inherited from the two successive unit maps.
    simp

/-- Helper for Exercise 12-12.2-5: in the split model, the generator `a 1` acts by the standard
quaternionic matrix `I`. -/
theorem quaternionGroupTwoToSplitMatrixUnits_a_one
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    ((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
        (QuaternionGroup.a (1 : ZMod 4)) :
          Units (Matrix (Fin 2) (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K) =
      quaternion_split_matrix_i (K := K) := by
  -- Rewrite the composed unit map through the source-side `i`-generator.
  change
    quaternion_split_algHom (K := K) a b h
      (rationalQuaternionToScalarExtension (K := K)
        ((quaternionGroupTwoToQuaternionUnits (QuaternionGroup.a (1 : ZMod 4)) :
          Units ℍ[ℚ]) : ℍ[ℚ])) =
      quaternion_split_matrix_i (K := K)
  rw [show ((quaternionGroupTwoToQuaternionUnits (QuaternionGroup.a (1 : ZMod 4)) :
      Units ℍ[ℚ]) : ℍ[ℚ]) = (QuaternionAlgebra.Basis.self ℚ).i by
        simpa [quaternionGroupTwoToQuaternionUnits] using
          congrArg (fun u : Units ℍ[ℚ] ↦ ((u : Units ℍ[ℚ]) : ℍ[ℚ]))
            quaternionGroupTwoUnitTable_a_one]
  rw [rationalQuaternionToScalarExtension_i, quaternion_split_algHom_basis_i]

/-- Helper for Exercise 12-12.2-5: in the split model, the central involution `a 2 = -1` acts by
the scalar matrix `-1`. -/
theorem quaternionGroupTwoToSplitMatrixUnits_a_two
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    ((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
        (QuaternionGroup.a (2 : ZMod 4)) :
          Units (Matrix (Fin 2) (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K) =
      (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  -- The source element `a 2` is the unit `-1`, so every algebra map sends it to `-1`.
  change
    quaternion_split_algHom (K := K) a b h
      (rationalQuaternionToScalarExtension (K := K)
        ((quaternionGroupTwoToQuaternionUnits (QuaternionGroup.a (2 : ZMod 4)) :
          Units ℍ[ℚ]) : ℍ[ℚ])) =
      (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K)
  rw [show ((quaternionGroupTwoToQuaternionUnits (QuaternionGroup.a (2 : ZMod 4)) :
      Units ℍ[ℚ]) : ℍ[ℚ]) = (-1 : ℍ[ℚ]) by
        simpa [quaternionGroupTwoToQuaternionUnits] using
          congrArg (fun u : Units ℍ[ℚ] ↦ ((u : Units ℍ[ℚ]) : ℍ[ℚ]))
            quaternionGroupTwoUnitTable_a_two]
  calc
    quaternion_split_algHom (K := K) a b h
        (rationalQuaternionToScalarExtension (K := K) (-1 : ℍ[ℚ])) =
      quaternion_split_algHom (K := K) a b h (-(1 : ℍ[K])) := by
        rw [map_neg, rationalQuaternionToScalarExtension_one]
    _ = (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        simp

/-- Helper for Exercise 12-12.2-5: in the split model, the generator `xa 0` acts by the witness
matrix `J(a,b)`. -/
theorem quaternionGroupTwoToSplitMatrixUnits_xa_zero
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    ((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
        (QuaternionGroup.xa (0 : ZMod 4)) :
          Units (Matrix (Fin 2) (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K) =
      quaternion_split_matrix_j (K := K) a b := by
  -- Rewrite the composed unit map through the source-side `j`-generator.
  change
    quaternion_split_algHom (K := K) a b h
      (rationalQuaternionToScalarExtension (K := K)
        ((quaternionGroupTwoToQuaternionUnits (QuaternionGroup.xa (0 : ZMod 4)) :
          Units ℍ[ℚ]) : ℍ[ℚ])) =
      quaternion_split_matrix_j (K := K) a b
  rw [show ((quaternionGroupTwoToQuaternionUnits (QuaternionGroup.xa (0 : ZMod 4)) :
      Units ℍ[ℚ]) : ℍ[ℚ]) = (QuaternionAlgebra.Basis.self ℚ).j by
        simpa [quaternionGroupTwoToQuaternionUnits] using
          congrArg (fun u : Units ℍ[ℚ] ↦ ((u : Units ℍ[ℚ]) : ℍ[ℚ]))
            quaternionGroupTwoUnitTable_xa_zero]
  rw [rationalQuaternionToScalarExtension_j, quaternion_split_algHom_basis_j]

/-- Helper for Exercise 12-12.2-5: in the split model, the element `xa 3 = k` acts by the matrix
`K(a,b)`. -/
theorem quaternionGroupTwoToSplitMatrixUnits_xa_three
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    ((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
        (QuaternionGroup.xa (3 : ZMod 4)) :
          Units (Matrix (Fin 2) (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K) =
      quaternion_split_matrix_k (K := K) a b := by
  -- Rewrite the composed unit map through the source-side `k`-generator.
  change
    quaternion_split_algHom (K := K) a b h
      (rationalQuaternionToScalarExtension (K := K)
        ((quaternionGroupTwoToQuaternionUnits (QuaternionGroup.xa (3 : ZMod 4)) :
          Units ℍ[ℚ]) : ℍ[ℚ])) =
      quaternion_split_matrix_k (K := K) a b
  rw [show ((quaternionGroupTwoToQuaternionUnits (QuaternionGroup.xa (3 : ZMod 4)) :
      Units ℍ[ℚ]) : ℍ[ℚ]) = (QuaternionAlgebra.Basis.self ℚ).k by
        simpa [quaternionGroupTwoToQuaternionUnits, quaternionKUnit_val] using
          congrArg (fun u : Units ℍ[ℚ] ↦ ((u : Units ℍ[ℚ]) : ℍ[ℚ]))
            quaternionGroupTwoUnitTable_xa_three]
  rw [rationalQuaternionToScalarExtension_k, quaternion_split_algHom_basis_k]

/-- Helper for Exercise 12-12.2-5: in the split model, the element `a 3 = -i` acts by `-I`. -/
theorem quaternionGroupTwoToSplitMatrixUnits_a_three
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    ((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
        (QuaternionGroup.a (3 : ZMod 4)) :
          Units (Matrix (Fin 2) (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K) =
      -quaternion_split_matrix_i (K := K) := by
  -- Route correction: use the source relation `a 3 = (-1) * a 1`, so the split matrix is
  -- `(-1) · I`.
  have hmul :
      (QuaternionGroup.a (3 : ZMod 4) : Q8) =
        QuaternionGroup.a (2 : ZMod 4) * QuaternionGroup.a (1 : ZMod 4) := by
    native_decide
  have hmul_matrix :
      (((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
          (QuaternionGroup.a (3 : ZMod 4)) :
            Units (Matrix (Fin 2) (Fin 2) K)) :
          Matrix (Fin 2) (Fin 2) K)) =
        ((((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
            (QuaternionGroup.a (2 : ZMod 4)) :
              Units (Matrix (Fin 2) (Fin 2) K)) :
            Matrix (Fin 2) (Fin 2) K)) *
          (((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
            (QuaternionGroup.a (1 : ZMod 4)) :
              Units (Matrix (Fin 2) (Fin 2) K)) :
            Matrix (Fin 2) (Fin 2) K))) := by
    rw [hmul]
    exact congrArg
      (fun u : Units (Matrix (Fin 2) (Fin 2) K) ↦ (u : Matrix (Fin 2) (Fin 2) K))
      ((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h).map_mul
        (QuaternionGroup.a (2 : ZMod 4)) (QuaternionGroup.a (1 : ZMod 4)))
  calc
    (((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
        (QuaternionGroup.a (3 : ZMod 4)) :
          Units (Matrix (Fin 2) (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K)) =
        ((((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
          (QuaternionGroup.a (2 : ZMod 4)) :
            Units (Matrix (Fin 2) (Fin 2) K)) :
          Matrix (Fin 2) (Fin 2) K)) *
        (((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
          (QuaternionGroup.a (1 : ZMod 4)) :
            Units (Matrix (Fin 2) (Fin 2) K)) :
          Matrix (Fin 2) (Fin 2) K))) := hmul_matrix
    _ = ((-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K)) * quaternion_split_matrix_i (K := K) := by
          rw [quaternionGroupTwoToSplitMatrixUnits_a_two (K := K) a b h,
            quaternionGroupTwoToSplitMatrixUnits_a_one (K := K) a b h]
    _ = -quaternion_split_matrix_i (K := K) := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [quaternion_split_matrix_i]

/-- Helper for Exercise 12-12.2-5: in the split model, the element `xa 1 = -k` acts by `-K`. -/
theorem quaternionGroupTwoToSplitMatrixUnits_xa_one
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    ((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
        (QuaternionGroup.xa (1 : ZMod 4)) :
          Units (Matrix (Fin 2) (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K) =
      -quaternion_split_matrix_k (K := K) a b := by
  -- Route correction: use the source relation `xa 1 = (-1) * xa 3`, so the split matrix is
  -- `(-1) · K(a,b)`.
  have hmul :
      (QuaternionGroup.xa (1 : ZMod 4) : Q8) =
        QuaternionGroup.a (2 : ZMod 4) * QuaternionGroup.xa (3 : ZMod 4) := by
    native_decide
  have hmul_matrix :
      (((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
          (QuaternionGroup.xa (1 : ZMod 4)) :
            Units (Matrix (Fin 2) (Fin 2) K)) :
          Matrix (Fin 2) (Fin 2) K)) =
        ((((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
            (QuaternionGroup.a (2 : ZMod 4)) :
              Units (Matrix (Fin 2) (Fin 2) K)) :
            Matrix (Fin 2) (Fin 2) K)) *
          (((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
            (QuaternionGroup.xa (3 : ZMod 4)) :
              Units (Matrix (Fin 2) (Fin 2) K)) :
            Matrix (Fin 2) (Fin 2) K))) := by
    rw [hmul]
    exact congrArg
      (fun u : Units (Matrix (Fin 2) (Fin 2) K) ↦ (u : Matrix (Fin 2) (Fin 2) K))
      ((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h).map_mul
        (QuaternionGroup.a (2 : ZMod 4)) (QuaternionGroup.xa (3 : ZMod 4)))
  calc
    (((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
        (QuaternionGroup.xa (1 : ZMod 4)) :
          Units (Matrix (Fin 2) (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K)) =
        ((((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
          (QuaternionGroup.a (2 : ZMod 4)) :
            Units (Matrix (Fin 2) (Fin 2) K)) :
          Matrix (Fin 2) (Fin 2) K)) *
        (((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
          (QuaternionGroup.xa (3 : ZMod 4)) :
            Units (Matrix (Fin 2) (Fin 2) K)) :
          Matrix (Fin 2) (Fin 2) K))) := hmul_matrix
    _ = ((-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K)) * quaternion_split_matrix_k (K := K) a b := by
          rw [quaternionGroupTwoToSplitMatrixUnits_a_two (K := K) a b h,
            quaternionGroupTwoToSplitMatrixUnits_xa_three (K := K) a b h]
    _ = -quaternion_split_matrix_k (K := K) a b := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [quaternion_split_matrix_k]

/-- Helper for Exercise 12-12.2-5: in the split model, the element `xa 2 = -j` acts by `-J`. -/
theorem quaternionGroupTwoToSplitMatrixUnits_xa_two
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    ((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
        (QuaternionGroup.xa (2 : ZMod 4)) :
          Units (Matrix (Fin 2) (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K) =
      -quaternion_split_matrix_j (K := K) a b := by
  -- Route correction: use the source relation `xa 2 = (-1) * xa 0`, so the split matrix is
  -- `(-1) · J(a,b)`.
  have hmul :
      (QuaternionGroup.xa (2 : ZMod 4) : Q8) =
        QuaternionGroup.a (2 : ZMod 4) * QuaternionGroup.xa (0 : ZMod 4) := by
    native_decide
  have hmul_matrix :
      (((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
          (QuaternionGroup.xa (2 : ZMod 4)) :
            Units (Matrix (Fin 2) (Fin 2) K)) :
          Matrix (Fin 2) (Fin 2) K)) =
        ((((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
            (QuaternionGroup.a (2 : ZMod 4)) :
              Units (Matrix (Fin 2) (Fin 2) K)) :
            Matrix (Fin 2) (Fin 2) K)) *
          (((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
            (QuaternionGroup.xa (0 : ZMod 4)) :
              Units (Matrix (Fin 2) (Fin 2) K)) :
            Matrix (Fin 2) (Fin 2) K))) := by
    rw [hmul]
    exact congrArg
      (fun u : Units (Matrix (Fin 2) (Fin 2) K) ↦ (u : Matrix (Fin 2) (Fin 2) K))
      ((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h).map_mul
        (QuaternionGroup.a (2 : ZMod 4)) (QuaternionGroup.xa (0 : ZMod 4)))
  calc
    (((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
        (QuaternionGroup.xa (2 : ZMod 4)) :
          Units (Matrix (Fin 2) (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K)) =
        ((((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
          (QuaternionGroup.a (2 : ZMod 4)) :
            Units (Matrix (Fin 2) (Fin 2) K)) :
          Matrix (Fin 2) (Fin 2) K)) *
        (((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
          (QuaternionGroup.xa (0 : ZMod 4)) :
            Units (Matrix (Fin 2) (Fin 2) K)) :
          Matrix (Fin 2) (Fin 2) K))) := hmul_matrix
    _ = ((-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K)) * quaternion_split_matrix_j (K := K) a b := by
          rw [quaternionGroupTwoToSplitMatrixUnits_a_two (K := K) a b h,
            quaternionGroupTwoToSplitMatrixUnits_xa_zero (K := K) a b h]
    _ = -quaternion_split_matrix_j (K := K) a b := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [quaternion_split_matrix_j]

/-- Helper for Exercise 12-12.2-5: the split matrix model yields the expected two-dimensional
representation of `Q8`. -/
def quaternionGroupTwoSplitRepresentation
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    Representation K Q8 (Fin 2 → K) where
  toFun g :=
    ((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h g :
        Units (Matrix (Fin 2) (Fin 2) K)) :
      Matrix (Fin 2) (Fin 2) K).mulVecLin
  map_one' := by
    -- The identity matrix acts trivially on `K²`.
    ext v i
    simp [quaternionGroupTwoToSplitMatrixUnits]
  map_mul' g g' := by
    -- Matrix multiplication matches composition of the action maps.
    ext v i
    simp [quaternionGroupTwoToSplitMatrixUnits, Matrix.mulVecLin_mul]

/-- Helper for Exercise 12-12.2-5: the trace of matrix multiplication on `K²` is the ordinary
matrix trace. -/
theorem matrix_trace_eq_trace_mulVecLin
    (M : Matrix (Fin 2) (Fin 2) K) :
    LinearMap.trace K (Fin 2 → K) M.mulVecLin = Matrix.trace M := by
  -- `Matrix.mulVecLin` is the standard `toLin'` model, so its trace is the ordinary matrix trace.
  simpa [Matrix.toLin'_apply'] using Matrix.trace_toLin'_eq M

/-- Helper for Exercise 12-12.2-5: the split two-dimensional model has exactly the quaternionic
character table `2, -2, 0`. -/
theorem quaternionGroupTwoSplitRepresentation_character_apply
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) (s : Q8) :
    (quaternionGroupTwoSplitRepresentation (K := K) a b h).character s =
      quaternionGroupTwoQuaternionCharacterOver (K := K) s := by
  -- Evaluate the explicit split `2 × 2` matrices on the eight elements of `Q8`.
  change
    LinearMap.trace K (Fin 2 → K)
        ((((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h s :
            Units (Matrix (Fin 2) (Fin 2) K)) :
              Matrix (Fin 2) (Fin 2) K)).mulVecLin) =
      quaternionGroupTwoQuaternionCharacterOver (K := K) s
  rw [matrix_trace_eq_trace_mulVecLin]
  cases s with
  | a i =>
      fin_cases i
      · -- At the identity the action matrix is `1`, so the trace is `2`.
        change Matrix.trace
            ((((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h (1 : Q8) :
                Units (Matrix (Fin 2) (Fin 2) K)) :
                Matrix (Fin 2) (Fin 2) K))) = 2
        simp [quaternionGroupTwoToSplitMatrixUnits, Matrix.trace]
      · -- The image of `a 1` is the matrix `I`, whose trace vanishes.
        simpa [quaternion_split_matrix_i, quaternionGroupTwoQuaternionCharacterOver, Matrix.trace]
          using congrArg Matrix.trace
            (quaternionGroupTwoToSplitMatrixUnits_a_one (K := K) a b h)
      · -- The central involution acts by `-1`, so the trace is `-2`.
        simpa [quaternionGroupTwoQuaternionCharacterOver, Matrix.trace] using
          congrArg Matrix.trace
            (quaternionGroupTwoToSplitMatrixUnits_a_two (K := K) a b h)
      · -- The image of `a 3 = -i` is `-I`, which still has trace `0`.
        simpa [quaternion_split_matrix_i, quaternionGroupTwoQuaternionCharacterOver, Matrix.trace]
          using congrArg Matrix.trace
            (quaternionGroupTwoToSplitMatrixUnits_a_three (K := K) a b h)
  | xa i =>
      fin_cases i
      · -- The image of `xa 0` is `J(a,b)`, whose trace is `0`.
        simpa [quaternion_split_matrix_j, quaternionGroupTwoQuaternionCharacterOver, Matrix.trace]
          using congrArg Matrix.trace
            (quaternionGroupTwoToSplitMatrixUnits_xa_zero (K := K) a b h)
      · -- The image of `xa 1 = -k` is `-K(a,b)`, which has trace `0`.
        simpa [quaternion_split_matrix_k, quaternionGroupTwoQuaternionCharacterOver, Matrix.trace]
          using congrArg Matrix.trace
            (quaternionGroupTwoToSplitMatrixUnits_xa_one (K := K) a b h)
      · -- The image of `xa 2 = -j` is `-J(a,b)`, which has trace `0`.
        simpa [quaternion_split_matrix_j, quaternionGroupTwoQuaternionCharacterOver, Matrix.trace]
          using congrArg Matrix.trace
            (quaternionGroupTwoToSplitMatrixUnits_xa_two (K := K) a b h)
      · -- The image of `xa 3 = k` is `K(a,b)`, whose trace is `0`.
        simpa [quaternion_split_matrix_k, quaternionGroupTwoQuaternionCharacterOver, Matrix.trace]
          using congrArg Matrix.trace
            (quaternionGroupTwoToSplitMatrixUnits_xa_three (K := K) a b h)

/-- Helper for Exercise 12-12.2-5: in the split model, the central involution `a 2 = -1`
acts by the scalar `-1`. -/
theorem quaternionGroupTwoSplitRepresentation_a_two_eq_neg_one
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.a (2 : ZMod 4)) =
      (-1 : K) • LinearMap.id := by
  -- The explicit split table sends `a 2` to the matrix `-1`, so its action on `K²` is scalar
  -- multiplication by `-1`.
  apply LinearMap.ext
  intro v
  ext i
  change
    ((((quaternionGroupTwoToSplitMatrixUnits (K := K) a b h
        (QuaternionGroup.a (2 : ZMod 4)) :
          Units (Matrix (Fin 2) (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K).mulVec v) i) =
      (((((-1 : K) •
          (LinearMap.id : (Fin 2 → K) →ₗ[K] (Fin 2 → K))) v) i))
  rw [quaternionGroupTwoToSplitMatrixUnits_a_two (K := K) a b h]
  fin_cases i <;> simp [Matrix.mulVec, Fin.sum_univ_two]

/-- Helper for Exercise 12-12.2-5: the split-model generators `i` and `j` anticommute on `K²`.
-/
theorem quaternionGroupTwoSplitRepresentation_generators_anticommute
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.xa (0 : ZMod 4)) *
        quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.a (1 : ZMod 4)) =
      -(quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.a (1 : ZMod 4)) *
        quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.xa (0 : ZMod 4))) := by
  -- Rewrite `xa 0 * a 1 = a 2 * (a 1 * xa 0)` inside the representation and identify `a 2`
  -- with the scalar `-1`.
  have hanticomm_group :
      (QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4) =
        QuaternionGroup.a (2 : ZMod 4) *
          (QuaternionGroup.a (1 : ZMod 4) * QuaternionGroup.xa (0 : ZMod 4)) := by
    native_decide
  calc
    quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.xa (0 : ZMod 4)) *
        quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.a (1 : ZMod 4)) =
      quaternionGroupTwoSplitRepresentation (K := K) a b h
        ((QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4)) := by
          simpa using
            ((quaternionGroupTwoSplitRepresentation (K := K) a b h).map_mul
              (QuaternionGroup.xa (0 : ZMod 4)) (QuaternionGroup.a (1 : ZMod 4))).symm
    _ =
      quaternionGroupTwoSplitRepresentation (K := K) a b h
        (QuaternionGroup.a (2 : ZMod 4) *
          (QuaternionGroup.a (1 : ZMod 4) * QuaternionGroup.xa (0 : ZMod 4))) := by
            rw [hanticomm_group]
    _ =
      quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.a (2 : ZMod 4)) *
        (quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.a (1 : ZMod 4)) *
          quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.xa (0 : ZMod 4))) := by
            rw [(quaternionGroupTwoSplitRepresentation (K := K) a b h).map_mul,
              (quaternionGroupTwoSplitRepresentation (K := K) a b h).map_mul]
    _ = ((-1 : K) • LinearMap.id) *
        (quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.a (1 : ZMod 4)) *
          quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.xa (0 : ZMod 4))) := by
            rw [quaternionGroupTwoSplitRepresentation_a_two_eq_neg_one (K := K) a b h]
    _ = (-1 : K) •
        (quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.a (1 : ZMod 4)) *
          quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.xa (0 : ZMod 4))) := by
            ext v i
            rfl
    _ = -(quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.a (1 : ZMod 4)) *
        quaternionGroupTwoSplitRepresentation (K := K) a b h (QuaternionGroup.xa (0 : ZMod 4))) := by
          simp

/-- Helper for Exercise 12-12.2-5: a bundled subrepresentation defines an invariant submodule. -/
theorem toSubmodule_mem_invtSubmodule_local
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K Q8 V) (σ : Subrepresentation ρ) :
    σ.toSubmodule ∈ ρ.invtSubmodule := by
  -- Unpack the bundled stability witness into the ambient invariant-submodule owner.
  simpa [Representation.mem_invtSubmodule,
    Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] using σ.apply_mem_toSubmodule

/-- Helper for Exercise 12-12.2-5: repackage an invariant submodule as a subrepresentation. -/
def subrepresentationOfInvtSubmodule_local
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K Q8 V) (W : ρ.invtSubmodule) :
    Subrepresentation ρ where
  toSubmodule := W
  apply_mem_toSubmodule := by
    -- The invariant-submodule witness is exactly the stability needed for a subrepresentation.
    intro g v hv
    have hW : (↑W : Submodule K V) ∈ Module.End.invtSubmodule (ρ g) :=
      (ρ.mem_invtSubmodule.mp W.property) g
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hW
    exact hW v hv

/-- Helper for Exercise 12-12.2-5: complementary invariant subspaces split a representation as a
product. -/
theorem prodEquivOfIsCompl_isIntertwining_local
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K Q8 V) (σ τ : Subrepresentation ρ)
    (hστ : IsCompl σ.toSubmodule τ.toSubmodule) :
    ∀ g,
      ↑(σ.toSubmodule.prodEquivOfIsCompl τ.toSubmodule hστ) ∘ₗ
          (σ.toRepresentation.prod τ.toRepresentation) g =
        ρ g ∘ₗ ↑(σ.toSubmodule.prodEquivOfIsCompl τ.toSubmodule hστ) := by
  -- On each factor, the complement equivalence is just the subtype inclusion into the ambient
  -- representation.
  intro g
  ext z
  · simpa [Submodule.coe_prodEquivOfIsCompl, LinearMap.comp_apply, LinearMap.coe_inl,
      LinearMap.coprod_apply, LinearMap.prodMap_apply, Submodule.coe_subtype, Representation.prod]
      using (show ↑((σ.toRepresentation g) z) = (ρ g) ↑z from rfl)
  · simpa [Submodule.coe_prodEquivOfIsCompl, LinearMap.comp_apply, LinearMap.coe_inr,
      LinearMap.coprod_apply, LinearMap.prodMap_apply, Submodule.coe_subtype, Representation.prod]
      using (show ↑((τ.toRepresentation g) z) = (ρ g) ↑z from rfl)

/-- Helper for Exercise 12-12.2-5: complementary invariant subspaces give an equivariant product
decomposition. -/
def prodEquivOfIsCompl_local
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K Q8 V) (σ τ : Subrepresentation ρ)
    (hστ : IsCompl σ.toSubmodule τ.toSubmodule) :
    (σ.toRepresentation.prod τ.toRepresentation).Equiv ρ :=
  Representation.Equiv.mk
    (σ.toSubmodule.prodEquivOfIsCompl τ.toSubmodule hστ)
    (prodEquivOfIsCompl_isIntertwining_local (K := K) ρ σ τ hστ)

/-- Helper for Exercise 12-12.2-5: a non-irreducible nontrivial representation contains a
nonzero proper subrepresentation. -/
theorem exists_proper_nonzero_subrepresentation_of_not_isIrreducible_local
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Rep K Q8) [Nontrivial ρ] (hρ : ¬ ρ.ρ.IsIrreducible) :
    ∃ W : Subrepresentation ρ.ρ, W ≠ ⊥ ∧ W ≠ ⊤ := by
  have hbot_top : (⊥ : Subrepresentation ρ.ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : ρ)
    have hxmem : x ∈ (⊥ : Subrepresentation ρ.ρ) := by
      have hxTop : x ∈ (⊤ : Subrepresentation ρ.ρ) := by
        change x ∈ ((⊤ : Subrepresentation ρ.ρ).toSubmodule)
        exact Submodule.mem_top
      rw [← h] at hxTop
      exact hxTop
    exact hx <| by simpa using hxmem
  letI : Nontrivial (Subrepresentation ρ.ρ) := ⟨⟨⊥, ⊤, hbot_top⟩⟩
  have hnot : ¬ ∀ W : Subrepresentation ρ.ρ, W = ⊥ ∨ W = ⊤ := by
    intro hsimple
    exact hρ ⟨hsimple⟩
  rcases not_forall.mp hnot with ⟨W, hW⟩
  refine ⟨W, ?_, ?_⟩
  · intro hWbot
    exact hW (Or.inl hWbot)
  · intro hWtop
    exact hW (Or.inr hWtop)

/-- Helper for Exercise 12-12.2-5: every one-dimensional `Q8`-representation is trivial on the
central involution `-1 = a 2`. -/
theorem quaternionGroupTwo_central_involution_character_eq_one_of_finrank_eq_one
    {V : Type*} [AddCommGroup V] [Module K V]
    (τ : Representation K Q8 V) [FiniteDimensional K V]
    (hV : Module.finrank K V = 1) :
    τ.character (QuaternionGroup.a (2 : ZMod 4)) = 1 := by
  have hVpos : 0 < Module.finrank K V := by
    omega
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos hVpos
  let A := τ (QuaternionGroup.xa (0 : ZMod 4))
  let B := τ (QuaternionGroup.a (1 : ZMod 4))
  obtain ⟨α, hA, -⟩ := A.existsUnique_eq_smul_id_of_finrank_eq_one hV
  obtain ⟨β, hB, -⟩ := B.existsUnique_eq_smul_id_of_finrank_eq_one hV
  have hanticomm_group :
      (QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4) =
        QuaternionGroup.a (2 : ZMod 4) *
          (QuaternionGroup.a (1 : ZMod 4) * QuaternionGroup.xa (0 : ZMod 4)) := by
    native_decide
  have hA_ne_zero : α ≠ 0 := by
    intro hα
    have hzeroA : A = 0 := by simpa [hα] using hA
    have hmul :=
      τ.map_mul (QuaternionGroup.xa (0 : ZMod 4))
        ((QuaternionGroup.xa (0 : ZMod 4))⁻¹)
    have : (0 : V →ₗ[K] V) = 1 := by
      simpa [A, hzeroA] using hmul
    exact zero_ne_one this
  have hB_ne_zero : β ≠ 0 := by
    intro hβ
    have hzeroB : B = 0 := by simpa [hβ] using hB
    have hmul :=
      τ.map_mul (QuaternionGroup.a (1 : ZMod 4))
        ((QuaternionGroup.a (1 : ZMod 4))⁻¹)
    have : (0 : V →ₗ[K] V) = 1 := by
      simpa [B, hzeroB] using hmul
    exact zero_ne_one this
  have hαβ : α * β ≠ 0 := mul_ne_zero hA_ne_zero hB_ne_zero
  have hAB_scalar : A * B = (α * β : K) • LinearMap.id := by
    -- In dimension `1`, both generators act by scalars, so their product is scalar too.
    calc
      A * B = (α • LinearMap.id) * (β • LinearMap.id) := by rw [hA, hB]
      _ = (α * β : K) • LinearMap.id := by
          ext x
          simp [LinearMap.comp_apply, smul_smul, mul_assoc, mul_comm, mul_left_comm]
  have hBA_scalar : B * A = (α * β : K) • LinearMap.id := by
    -- The reversed product gives the same scalar because the base field is commutative.
    calc
      B * A = (β • LinearMap.id) * (α • LinearMap.id) := by rw [hB, hA]
      _ = (β * α : K) • LinearMap.id := by
          ext x
          simp [LinearMap.comp_apply, smul_smul, mul_assoc, mul_comm, mul_left_comm]
      _ = (α * β : K) • LinearMap.id := by rw [mul_comm]
  have hscaled :
      (α * β : K) • LinearMap.id =
        τ (QuaternionGroup.a (2 : ZMod 4)) * ((α * β : K) • LinearMap.id) := by
    -- The source relation `ji = (-1)(ij)` collapses in dimension `1` because both generators act
    -- by scalars.
    calc
      (α * β : K) • LinearMap.id = A * B := hAB_scalar.symm
      _ = τ ((QuaternionGroup.xa (0 : ZMod 4) : Q8) * QuaternionGroup.a (1 : ZMod 4)) := by
        simpa [A, B] using
          (τ.map_mul (QuaternionGroup.xa (0 : ZMod 4)) (QuaternionGroup.a (1 : ZMod 4))).symm
      _ = τ
          (QuaternionGroup.a (2 : ZMod 4) *
            (QuaternionGroup.a (1 : ZMod 4) * QuaternionGroup.xa (0 : ZMod 4))) := by
          rw [hanticomm_group]
      _ = τ (QuaternionGroup.a (2 : ZMod 4)) * (B * A) := by
          rw [τ.map_mul, τ.map_mul]
      _ = τ (QuaternionGroup.a (2 : ZMod 4)) * ((α * β : K) • LinearMap.id) := by
          rw [hBA_scalar]
  have hcentral : τ (QuaternionGroup.a (2 : ZMod 4)) = 1 := by
    -- Cancel the nonzero scalar factor to see that the central involution acts trivially.
    ext x
    have hx := congrArg (fun f : V →ₗ[K] V ↦ f x) hscaled
    have hx' : (α * β) • x = (α * β) • (τ (QuaternionGroup.a (2 : ZMod 4)) x) := by
      simpa [LinearMap.smul_apply, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hx
    exact (smul_right_inj hαβ).mp hx' |>.symm
  calc
    τ.character (QuaternionGroup.a (2 : ZMod 4)) = τ.character (1 : Q8) := by
      simp [Representation.character, hcentral]
    _ = 1 := by
      simpa [hV] using (Representation.char_one (ρ := τ))

/-- Helper for Exercise 12-12.2-5: the split nonlinear slot is simple once `-1 = a² + b²`.
-/
theorem quaternionGroupTwoSplitRepresentation_simple
    (a b : K) (h : -(1 : K) = a ^ 2 + b ^ 2) :
    CategoryTheory.Simple (FDRep.of (quaternionGroupTwoSplitRepresentation (K := K) a b h)) := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let ρ : Representation K Q8 (Fin 2 → K) :=
    quaternionGroupTwoSplitRepresentation (K := K) a b h
  by_cases hρirr : ρ.IsIrreducible
  · -- When the split model is already irreducible, the bundled `FDRep` is simple.
    letI : Representation.IsIrreducible (FDRep.of ρ).ρ := by
      simpa [ρ] using hρirr
    simpa [ρ] using FDRep.simple_of_isIrreducible (FDRep.of ρ)
  · -- Route correction: split a hypothetical reducible `2`-dimensional model into two lines, and
    -- compare the value of the central involution on each line with the explicit value `-2`.
    let ρrep : Rep K Q8 := Rep.of ρ
    have hρfin : Module.finrank K ρrep = 2 := by
      change Module.finrank K (Fin 2 → K) = 2
      simp
    letI : Nontrivial ρrep := by
      change Nontrivial (Fin 2 → K)
      infer_instance
    letI : NeZero (Nat.card Q8 : K) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
    have hρrep_irr : ¬ ρrep.ρ.IsIrreducible := by
      simpa [ρrep, ρ] using hρirr
    obtain ⟨σ, hσ_ne_bot, hσ_ne_top⟩ :=
      exists_proper_nonzero_subrepresentation_of_not_isIrreducible_local
        (K := K) (V := ρrep) (ρ := ρrep) hρrep_irr
    obtain ⟨V₀, hV₀⟩ :=
      exists_isCompl_of_mem_invtSubmodule ρ σ.toSubmodule
        (toSubmodule_mem_invtSubmodule_local (K := K) ρ σ)
    let ρ₀ : Subrepresentation ρ := subrepresentationOfInvtSubmodule_local (K := K) ρ V₀
    have hρ₀ : IsCompl σ.toSubmodule ρ₀.toSubmodule := by
      simpa [ρ₀, subrepresentationOfInvtSubmodule_local] using hV₀
    have hσ_fin_lt : Module.finrank K σ.toSubmodule < 2 := by
      have hσ_toSubmodule_ne_top : σ.toSubmodule ≠ ⊤ := by
        intro hσ_top
        exact hσ_ne_top (Subrepresentation.toSubmodule_injective hσ_top)
      simpa [hρfin] using
        (Submodule.finrank_lt (K := K) (V := ρrep) (s := σ.toSubmodule) hσ_toSubmodule_ne_top)
    have hσ_fin_pos : 0 < Module.finrank K σ.toSubmodule := by
      letI : Nontrivial σ.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr <| by
        intro hσ_bot
        exact hσ_ne_bot (Subrepresentation.toSubmodule_injective hσ_bot)
      exact Module.finrank_pos
    have hσ_fin : Module.finrank K σ.toSubmodule = 1 := by
      omega
    have hρ₀_fin_sum :
        Module.finrank K σ.toSubmodule + Module.finrank K ρ₀.toSubmodule = 2 := by
      simpa [hρfin] using (Submodule.finrank_add_eq_of_isCompl hρ₀)
    have hρ₀_fin : Module.finrank K ρ₀.toSubmodule = 1 := by
      omega
    let eρ : (σ.toRepresentation.prod ρ₀.toRepresentation).Equiv ρ :=
      prodEquivOfIsCompl_local (K := K) ρ σ ρ₀ hρ₀
    have hchar_split :
        ρ.character (QuaternionGroup.a (2 : ZMod 4)) =
          σ.toRepresentation.character (QuaternionGroup.a (2 : ZMod 4)) +
            ρ₀.toRepresentation.character (QuaternionGroup.a (2 : ZMod 4)) := by
      have hchar :
          σ.toRepresentation.character + ρ₀.toRepresentation.character = ρ.character := by
        calc
          σ.toRepresentation.character + ρ₀.toRepresentation.character =
              (σ.toRepresentation.prod ρ₀.toRepresentation).character := by
                symm
                exact Representation.char_prod σ.toRepresentation ρ₀.toRepresentation
          _ = ρ.character := Representation.char_iso eρ
      exact (congrFun hchar (QuaternionGroup.a (2 : ZMod 4))).symm
    have hσ_a_two :
        σ.toRepresentation.character (QuaternionGroup.a (2 : ZMod 4)) = 1 :=
      quaternionGroupTwo_central_involution_character_eq_one_of_finrank_eq_one
        (K := K) (τ := σ.toRepresentation) hσ_fin
    have hρ₀_a_two :
        ρ₀.toRepresentation.character (QuaternionGroup.a (2 : ZMod 4)) = 1 :=
      quaternionGroupTwo_central_involution_character_eq_one_of_finrank_eq_one
        (K := K) (τ := ρ₀.toRepresentation) hρ₀_fin
    have hsplit_a_two :
        ρ.character (QuaternionGroup.a (2 : ZMod 4)) = (-2 : K) := by
      simpa [ρ] using
        quaternionGroupTwoSplitRepresentation_character_apply
          (K := K) a b h (QuaternionGroup.a (2 : ZMod 4))
    have hbad : (-2 : K) = 1 + 1 := by
      calc
        (-2 : K) = ρ.character (QuaternionGroup.a (2 : ZMod 4)) := hsplit_a_two.symm
        _ =
            σ.toRepresentation.character (QuaternionGroup.a (2 : ZMod 4)) +
              ρ₀.toRepresentation.character (QuaternionGroup.a (2 : ZMod 4)) := hchar_split
        _ = 1 + 1 := by rw [hσ_a_two, hρ₀_a_two]
    have hbad_rat : (-2 : ℚ) = 1 + 1 := by
      exact_mod_cast hbad
    norm_num at hbad_rat

/-- Helper for Exercise 12-12.2-5: the nonlinear split character is separated from every linear
slot by its value at the identity. -/
theorem quaternionGroupTwoQuaternionCharacterOver_ne_linear_character
    (n : Fin 4) :
    quaternionGroupTwoQuaternionCharacterOver (K := K) ≠
      (quaternionGroupTwoLinearRepresentation (K := K) n).character := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  -- The nonlinear slot has value `2` at `1`, whereas each linear slot has value `1`.
  intro hEq
  have hone := congrFun hEq (1 : Q8)
  have hlinear_one :
      (quaternionGroupTwoLinearRepresentation (K := K) n).character (1 : Q8) = 1 := by
    simpa [quaternionGroupTwoLinearRepresentation, quaternionGroupTwoLinearCharacterOver,
      quaternion_group_two_rational_linear_character_family] using
      scalarMonoidRepresentation_character_apply
        (K := K) (β := quaternionGroupTwoLinearCharacterOver (K := K) n) (1 : Q8)
  have htwo_eq_one : (2 : K) = 1 := by
    have hpsi_one : quaternionGroupTwoQuaternionCharacterOver (K := K) (1 : Q8) = 2 := by
      change quaternionGroupTwoQuaternionCharacterOver (K := K)
          (QuaternionGroup.a (0 : ZMod 4)) = 2
      simp [quaternionGroupTwoQuaternionCharacterOver]
    rw [hpsi_one, hlinear_one] at hone
    exact hone
  have hrat : (2 : ℚ) = 1 := by
    exact_mod_cast htwo_eq_one
  norm_num at hrat

/-- Helper for Exercise 12-12.2-5: a split witness makes the quaternionic nonlinear character an
honest finite-dimensional `K`-representation. -/
theorem quaternionGroupTwoQuaternionCharacterOver_fdRep_of_neg_one_sum_two_squares
    (hsum : ∃ a b : K, -(1 : K) = a ^ 2 + b ^ 2) :
    ∃ τ : FDRep K Q8, τ.character = quaternionGroupTwoQuaternionCharacterOver (K := K) := by
  rcases hsum with ⟨a, b, h⟩
  refine ⟨FDRep.of (quaternionGroupTwoSplitRepresentation (K := K) a b h), ?_⟩
  -- The explicit split model already has the required quaternionic character.
  ext s
  simpa using quaternionGroupTwoSplitRepresentation_character_apply
    (K := K) a b h s

/-- Helper for Exercise 12-12.2-5: the quaternionic nonlinear character always belongs to
LinearRepresentations_Serre_1977's owner `R̄[K](Q8)` because it is realized over the algebraic closure. -/
theorem quaternionGroupTwoQuaternionCharacterOver_mem_overlineCharacterRing :
    quaternionGroupTwoQuaternionCharacterOver (K := K) ∈ R̄[K](Q8) := by
  -- Realize the nonlinear slot over the algebraic closure, then read that realization in
  -- LinearRepresentations_Serre_1977's owner `R̄[K](Q8)`.
  rw [mem_overlineCharacterRingInExtension_iff]
  have hmap_two :
      algebraMap K (AlgebraicClosure K) (2 : K) = (2 : AlgebraicClosure K) := by
    -- The coefficient map preserves the natural number `2`.
    simpa using (map_natCast (algebraMap K (AlgebraicClosure K)) 2)
  have hmap_neg_two :
      algebraMap K (AlgebraicClosure K) (-((2 : K))) = (-2 : AlgebraicClosure K) := by
    -- The same coefficient map preserves `-2`.
    simpa using (map_intCast (algebraMap K (AlgebraicClosure K)) (-2))
  have hmap :
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft Q8)
          (quaternionGroupTwoQuaternionCharacterOver (K := K)) =
        quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
    -- The coefficientwise scalar extension preserves the explicit values `2`, `-2`, and `0`.
    ext s
    cases s with
    | a i =>
        fin_cases i
        · change algebraMap K (AlgebraicClosure K) (2 : K) = (2 : AlgebraicClosure K)
          exact hmap_two
        · change algebraMap K (AlgebraicClosure K) (0 : K) = (0 : AlgebraicClosure K)
          simp
        · change algebraMap K (AlgebraicClosure K) (-((2 : K))) = (-2 : AlgebraicClosure K)
          exact hmap_neg_two
        · change algebraMap K (AlgebraicClosure K) (0 : K) = (0 : AlgebraicClosure K)
          simp
    | xa i =>
        fin_cases i <;> simp [quaternionGroupTwoQuaternionCharacterOver]
  rcases neg_one_sum_two_squares_in_algebraicClosure (K := K) with ⟨a, b, h⟩
  rcases quaternionGroupTwoQuaternionCharacterOver_fdRep_of_neg_one_sum_two_squares
      (K := AlgebraicClosure K) ⟨a, b, h⟩ with ⟨τ, hτchar⟩
  have hpsi_alg :
      quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) ∈
        R[AlgebraicClosure K](Q8) := by
    have hτmem : τ.character ∈ R[AlgebraicClosure K](Q8) := by
      simpa using
        rep_character_mem_characterRingOverField
          (K := AlgebraicClosure K) (G := Q8) (ρ := Rep.of τ.ρ)
    simpa [hτchar] using hτmem
  exact hmap ▸ hpsi_alg

/-- Helper for Exercise 12-12.2-5: coefficientwise scalar extension sends the quaternionic `K`
character to the same explicit table over `AlgebraicClosure K`. -/
theorem quaternionGroupTwoQuaternionCharacterOver_scalarExtension :
    ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft Q8)
        (quaternionGroupTwoQuaternionCharacterOver (K := K)) =
      quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
  have hmap_two :
      algebraMap K (AlgebraicClosure K) (2 : K) = (2 : AlgebraicClosure K) := by
    -- The coefficient map preserves the natural number `2`.
    simpa using (map_natCast (algebraMap K (AlgebraicClosure K)) 2)
  have hmap_neg_two :
      algebraMap K (AlgebraicClosure K) (-((2 : K))) = (-2 : AlgebraicClosure K) := by
    -- The same coefficient map preserves `-2`.
    simpa using (map_intCast (algebraMap K (AlgebraicClosure K)) (-2))
  -- The explicit quaternionic table only uses the values `2`, `-2`, and `0`.
  ext s
  cases s with
  | a i =>
      fin_cases i
      · change algebraMap K (AlgebraicClosure K) (2 : K) = (2 : AlgebraicClosure K)
        exact hmap_two
      · change algebraMap K (AlgebraicClosure K) (0 : K) = (0 : AlgebraicClosure K)
        simp
      · change algebraMap K (AlgebraicClosure K) (-((2 : K))) = (-2 : AlgebraicClosure K)
        exact hmap_neg_two
      · change algebraMap K (AlgebraicClosure K) (0 : K) = (0 : AlgebraicClosure K)
        simp
  | xa i =>
      fin_cases i <;> simp [quaternionGroupTwoQuaternionCharacterOver]

/-- Helper for Exercise 12-12.2-5: the four linear `Q8`-slots stay pairwise nonisomorphic over
every `ℚ`-algebra. -/
theorem quaternionGroupTwoRationalLinearCharacter_separated
    (i j : Fin 4) (hij : i ≠ j) :
    quaternion_group_two_rational_linear_character_family i
        (QuaternionGroup.a (1 : ZMod 4)) ≠
      quaternion_group_two_rational_linear_character_family j
        (QuaternionGroup.a (1 : ZMod 4)) ∨
    quaternion_group_two_rational_linear_character_family i
        (QuaternionGroup.xa (0 : ZMod 4)) ≠
      quaternion_group_two_rational_linear_character_family j
        (QuaternionGroup.xa (0 : ZMod 4)) := by
  -- The four rational linear characters are separated by their values on `a 1` or `xa 0`.
  fin_cases i <;> fin_cases j <;> try contradiction
  · right
    simp [quaternion_group_two_rational_linear_character_family]
    norm_num
  · left
    have hval : (1 : ZMod 4).val = 1 := rfl
    simpa [quaternion_group_two_rational_linear_character_family, hval] using
      (show (1 : ℚ) ≠ (-1 : ℚ) by norm_num)
  · left
    have hval : (1 : ZMod 4).val = 1 := rfl
    simpa [quaternion_group_two_rational_linear_character_family, hval] using
      (show (1 : ℚ) ≠ (-1 : ℚ) by norm_num)
  · right
    simp [quaternion_group_two_rational_linear_character_family]
    norm_num
  · left
    have hval : (1 : ZMod 4).val = 1 := rfl
    simpa [quaternion_group_two_rational_linear_character_family, hval] using
      (show (1 : ℚ) ≠ (-1 : ℚ) by norm_num)
  · left
    have hval : (1 : ZMod 4).val = 1 := rfl
    simpa [quaternion_group_two_rational_linear_character_family, hval] using
      (show (1 : ℚ) ≠ (-1 : ℚ) by norm_num)
  · left
    have hval : (1 : ZMod 4).val = 1 := rfl
    simpa [quaternion_group_two_rational_linear_character_family, hval] using
      (show (-1 : ℚ) ≠ (1 : ℚ) by norm_num)
  · left
    have hval : (1 : ZMod 4).val = 1 := rfl
    simpa [quaternion_group_two_rational_linear_character_family, hval] using
      (show (-1 : ℚ) ≠ (1 : ℚ) by norm_num)
  · right
    simp [quaternion_group_two_rational_linear_character_family]
    norm_num
  · left
    have hval : (1 : ZMod 4).val = 1 := rfl
    simpa [quaternion_group_two_rational_linear_character_family, hval] using
      (show (-1 : ℚ) ≠ (1 : ℚ) by norm_num)
  · left
    have hval : (1 : ZMod 4).val = 1 := rfl
    simpa [quaternion_group_two_rational_linear_character_family, hval] using
      (show (-1 : ℚ) ≠ (1 : ℚ) by norm_num)
  · right
    simp [quaternion_group_two_rational_linear_character_family]
    norm_num

/-- Helper for Exercise 12-12.2-5: the four linear `Q8`-slots stay pairwise nonisomorphic over
every `ℚ`-algebra. -/
theorem quaternionGroupTwoLinearRepresentation_pairwise :
    CategoryTheory.PairwiseNonisomorphic
      (fun n : Fin 4 ↦ quaternionGroupTwoLinearRepresentation (K := K) n) := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  intro i j hij hij_iso
  rcases hij_iso with ⟨e⟩
  have ha :=
    congrFun (FDRep.char_iso e) (QuaternionGroup.a (1 : ZMod 4))
  have hxa :=
    congrFun (FDRep.char_iso e) (QuaternionGroup.xa (0 : ZMod 4))
  have hsep := quaternionGroupTwoRationalLinearCharacter_separated i j hij
  rcases hsep with ha_sep | hxa_sep
  · have haQ :
        algebraMap ℚ K
            (quaternion_group_two_rational_linear_character_family i
              (QuaternionGroup.a (1 : ZMod 4))) =
          algebraMap ℚ K
            (quaternion_group_two_rational_linear_character_family j
              (QuaternionGroup.a (1 : ZMod 4))) := by
      simpa [quaternionGroupTwoLinearRepresentation_character_apply] using ha
    exact ha_sep ((algebraMap ℚ K).injective haQ)
  · have hxaQ :
        algebraMap ℚ K
            (quaternion_group_two_rational_linear_character_family i
              (QuaternionGroup.xa (0 : ZMod 4))) =
          algebraMap ℚ K
            (quaternion_group_two_rational_linear_character_family j
              (QuaternionGroup.xa (0 : ZMod 4))) := by
      simpa [quaternionGroupTwoLinearRepresentation_character_apply] using hxa
    exact hxa_sep ((algebraMap ℚ K).injective hxaQ)

-- Proof sketch: quasisplitness identifies `R[K](Q8)` with `\overline{R}_K(Q8)`, so the explicit
-- nonlinear quaternionic slot moves from the algebraic-closure owner into the honest character
-- ring over `K`.
/-- Helper for Exercise 12-12.2-5: in the quasisplit case, the explicit nonlinear quaternionic
character already lies in `R[K](Q8)`. -/
theorem quaternionGroupTwoQuaternionCharacterOver_mem_characterRing_of_isQuasisplit
    (hquasi : IsQuasisplitGroupAlgebra K Q8) :
    quaternionGroupTwoQuaternionCharacterOver (K := K) ∈ R[K](Q8) := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  -- Convert quasisplitness into LinearRepresentations_Serre_1977's owner equality and then reuse the algebraic-closure
  -- realization of the nonlinear slot.
  have hEq : R[K](Q8) = R̄[K](Q8) :=
    (characterRing_eq_overlineCharacterRing_iff_isQuasisplitGroupAlgebra
      (K := K) (G := Q8)).2 hquasi
  have hpsi_over :
      quaternionGroupTwoQuaternionCharacterOver (K := K) ∈ R̄[K](Q8) :=
    quaternionGroupTwoQuaternionCharacterOver_mem_overlineCharacterRing (K := K)
  rw [hEq]
  exact hpsi_over

-- Proof sketch: once the explicit quaternionic character is realized over `K`, the existing
-- quaternionic-matrix criterion produces `-1 = a² + b²`, and the split-matrix model then gives
-- the required algebra isomorphism.
/-- Helper for Exercise 12-12.2-5: any honest `K`-model of the nonlinear quaternionic character
forces the quaternion algebra factor to split. -/
theorem quaternionGroupTwo_groupAlgebra_forward_of_realizableQuaternionCharacter
    (hτ :
      ∃ τ : FDRep K Q8,
        τ.character = quaternionGroupTwoQuaternionCharacterOver (K := K)) :
    Nonempty (K ⊗[ℚ] ℍ[ℚ] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  rcases hτ with ⟨τ, hτchar⟩
  -- The existing realizability criterion turns the quaternionic character into a sum-of-squares
  -- witness for `-1`.
  have hsum :
      ∃ a b : K, -(1 : K) = a ^ 2 + b ^ 2 :=
    quaternionGroupTwoQuaternionCharacterOver_realizable_implies_neg_one_sum_two_squares
      (K := K) (τ := Rep.of τ.ρ) hτchar
  -- Feed that witness into the explicit quaternion-splitting construction.
  exact tensorQuaternion_split_of_neg_one_sum_two_squares (K := K) hsum

/-- Helper for Exercise 12-12.2-5: pairing a finite `ℤ`-linear combination with a test character
expands coefficientwise in the left variable. -/
private theorem groupFunctionPairing_sum_zsmul_left_local
    {ι : Type*} [Fintype ι] (s : Finset ι) (g : ι → ℤ) (χ : ι → Q8 → K) (ψ : Q8 → K) :
    ⟪∑ j ∈ s, g j • χ j, ψ⟫ = ∑ j ∈ s, (g j : K) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert a s ha ih =>
      -- Rewrite the inserted term as an honest `K`-scalar multiple before using bilinearity.
      have hzsmul : (g a • χ a : Q8 → K) = ((g a : K) • χ a) := by
        ext x
        simp [zsmul_eq_mul, smul_eq_mul]
      rw [Finset.sum_insert ha, Representation.groupFunctionPairing_add_left, hzsmul,
        Representation.groupFunctionPairing_smul_left, ih, Finset.sum_insert ha]

/-- Helper for Exercise 12-12.2-5: pairing a representation-ring element with an irreducible basis
character isolates the corresponding basis coefficient. -/
private theorem basis_coefficient_pairing_eq_local
    {ι : Type*} [Fintype ι] [CharZero K] (π : ι → FDRep K Q8)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R[K](Q8)) (i : ι) :
    ⟪(x : Q8 → K), (π i).character⟫ =
      ((((irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr x) i :
        ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
  letI : Invertible (Nat.card Q8 : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx :
      ∑ j, c j • (π j).character = (x : Q8 → K) := by
    -- Rewrite the basis expansion of `x` into the ambient function space.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R[K](Q8) ↦ (z : Q8 → K)) (b.sum_repr x)
  have horth :
      Pairwise fun j k ↦
        ⟪(π j).character, (π k).character⟫ = (0 : K) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      K π hπ_complete.isSimple hπ_pairwise
  calc
    ⟪(x : Q8 → K), (π i).character⟫
        = ⟪∑ j, c j • (π j).character, (π i).character⟫ := by
            -- Replace `x` by its irreducible-basis expansion.
            simpa [hx] using
              congrArg
                (fun ψ : Q8 → K ↦ groupFunctionPairingOverField K ψ (π i).character)
                hx.symm
    _ = ∑ j, ((c j : ℤ) : K) * ⟪(π j).character, (π i).character⟫ := by
          -- Expand the pairing termwise across the finite sum.
          simpa [c] using
            groupFunctionPairing_sum_zsmul_left_local (K := K) (s := Finset.univ)
              (g := c) (χ := fun j ↦ (π j).character) (ψ := (π i).character)
    _ = ((c i : ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
          -- Orthogonality kills every off-diagonal basis term.
          refine Finset.sum_eq_single i ?_ ?_
          · intro j _ hji
            simp [horth hji]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim

/-- Helper for Exercise 12-12.2-5: the self-pairing of a simple character is a positive natural
number cast to `K`. -/
private theorem self_pairing_character_eq_natCast_pos_local
    (V : FDRep K Q8) [CategoryTheory.Simple V] :
    ∃ n : ℕ, 0 < n ∧ ⟪V.character, V.character⟫ = (n : K) := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  letI : Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
  letI : Invertible (Nat.card Q8 : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let n : ℕ := Module.finrank K (Representation.IntertwiningMap V.ρ V.ρ)
  have hn_pos : 0 < n := by
    have hV_nontriv : Nontrivial V := by
      by_contra hV_sub
      letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV_sub
      have hzero : (𝟙 V : V ⟶ V) = 0 := by
        ext x
        simp
      exact CategoryTheory.id_nonzero V hzero
    letI : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := by
      refine ⟨0, 1, ?_⟩
      intro hone
      obtain ⟨x, hx⟩ := exists_ne (0 : V)
      have hx0 := congrArg (fun f : Representation.IntertwiningMap V.ρ V.ρ ↦ f x) hone
      exact hx (by simpa using hx0.symm)
    -- The identity intertwiner shows that the self-endomorphism space has positive dimension.
    simpa [n] using
      (Module.finrank_pos_iff.mpr
        (inferInstance : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ)))
  have hpair :
      ⟪V.character, V.character⟫ = (n : K) := by
    -- The normalized self-pairing equals the dimension of the intertwining space.
    simpa [n] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        K V.ρ V.ρ)
  exact ⟨n, hn_pos, hpair⟩

/-- Helper for Exercise 12-12.2-5: the self-pairing of a simple character is nonzero. -/
private theorem self_pairing_character_ne_zero_local
    (V : FDRep K Q8) [CategoryTheory.Simple V] :
    ⟪V.character, V.character⟫ ≠ (0 : K) := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  rcases self_pairing_character_eq_natCast_pos_local (K := K) V with ⟨n, hn, hpair⟩
  rw [hpair]
  exact Nat.cast_ne_zero.mpr hn.ne'

/-- Helper for Exercise 12-12.2-5: the explicit quaternionic class function has self-pairing `1`.
-/
private theorem quaternionGroupTwoQuaternionCharacterOver_self_pairing :
    ⟪quaternionGroupTwoQuaternionCharacterOver (K := K),
      quaternionGroupTwoQuaternionCharacterOver (K := K)⟫ = 1 := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  letI : Invertible (Nat.card Q8 : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let a2 : Q8 := QuaternionGroup.a (2 : ZMod 4)
  let f : Q8 → K := fun g ↦
    quaternionGroupTwoQuaternionCharacterOver (K := K) g *
      quaternionGroupTwoQuaternionCharacterOver (K := K) g⁻¹
  have ha2_ne_one : a2 ≠ (1 : Q8) := by
    -- The central involution `a 2` is distinct from the identity `a 0`.
    intro h
    change (QuaternionGroup.a (2 : ZMod 4) : Q8) = QuaternionGroup.a (0 : ZMod 4) at h
    injection h with h'
    exact (by decide : (2 : ZMod 4) ≠ 0) h'
  have ha2_inv : a2⁻¹ = a2 := by
    -- In `Q8`, the central involution is its own inverse.
    change (QuaternionGroup.a (2 : ZMod 4) : Q8)⁻¹ = QuaternionGroup.a (2 : ZMod 4)
    native_decide
  have hvanish :
      ∀ g : Q8, g ≠ 1 → g ≠ a2 → f g = 0 := by
    intro g hg1 hg2
    -- Away from `{1, -1}`, the quaternionic character vanishes, so the product term vanishes too.
    have hψg : quaternionGroupTwoQuaternionCharacterOver (K := K) g = 0 := by
      rw [quaternionGroupTwoQuaternionCharacterOver_apply (K := K) g]
      simp [a2, hg1, hg2]
    simp [f, hψg]
  have hrest :
      Finset.sum ((Finset.univ.erase (1 : Q8)).erase a2) f = 0 := by
    -- After removing `1` and `-1`, every remaining summand is zero by the explicit character table.
    refine Finset.sum_eq_zero ?_
    intro g hg
    have hg_a2 : g ≠ a2 := (Finset.mem_erase.mp hg).1
    have hg1 : g ≠ (1 : Q8) := by
      exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hg)).1
    exact hvanish g hg1 hg_a2
  have hsum :
      Finset.sum Finset.univ f = 8 := by
    have hsplit1 :
        Finset.sum Finset.univ f = f 1 + Finset.sum (Finset.univ.erase (1 : Q8)) f := by
      -- Isolate the identity term from the full sum.
      symm
      simpa [add_comm] using
        (Finset.sum_erase_add (s := Finset.univ) (f := f) (by simp : (1 : Q8) ∈ Finset.univ))
    have ha2_mem : a2 ∈ Finset.univ.erase (1 : Q8) := by
      simp [ha2_ne_one]
    have hsplit2 :
        Finset.sum (Finset.univ.erase (1 : Q8)) f =
          f a2 + Finset.sum ((Finset.univ.erase (1 : Q8)).erase a2) f := by
      -- Then isolate the central involution from the remaining sum.
      symm
      simpa [add_comm] using
        (Finset.sum_erase_add (s := Finset.univ.erase (1 : Q8)) (f := f) ha2_mem)
    have hψ_one : quaternionGroupTwoQuaternionCharacterOver (K := K) (1 : Q8) = 2 := by
      -- The character has degree `2`.
      rw [quaternionGroupTwoQuaternionCharacterOver_apply (K := K) (1 : Q8)]
      simp
    have hψ_a2 : quaternionGroupTwoQuaternionCharacterOver (K := K) a2 = -2 := by
      -- The central involution has character value `-2`.
      rw [quaternionGroupTwoQuaternionCharacterOver_apply (K := K) a2]
      simp [a2, ha2_ne_one]
    calc
      Finset.sum Finset.univ f = f 1 + Finset.sum (Finset.univ.erase (1 : Q8)) f := hsplit1
      _ = f 1 + (f a2 + Finset.sum ((Finset.univ.erase (1 : Q8)).erase a2) f) := by
            rw [hsplit2]
      _ = f 1 + f a2 := by rw [hrest]; ring
      _ = 8 := by
            norm_num [f, hψ_one, hψ_a2, ha2_inv]
  -- The normalized pairing is `(1 / |Q8|)` times the explicit sum, so the value is `1`.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  have hcard : Nat.card Q8 = 8 := by
    simpa using (QuaternionGroup.card (n := 2))
  have huniv :
      (@Finset.univ Q8 QuaternionGroup.instFintypeOfNeZeroNat) =
        (@Finset.univ Q8 instFintypeGGroupFunctionPairingOverFieldTheorems) := by
    ext s
    simp
  have hsum' :
      Finset.sum (@Finset.univ Q8 instFintypeGGroupFunctionPairingOverFieldTheorems)
        (fun t ↦
          quaternionGroupTwoQuaternionCharacterOver (K := K) t *
            quaternionGroupTwoQuaternionCharacterOver (K := K) t⁻¹) = (8 : K) := by
    simpa [huniv, f] using hsum
  have hcardK : ((Nat.card Q8 : Nat) : K) = (8 : K) := by
    exact_mod_cast hcard
  have hcardInv : (((Nat.card Q8 : Nat) : K)⁻¹) = (8 : K)⁻¹ := by
    rw [hcardK]
  have h8_ne : (8 : K) ≠ 0 := by
    exact_mod_cast (show (8 : ℕ) ≠ 0 by decide)
  calc
    (((Nat.card Q8 : Nat) : K)⁻¹) *
        Finset.sum (@Finset.univ Q8 instFintypeGGroupFunctionPairingOverFieldTheorems)
          (fun s ↦
            quaternionGroupTwoQuaternionCharacterOver (K := K) s *
              quaternionGroupTwoQuaternionCharacterOver (K := K) s⁻¹)
        = (((Nat.card Q8 : Nat) : K)⁻¹) * (8 : K) := by
            rw [hsum']
    _ = (8 : K)⁻¹ * (8 : K) := by rw [hcardInv]
    _ = 1 := by simpa using inv_mul_cancel₀ h8_ne

/-- Helper for Exercise 12-12.2-5: a simple finite-dimensional `K`-representation has positive
degree. -/
private theorem simple_fdRep_finrank_pos_local
    (V : FDRep K Q8) [Simple V] :
    0 < Module.finrank K V := by
  have hV_nontriv : Nontrivial V := by
    by_contra hV_sub
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV_sub
    have hzero : (𝟙 V : V ⟶ V) = 0 := by
      ext x
      simp
    exact CategoryTheory.id_nonzero V hzero
  letI : Nontrivial V := hV_nontriv
  exact Module.finrank_pos

/-- Helper for Exercise 12-12.2-5: self-pairing `1` forces the irreducible-basis coefficients of
an element of `R[K](Q8)` to satisfy a weighted square-sum identity. -/
private theorem repr_weighted_square_sum_eq_one_of_self_pairing_eq_one
    {ι : Type*} [Fintype ι] [CharZero K]
    (π : ι → FDRep K Q8)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R[K](Q8))
    (n : ι → ℕ)
    (hdiag : ∀ i, ⟪(π i).character, (π i).character⟫ = (n i : K))
    (hpair : ⟪(x : Q8 → K), x⟫ = (1 : K)) :
    ∑ i,
        ((irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr x i)^2 *
          (n i : ℤ) = 1 := by
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx : ∑ j, c j • (π j).character = (x : Q8 → K) := by
    -- Rewrite the basis expansion of `x` into the ambient function space.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R[K](Q8) ↦ (z : Q8 → K)) (b.sum_repr x)
  have hcast :
      (((∑ i, (c i)^2 * (n i : ℤ) : ℤ) : K)) = ⟪(x : Q8 → K), x⟫ := by
    calc
      (((∑ i, (c i)^2 * (n i : ℤ) : ℤ) : K))
          = ∑ i, ((c i : ℤ) : K) * (((c i : ℤ) : K) * (n i : K)) := by
              -- Convert the weighted integer square sum into the ambient field sum.
              simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
      _ = ∑ i, ((c i : ℤ) : K) * ⟪(π i).character, (x : Q8 → K)⟫ := by
            -- Each basis coefficient is recovered by pairing with the corresponding character.
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Representation.groupFunctionPairing_comm,
              basis_coefficient_pairing_eq_local (K := K) (π := π) hπ_pairwise hπ_complete x i,
              hdiag i]
      _ = ⟪∑ i, c i • (π i).character, (x : Q8 → K)⟫ := by
            -- Reassemble the coefficient sum into a single pairing.
            symm
            simpa [c] using
              groupFunctionPairing_sum_zsmul_left_local (K := K) (s := Finset.univ)
                (g := c) (χ := fun i ↦ (π i).character) (ψ := (x : Q8 → K))
      _ = ⟪(x : Q8 → K), x⟫ := by
            rw [hx]
  have hcast_one : (((∑ i, (c i)^2 * (n i : ℤ) : ℤ) : K)) = (1 : K) := by
    rw [hcast, hpair]
  exact_mod_cast hcast_one

/-- Helper for Exercise 12-12.2-5: if a weighted sum of integer squares is `1`, exactly one
coefficient survives, with sign `±1`, and its weight is `1`. -/
private theorem weighted_integer_coefficients_eq_singleton_of_sq_mul_sum_eq_one
    {ι : Type*} [Fintype ι] (c : ι → ℤ) (n : ι → ℕ)
    (hn : ∀ i, 0 < n i)
    (h : ∑ i, (c i)^2 * (n i : ℤ) = 1) :
    ∃ i, (c i = 1 ∨ c i = -1) ∧ n i = 1 ∧ ∀ j, j ≠ i → c j = 0 := by
  classical
  have hnotallzero : ¬ ∀ i, c i = 0 := by
    intro hzero
    have hsum_zero : ∑ i, (c i)^2 * (n i : ℤ) = 0 := by
      simp [hzero]
    linarith
  obtain ⟨i, hi_nonzero⟩ : ∃ i, c i ≠ 0 := by
    simpa [not_forall] using hnotallzero
  have hi_term_le : (c i)^2 * (n i : ℤ) ≤ 1 := by
    calc
      (c i)^2 * (n i : ℤ) ≤ ∑ j, (c j)^2 * (n j : ℤ) := by
        simpa using
          (Finset.single_le_sum
            (fun j _ ↦ mul_nonneg (sq_nonneg (c j)) (by positivity : 0 ≤ (n j : ℤ)))
            (Finset.mem_univ i) :
              (c i)^2 * (n i : ℤ) ≤ ∑ j, (c j)^2 * (n j : ℤ))
      _ = 1 := h
  have hi_term_eq : (c i)^2 * (n i : ℤ) = 1 := by
    have hi_sq_ge_one : 1 ≤ (c i)^2 := by
      have hi_sq_pos : 0 < (c i)^2 := sq_pos_iff.mpr hi_nonzero
      linarith
    have hi_weight_ge_one : 1 ≤ (n i : ℤ) := by
      exact_mod_cast Nat.succ_le_of_lt (hn i)
    have hi_term_ge_one : 1 ≤ (c i)^2 * (n i : ℤ) := by
      nlinarith
    linarith
  have hi_sq_le : (c i)^2 ≤ 1 := by
    have hn_pos_int : 0 < (n i : ℤ) := by
      exact_mod_cast hn i
    nlinarith [hi_term_eq]
  have hi_sq_eq : (c i)^2 = 1 := by
    exact Int.sq_eq_one_of_sq_le_three (le_trans hi_sq_le (by norm_num)) hi_nonzero
  have hi_sign : c i = 1 ∨ c i = -1 := sq_eq_one_iff.mp hi_sq_eq
  have hi_weight_eq : n i = 1 := by
    have hi_weight_int : (n i : ℤ) = 1 := by
      simpa [hi_sq_eq] using hi_term_eq
    exact_mod_cast hi_weight_int
  refine ⟨i, hi_sign, hi_weight_eq, ?_⟩
  intro j hji
  have hsum_erase :
      Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2 * (n k : ℤ)) +
        (c i)^2 * (n i : ℤ) = 1 := by
    calc
      Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2 * (n k : ℤ)) +
          (c i)^2 * (n i : ℤ)
          = ∑ k, (c k)^2 * (n k : ℤ) := by
              simpa using
                (Finset.sum_erase_add (s := Finset.univ)
                  (f := fun k ↦ (c k)^2 * (n k : ℤ)) (Finset.mem_univ i))
      _ = 1 := h
  have herase_zero :
      Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2 * (n k : ℤ)) = 0 := by
    rw [hi_term_eq] at hsum_erase
    linarith
  have hj_term_le :
      (c j)^2 * (n j : ℤ) ≤
        Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2 * (n k : ℤ)) := by
    have hj_mem : j ∈ Finset.univ.erase i := by
      simp [hji]
    simpa using
      (Finset.single_le_sum
        (fun k _ ↦ mul_nonneg (sq_nonneg (c k)) (by positivity : 0 ≤ (n k : ℤ))) hj_mem :
          (c j)^2 * (n j : ℤ) ≤
            Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2 * (n k : ℤ)))
  have hj_term_eq_zero : (c j)^2 * (n j : ℤ) = 0 := by
    have hj_term_nonneg : 0 ≤ (c j)^2 * (n j : ℤ) := by
      exact mul_nonneg (sq_nonneg (c j)) (by positivity : 0 ≤ (n j : ℤ))
    linarith
  have hj_sq_eq_zero : (c j)^2 = 0 := by
    have hnj_pos_int : 0 < (n j : ℤ) := by
      exact_mod_cast hn j
    nlinarith [hj_term_eq_zero]
  exact sq_eq_zero_iff.mp hj_sq_eq_zero

/-- Helper for Exercise 12-12.2-5: every `FDRep` object is canonically isomorphic to the object
rebuilt from its underlying unbundled representation. -/
private noncomputable def fdRepIsoOfRho_local (τ : FDRep K Q8) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    ext x
    rfl

/-- Helper for Exercise 12-12.2-5: precomposing with a representation equivalence identifies
intertwining spaces with the same codomain. -/
private noncomputable def intertwiningMapCongrLeft_local
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    {W : Type*} [AddCommGroup W] [Module K W]
    {ρ : Representation K Q8 V₁} {σ : Representation K Q8 V₂}
    (e : ρ.Equiv σ) (τ : Representation K Q8 W) :
    Representation.IntertwiningMap σ τ ≃ₗ[K] Representation.IntertwiningMap ρ τ :=
  { toFun := fun f ↦ f.comp e.toIntertwiningMap
    invFun := fun f ↦ f.comp e.symm.toIntertwiningMap
    left_inv := by
      intro f
      apply Representation.IntertwiningMap.ext
      ext x
      simp
    right_inv := by
      intro f
      apply Representation.IntertwiningMap.ext
      ext x
      simp
    map_add' := by
      intro f g
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a f
      apply Representation.IntertwiningMap.ext
      ext x
      rfl }

/-- Helper for Exercise 12-12.2-5: intertwining maps from a direct sum are exactly families of
intertwining maps from each summand. -/
private noncomputable def directSumIntertwiningMapEquivPi_local
    {ι : Type*} {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module K (M i)]
    {W : Type*} [AddCommMonoid W] [Module K W]
    (π : ∀ i, Representation K Q8 (M i)) (τ : Representation K Q8 W) :
    Representation.IntertwiningMap (Representation.directSum π) τ ≃ₗ[K]
      ∀ i, Representation.IntertwiningMap (π i) τ :=
  let _ : DecidableEq ι := Classical.decEq ι
  { toFun := fun F i ↦
      ((F.toLinearMap.comp
          (DirectSum.lof K ι M i)).intertwiningMap_of_isIntertwiningMap
        (π i) τ fun g x ↦ by
          simpa [Representation.directSum] using
            congr($(F.isIntertwining' g) (DirectSum.lof K ι M i x)))
    invFun := fun f ↦
      { toLinearMap := DirectSum.toModule K ι W fun i ↦ (f i).toLinearMap
        isIntertwining' := by
          intro g
          apply DirectSum.linearMap_ext
          intro i
          ext x
          simp [Representation.directSum, Representation.IntertwiningMap.isIntertwining] }
    left_inv := by
      intro F
      apply Representation.IntertwiningMap.ext
      apply DirectSum.linearMap_ext
      intro i
      ext x
      change
        (DirectSum.toModule K ι W
          (fun j ↦ F.toLinearMap.comp (DirectSum.lof K ι M j)))
          (DirectSum.lof K ι M i x) =
        F (DirectSum.lof K ι M i x)
      simp
    right_inv := by
      intro f
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      change
        (DirectSum.toModule K ι W fun j ↦ (f j).toLinearMap)
          (DirectSum.lof K ι M i x) =
        (f i) x
      simp
    map_add' := by
      intro F H
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a F
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl }

/-- Helper for Exercise 12-12.2-5: a nonisomorphism hypothesis on two explicit irreducible
representations forces every intertwiner between them to vanish. -/
private theorem intertwiningMap_eq_zero_of_not_isomorphic_explicit_local
    {V1 : Type*} [AddCommGroup V1] [Module K V1]
    {V2 : Type*} [AddCommGroup V2] [Module K V2]
    (ρ1 : Representation K Q8 V1) [ρ1.IsIrreducible]
    (ρ2 : Representation K Q8 V2) [ρ2.IsIrreducible]
    (f : Representation.IntertwiningMap ρ1 ρ2) (hρ : ¬ Nonempty (ρ1.Equiv ρ2)) :
    f = 0 := by
  -- A nonzero intertwiner between irreducibles would be bijective, hence a representation
  -- equivalence, contradicting the nonisomorphism hypothesis.
  simpa using
    (Representation.IsIrreducible.bijective_or_eq_zero
      (ρ := ρ1) (σ := ρ2) f).resolve_left
      (fun hf ↦ hρ ⟨f.ofBijective hf⟩)

/-- Helper for Exercise 12-12.2-5: in characteristic zero, `Q8` admits a complete pairwise
nonisomorphic family of simple finite-dimensional `K`-representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_local :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep K Q8),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hcard_ne : (Nat.card Q8 : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card Q8 : K) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := leftRegular K Q8)
  let e :
      (Representation.directSum fun i ↦ (σ i).toRepresentation).Equiv (leftRegular K Q8) :=
    directSum_equiv_of_iSupIndep_of_iSup_eq_top (ρ := leftRegular K Q8) σ hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty ((σ i).toRepresentation.Equiv (σ j).toRepresentation)
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨f⟩
            exact ⟨f.symm⟩,
          fun {i j k} hij hjk ↦ by
            rcases hij with ⟨f⟩
            rcases hjk with ⟨g⟩
            exact ⟨f.trans g⟩⟩ }
  let ι : Type := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : Quotient r)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep K Q8 := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot label isomorphic simple summands.
    intro q q' hqq' hIso
    rcases hIso with ⟨f⟩
    have hclasses :
        (⟦Quotient.out q⟧ : Quotient r) = ⟦Quotient.out q'⟧ := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso ((forget₂ (FDRep K Q8) (Rep K Q8)).mapIso f)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : Quotient r) := (Quotient.out_eq q).symm
      _ = ⟦Quotient.out q'⟧ := hclasses
      _ = q' := Quotient.out_eq q'
  have hσ_complete :
      ∀ (τ : FDRep K Q8) [Simple τ], ∃ i : κ, Nonempty (τ ≅ FDRep.of ((σ i).toRepresentation)) := by
    intro τ _
    letI : Representation.IsIrreducible τ.ρ := FDRep.isIrreducible_of_simple τ
    have hτ_nontriv : Nontrivial τ := by
      by_contra hτ_sub
      letI : Subsingleton τ := not_nontrivial_iff_subsingleton.mp hτ_sub
      have hzero : (𝟙 τ : τ ⟶ τ) = 0 := by
        ext x
        simp
      exact CategoryTheory.id_nonzero τ hzero
    obtain ⟨v, hv⟩ := exists_ne (0 : τ)
    let f : Representation.IntertwiningMap (leftRegular K Q8) τ.ρ :=
      (Representation.leftRegularMapEquiv τ.ρ).symm v
    have hf_nonzero : f ≠ 0 := by
      intro hf
      apply hv
      have hf' := congrArg (Representation.leftRegularMapEquiv τ.ρ) hf
      simpa [f] using hf'
    let F :
        Representation.IntertwiningMap
          (Representation.directSum fun i ↦ (σ i).toRepresentation) τ.ρ :=
      intertwiningMapCongrLeft_local (K := K) e τ.ρ f
    have hF_nonzero : F ≠ 0 := by
      intro hF
      exact hf_nonzero ((intertwiningMapCongrLeft_local (K := K) e τ.ρ).injective hF)
    have hcomponent :
        ∃ i, (directSumIntertwiningMapEquivPi_local
          (K := K) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i) ≠ 0 := by
      by_contra hnone
      have hnone' := not_exists.mp hnone
      apply hF_nonzero
      apply (directSumIntertwiningMapEquivPi_local
        (K := K) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ)).injective
      ext i x
      have hi0 :
          (directSumIntertwiningMapEquivPi_local
            (K := K) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i) = 0 := by
        simpa using hnone' i
      simp [hi0]
    rcases hcomponent with ⟨i, hi⟩
    have hi_iso : Nonempty (((σ i).toRepresentation).Equiv τ.ρ) := by
      by_contra hnot
      let ρ1 := (σ i).toRepresentation
      let ρ2 := τ.ρ
      let fi : Representation.IntertwiningMap ((σ i).toRepresentation) τ.ρ :=
        directSumIntertwiningMapEquivPi_local
          (K := K) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i
      letI : Representation.IsIrreducible ((σ i).toRepresentation) := by
        exact hσ_irr i
      have hnot' : ¬ Nonempty (Representation.Equiv ((σ i).toRepresentation) τ.ρ) := hnot
      have hnot'' : ¬ Nonempty (ρ1.Equiv ρ2) := by
        simpa [ρ1, ρ2] using hnot'
      -- In the nonisomorphic case Schur's lemma forces the chosen coordinate intertwiner to vanish.
      have hfi_zero : fi = 0 := by
        let f' : ρ1.IntertwiningMap ρ2 := fi
        simpa [ρ1, ρ2, f'] using
          intertwiningMap_eq_zero_of_not_isomorphic_explicit_local
            (K := K) (V1 := ↥(σ i).toSubmodule) (V2 := ↥τ)
            (ρ1 := ρ1) (ρ2 := ρ2) (f := f') hnot''
      exact hi hfi_zero
    rcases hi_iso with ⟨eτ⟩
    -- A nonzero coordinate map between irreducibles yields the desired `FDRep` isomorphism.
    refine ⟨i, ?_⟩
    exact ⟨(fdRepIsoOfRho_local (K := K) τ).trans eτ.symm.toFDRepIso⟩
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine
      { isSimple := ?_
        exists_iso := ?_ }
    · intro q
      letI : Representation.IsIrreducible (π q).ρ := by
        simpa [π] using hσ_irr (Quotient.out q)
      exact FDRep.simple_of_isIrreducible (π q)
    · intro τ _
      obtain ⟨i, hi⟩ := hσ_complete τ
      refine ⟨(⟦i⟧ : Quotient r), ?_⟩
      have hout :
          Nonempty (((σ (Quotient.out (⟦i⟧ : Quotient r))).toRepresentation).Equiv
            ((σ i).toRepresentation)) := by
        exact Quotient.exact (Quotient.out_eq (⟦i⟧ : Quotient r))
      rcases hout with ⟨hout⟩
      rcases hi with ⟨hi⟩
      simpa [π] using ⟨hi.trans hout.toFDRepIso.symm⟩
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Exercise 12-12.2-5: if the quaternionic class function already lies in `R[K](Q8)`,
then it is the character of an honest irreducible `K`-representation. -/
private theorem quaternionGroupTwoQuaternionCharacterOver_fdRep_of_mem_characterRing
    (hpsi_mem : quaternionGroupTwoQuaternionCharacterOver (K := K) ∈ R[K](Q8)) :
    ∃ τ : FDRep K Q8, τ.character = quaternionGroupTwoQuaternionCharacterOver (K := K) := by
  classical
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  obtain ⟨ι, hι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (K := K)
  letI : Fintype ι := hι
  let x : R[K](Q8) := ⟨quaternionGroupTwoQuaternionCharacterOver (K := K), hpsi_mem⟩
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx :
      ∑ j, c j • (π j).character = (x : Q8 → K) := by
    -- Expand the character-ring element `x` in the irreducible-character basis.
    simpa [b, c, x, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R[K](Q8) ↦ (z : Q8 → K)) (b.sum_repr x)
  have hdiag_data (i : ι) :
      ∃ n : ℕ, 0 < n ∧ ⟪(π i).character, (π i).character⟫ = (n : K) := by
    letI : Simple (π i) := hπ_complete.isSimple i
    -- Each irreducible basis character has positive integral self-pairing.
    exact self_pairing_character_eq_natCast_pos_local (K := K) (V := π i)
  choose n hn_pos hdiag using hdiag_data
  have hpair : ⟪(x : Q8 → K), (x : Q8 → K)⟫ = (1 : K) := by
    -- The explicit quaternionic character has self-pairing `1`.
    simpa [x] using quaternionGroupTwoQuaternionCharacterOver_self_pairing (K := K)
  have hsum :
      ∑ i, (c i)^2 * (n i : ℤ) = 1 := by
    -- Pairing the basis expansion of `x` with itself yields LinearRepresentations_Serre_1977's weighted square-sum identity.
    simpa [b, c, x] using
      repr_weighted_square_sum_eq_one_of_self_pairing_eq_one
        (K := K) (π := π) hπ_pairwise hπ_complete x n hdiag hpair
  obtain ⟨i0, hi_sign, _hi_weight, hzero⟩ :=
    weighted_integer_coefficients_eq_singleton_of_sq_mul_sum_eq_one
      (c := c) (n := n) hn_pos hsum
  have hx_single :
      (x : Q8 → K) = c i0 • (π i0).character := by
    -- The weighted-singleton identity kills every basis coefficient except one.
    calc
      (x : Q8 → K) = ∑ j, c j • (π j).character := by simpa using hx.symm
      _ = c i0 • (π i0).character := by
            refine Finset.sum_eq_single i0 ?_ ?_
            · intro j _ hji
              simp [hzero j hji]
            · intro hi
              exact (hi (Finset.mem_univ i0)).elim
  rcases hi_sign with hci | hci
  · -- Coefficient `+1` gives an honest irreducible model of `ψ`.
    refine ⟨π i0, ?_⟩
    ext g
    simpa [x, hci] using (congrFun hx_single g).symm
  · -- Coefficient `-1` is impossible because evaluating at `1` would force a positive dimension
    -- to be negative.
    have hneg :
        (2 : K) = -((Module.finrank K (π i0)) : K) := by
      simpa [x, hci, quaternionGroupTwoQuaternionCharacterOver, Representation.char_one] using
        congrFun hx_single (1 : Q8)
    have hadd :
        (2 : K) + ((Module.finrank K (π i0)) : K) = 0 := by
      calc
        (2 : K) + ((Module.finrank K (π i0)) : K)
            = -((Module.finrank K (π i0)) : K) + ((Module.finrank K (π i0)) : K) := by
                rw [hneg]
        _ = 0 := by ring
    have hnat_zero :
        (((2 + Module.finrank K (π i0) : ℕ) : K)) = 0 := by
      simpa using hadd
    have hnat_pos : 0 < 2 + Module.finrank K (π i0) := by
      positivity
    have hnat_ne :
        (((2 + Module.finrank K (π i0) : ℕ) : K)) ≠ 0 :=
      Nat.cast_ne_zero.mpr hnat_pos.ne'
    exact False.elim (hnat_ne hnat_zero)

-- Proof sketch: LinearRepresentations_Serre_1977's source route reduces the forward implication to one descent statement for
-- the nonlinear character `ψ`: once `ψ ∈ R[K](Q8)` yields an honest `K`-model, the endgame is
-- already packaged by `quaternionGroupTwo_groupAlgebra_forward_of_realizableQuaternionCharacter`.
/-- Helper for Exercise 12-12.2-5: the forward implication of quasisplitness reduces to descending
the nonlinear quaternionic slot from character-ring membership to an honest `K`-representation. -/
theorem quaternionGroupTwo_groupAlgebra_forward_of_quasisplit
    (hquasi : IsQuasisplitGroupAlgebra K Q8) :
    Nonempty (K ⊗[ℚ] ℍ[ℚ] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hpsi_mem :
      quaternionGroupTwoQuaternionCharacterOver (K := K) ∈ R[K](Q8) :=
    quaternionGroupTwoQuaternionCharacterOver_mem_characterRing_of_isQuasisplit
      (K := K) hquasi
  -- TODO: produce an honest `K`-representation with character `ψ` from `hpsi_mem`.
  -- The stabilized endgame is already closed below: once this descent is available, the existing
  -- quaternionic criterion gives `-1 = a² + b²`, and the tensor quaternion factor splits.
  have hreal :
      ∃ τ : FDRep K Q8,
        τ.character = quaternionGroupTwoQuaternionCharacterOver (K := K) := by
    -- Route correction: instead of descending through an algebraic closure, decompose `ψ`
    -- inside the honest character ring and use the invariant `⟪ψ, ψ⟫ = 1` to isolate one
    -- irreducible basis vector.
    exact quaternionGroupTwoQuaternionCharacterOver_fdRep_of_mem_characterRing
      (K := K) hpsi_mem
  exact quaternionGroupTwo_groupAlgebra_forward_of_realizableQuaternionCharacter
    (K := K) hreal

-- Proof sketch: among the simple factors of `ℚ[Q8]`, the four linear components are already
-- split over any field of characteristic zero; thus quasisplitness is equivalent to the
-- quaternionic factor becoming a matrix algebra after scalar extension to `K`.
/-- Exercise 12-12.2-5 (4): the group algebra `K[Q8]` is quasisplit exactly when the rational
quaternion algebra `ℍ[ℚ]` splits after extending scalars from `ℚ` to `K`. -/
theorem quaternionGroupTwo_groupAlgebra_isQuasisplit_iff_tensorQuaternion_split :
    IsQuasisplitGroupAlgebra K Q8 ↔
      Nonempty (K ⊗[ℚ] ℍ[ℚ] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) := by
  constructor
  · intro hquasi
    -- Route correction: isolate the only remaining source-faithful blocker in a dedicated
    -- forward helper, and keep the endgame flat in the main theorem.
    exact quaternionGroupTwo_groupAlgebra_forward_of_quasisplit (K := K) hquasi
  · intro hsplit
    letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
    -- Route correction: the tensor-splitting hypothesis already produces the nonlinear slot over
    -- `K`; the only remaining blocker is the complete-family packaging with the four linear slots.
    have hsum : ∃ a b : K, -(1 : K) = a ^ 2 + b ^ 2 :=
      neg_one_sum_two_squares_of_tensorQuaternion_split (K := K) hsplit
    have hpsi_fd :
        ∃ τ : FDRep K Q8,
          τ.character = quaternionGroupTwoQuaternionCharacterOver (K := K) :=
      quaternionGroupTwoQuaternionCharacterOver_fdRep_of_neg_one_sum_two_squares
        (K := K) hsum
    rcases hsum with ⟨a, b, hab⟩
    let aL : AlgebraicClosure K := algebraMap K (AlgebraicClosure K) a
    let bL : AlgebraicClosure K := algebraMap K (AlgebraicClosure K) b
    have habL :
        -(1 : AlgebraicClosure K) = aL ^ 2 + bL ^ 2 := by
      -- The witness for `-1 = a² + b²` survives coefficient extension.
      dsimp [aL, bL]
      simpa [map_add, map_neg, map_one, map_pow] using
        congrArg (algebraMap K (AlgebraicClosure K)) hab
    let π : Fin 5 → FDRep (AlgebraicClosure K) Q8 := fun i =>
      match i with
      | ⟨0, _⟩ => quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 0
      | ⟨1, _⟩ => quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 1
      | ⟨2, _⟩ => quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 2
      | ⟨3, _⟩ => quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 3
      | ⟨4, _⟩ =>
          FDRep.of
            (quaternionGroupTwoSplitRepresentation (K := AlgebraicClosure K) aL bL habL)
    have hsimple : ∀ i, CategoryTheory.Simple (π i) := by
      intro i
      fin_cases i
      · simpa [π] using
          quaternionGroupTwoLinearRepresentation_simple (K := AlgebraicClosure K) 0
      · simpa [π] using
          quaternionGroupTwoLinearRepresentation_simple (K := AlgebraicClosure K) 1
      · simpa [π] using
          quaternionGroupTwoLinearRepresentation_simple (K := AlgebraicClosure K) 2
      · simpa [π] using
          quaternionGroupTwoLinearRepresentation_simple (K := AlgebraicClosure K) 3
      · simpa [π] using
          quaternionGroupTwoSplitRepresentation_simple
            (K := AlgebraicClosure K) aL bL habL
    have hpairwise : CategoryTheory.PairwiseNonisomorphic π := by
      intro i j hij hij_iso
      fin_cases i <;> fin_cases j <;> try contradiction
      · simpa [π] using
          (quaternionGroupTwoLinearRepresentation_pairwise (K := AlgebraicClosure K)
            (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
            ⟨by simpa [π] using hij_iso.some⟩)
      · simpa [π] using
          (quaternionGroupTwoLinearRepresentation_pairwise (K := AlgebraicClosure K)
            (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
            ⟨by simpa [π] using hij_iso.some⟩)
      · simpa [π] using
          (quaternionGroupTwoLinearRepresentation_pairwise (K := AlgebraicClosure K)
            (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
            ⟨by simpa [π] using hij_iso.some⟩)
      · rcases hij_iso with ⟨e⟩
        have hchar :
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 0).character =
              quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
          calc
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 0).character
                = (π 0).character := by rfl
            _ = (π 4).character := FDRep.char_iso e
            _ = quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
                  ext s
                  simpa [π] using
                    quaternionGroupTwoSplitRepresentation_character_apply
                      (K := AlgebraicClosure K) aL bL habL s
        exact
          quaternionGroupTwoQuaternionCharacterOver_ne_linear_character
            (K := AlgebraicClosure K) 0 hchar.symm
      · simpa [π] using
          (quaternionGroupTwoLinearRepresentation_pairwise (K := AlgebraicClosure K)
            (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide)
            ⟨by simpa [π] using hij_iso.some⟩)
      · simpa [π] using
          (quaternionGroupTwoLinearRepresentation_pairwise (K := AlgebraicClosure K)
            (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide)
            ⟨by simpa [π] using hij_iso.some⟩)
      · simpa [π] using
          (quaternionGroupTwoLinearRepresentation_pairwise (K := AlgebraicClosure K)
            (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
            ⟨by simpa [π] using hij_iso.some⟩)
      · rcases hij_iso with ⟨e⟩
        have hchar :
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 1).character =
              quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
          calc
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 1).character
                = (π 1).character := by rfl
            _ = (π 4).character := FDRep.char_iso e
            _ = quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
                  ext s
                  simpa [π] using
                    quaternionGroupTwoSplitRepresentation_character_apply
                      (K := AlgebraicClosure K) aL bL habL s
        exact
          quaternionGroupTwoQuaternionCharacterOver_ne_linear_character
            (K := AlgebraicClosure K) 1 hchar.symm
      · simpa [π] using
          (quaternionGroupTwoLinearRepresentation_pairwise (K := AlgebraicClosure K)
            (i := (2 : Fin 4)) (j := (0 : Fin 4)) (by decide)
            ⟨by simpa [π] using hij_iso.some⟩)
      · simpa [π] using
          (quaternionGroupTwoLinearRepresentation_pairwise (K := AlgebraicClosure K)
            (i := (2 : Fin 4)) (j := (1 : Fin 4)) (by decide)
            ⟨by simpa [π] using hij_iso.some⟩)
      · simpa [π] using
          (quaternionGroupTwoLinearRepresentation_pairwise (K := AlgebraicClosure K)
            (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
            ⟨by simpa [π] using hij_iso.some⟩)
      · rcases hij_iso with ⟨e⟩
        have hchar :
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 2).character =
              quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
          calc
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 2).character
                = (π 2).character := by rfl
            _ = (π 4).character := FDRep.char_iso e
            _ = quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
                  ext s
                  simpa [π] using
                    quaternionGroupTwoSplitRepresentation_character_apply
                      (K := AlgebraicClosure K) aL bL habL s
        exact
          quaternionGroupTwoQuaternionCharacterOver_ne_linear_character
            (K := AlgebraicClosure K) 2 hchar.symm
      · simpa [π] using
          (quaternionGroupTwoLinearRepresentation_pairwise (K := AlgebraicClosure K)
            (i := (3 : Fin 4)) (j := (0 : Fin 4)) (by decide)
            ⟨by simpa [π] using hij_iso.some⟩)
      · simpa [π] using
          (quaternionGroupTwoLinearRepresentation_pairwise (K := AlgebraicClosure K)
            (i := (3 : Fin 4)) (j := (1 : Fin 4)) (by decide)
            ⟨by simpa [π] using hij_iso.some⟩)
      · simpa [π] using
          (quaternionGroupTwoLinearRepresentation_pairwise (K := AlgebraicClosure K)
            (i := (3 : Fin 4)) (j := (2 : Fin 4)) (by decide)
            ⟨by simpa [π] using hij_iso.some⟩)
      · rcases hij_iso with ⟨e⟩
        have hchar :
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 3).character =
              quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
          calc
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 3).character
                = (π 3).character := by rfl
            _ = (π 4).character := FDRep.char_iso e
            _ = quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
                  ext s
                  simpa [π] using
                    quaternionGroupTwoSplitRepresentation_character_apply
                      (K := AlgebraicClosure K) aL bL habL s
        exact
          quaternionGroupTwoQuaternionCharacterOver_ne_linear_character
            (K := AlgebraicClosure K) 3 hchar.symm
      · rcases hij_iso with ⟨e⟩
        have hchar :
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 0).character =
              quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
          calc
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 0).character
                = (π 0).character := by rfl
            _ = (π 4).character := FDRep.char_iso e.symm
            _ = quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
                  ext s
                  simpa [π] using
                    quaternionGroupTwoSplitRepresentation_character_apply
                      (K := AlgebraicClosure K) aL bL habL s
        exact
          quaternionGroupTwoQuaternionCharacterOver_ne_linear_character
            (K := AlgebraicClosure K) 0 hchar.symm
      · rcases hij_iso with ⟨e⟩
        have hchar :
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 1).character =
              quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
          calc
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 1).character
                = (π 1).character := by rfl
            _ = (π 4).character := FDRep.char_iso e.symm
            _ = quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
                  ext s
                  simpa [π] using
                    quaternionGroupTwoSplitRepresentation_character_apply
                      (K := AlgebraicClosure K) aL bL habL s
        exact
          quaternionGroupTwoQuaternionCharacterOver_ne_linear_character
            (K := AlgebraicClosure K) 1 hchar.symm
      · rcases hij_iso with ⟨e⟩
        have hchar :
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 2).character =
              quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
          calc
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 2).character
                = (π 2).character := by rfl
            _ = (π 4).character := FDRep.char_iso e.symm
            _ = quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
                  ext s
                  simpa [π] using
                    quaternionGroupTwoSplitRepresentation_character_apply
                      (K := AlgebraicClosure K) aL bL habL s
        exact
          quaternionGroupTwoQuaternionCharacterOver_ne_linear_character
            (K := AlgebraicClosure K) 2 hchar.symm
      · rcases hij_iso with ⟨e⟩
        have hchar :
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 3).character =
              quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
          calc
            (quaternionGroupTwoLinearRepresentation (K := AlgebraicClosure K) 3).character
                = (π 3).character := by rfl
            _ = (π 4).character := FDRep.char_iso e.symm
            _ = quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) := by
                  ext s
                  simpa [π] using
                    quaternionGroupTwoSplitRepresentation_character_apply
                      (K := AlgebraicClosure K) aL bL habL s
        exact
          quaternionGroupTwoQuaternionCharacterOver_ne_linear_character
            (K := AlgebraicClosure K) 3 hchar.symm
    have hcomplete : IsCompleteIrreducibleFamily π := by
      letI : NeZero (Nat.card Q8 : AlgebraicClosure K) :=
        ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
      refine
        Representation.isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card
          (π := π) hsimple hpairwise ?_
      rw [show Nat.card Q8 = 8 by
        simpa using (QuaternionGroup.card (n := 2))]
      have hdeg :
          ∀ i : Fin 5, Module.finrank (AlgebraicClosure K) (π i).V ^ 2 =
            (match i with
            | 0 => 1
            | 1 => 1
            | 2 => 1
            | 3 => 1
            | 4 => 2) ^ 2 := by
        intro i
        fin_cases i
        · change Module.finrank (AlgebraicClosure K) (AlgebraicClosure K) ^ 2 = 1 ^ 2
          simp
        · change Module.finrank (AlgebraicClosure K) (AlgebraicClosure K) ^ 2 = 1 ^ 2
          simp
        · change Module.finrank (AlgebraicClosure K) (AlgebraicClosure K) ^ 2 = 1 ^ 2
          simp
        · change Module.finrank (AlgebraicClosure K) (AlgebraicClosure K) ^ 2 = 1 ^ 2
          simp
        · change Module.finrank (AlgebraicClosure K) (Fin 2 → AlgebraicClosure K) ^ 2 = 2 ^ 2
          simp
      simp_rw [hdeg]
      have huniv :
          (@Finset.univ (Fin 5) instFintype_serre) = (@Finset.univ (Fin 5) (Fin.fintype 5)) := by
        ext x
        simp
      rw [huniv]
      decide
    have hslot_mem :
        ∀ i, (π i).character ∈
          characterRingOverFieldInExtension K (AlgebraicClosure K) Q8 := by
      intro i
      fin_cases i
      · refine Subalgebra.mem_map.mpr ?_
        refine
          ⟨(quaternionGroupTwoLinearRepresentation (K := K) 0).character,
            ?_, ?_⟩
        · simpa using Representation.rep_character_mem_characterRingOverField
            (K := K) (G := Q8) (ρ := Rep.of (quaternionGroupTwoLinearRepresentation (K := K) 0).ρ)
        · ext g
          simp [π, quaternionGroupTwoLinearRepresentation_character_apply]
      · refine Subalgebra.mem_map.mpr ?_
        refine
          ⟨(quaternionGroupTwoLinearRepresentation (K := K) 1).character,
            ?_, ?_⟩
        · simpa using Representation.rep_character_mem_characterRingOverField
            (K := K) (G := Q8) (ρ := Rep.of (quaternionGroupTwoLinearRepresentation (K := K) 1).ρ)
        · ext g
          simp [π, quaternionGroupTwoLinearRepresentation_character_apply]
      · refine Subalgebra.mem_map.mpr ?_
        refine
          ⟨(quaternionGroupTwoLinearRepresentation (K := K) 2).character,
            ?_, ?_⟩
        · simpa using Representation.rep_character_mem_characterRingOverField
            (K := K) (G := Q8) (ρ := Rep.of (quaternionGroupTwoLinearRepresentation (K := K) 2).ρ)
        · ext g
          simp [π, quaternionGroupTwoLinearRepresentation_character_apply]
      · refine Subalgebra.mem_map.mpr ?_
        refine
          ⟨(quaternionGroupTwoLinearRepresentation (K := K) 3).character,
            ?_, ?_⟩
        · simpa using Representation.rep_character_mem_characterRingOverField
            (K := K) (G := Q8) (ρ := Rep.of (quaternionGroupTwoLinearRepresentation (K := K) 3).ρ)
        · ext g
          simp [π, quaternionGroupTwoLinearRepresentation_character_apply]
      · rcases hpsi_fd with ⟨τ, hτchar⟩
        refine Subalgebra.mem_map.mpr ?_
        refine ⟨τ.character, ?_, ?_⟩
        · simpa using Representation.rep_character_mem_characterRingOverField
            (K := K) (G := Q8) (ρ := Rep.of τ.ρ)
        · ext g
          calc
            algebraMap K (AlgebraicClosure K) (τ.character g) =
                algebraMap K (AlgebraicClosure K)
                  (quaternionGroupTwoQuaternionCharacterOver (K := K) g) := by
                    rw [hτchar]
            _ =
                quaternionGroupTwoQuaternionCharacterOver (K := AlgebraicClosure K) g := by
                    simpa using
                      congrFun
                        (quaternionGroupTwoQuaternionCharacterOver_scalarExtension (K := K)) g
            _ = (π 4).character g := by
                  simpa [π] using
                    (quaternionGroupTwoSplitRepresentation_character_apply
                      (K := AlgebraicClosure K) aL bL habL g).symm
    have hoverline_le : R̄[K](Q8) ≤ R[K](Q8) := by
      intro χ hχ
      have hχL :
          ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft Q8) χ ∈
            R[AlgebraicClosure K](Q8) := by
        -- Move the source-facing owner element into the algebraic-closure character ring.
        exact (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χ).1 hχ
      let x : R[AlgebraicClosure K](Q8) :=
        ⟨((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft Q8) χ, hχL⟩
      let b :=
        irreducible_characters_basis_of_complete_family
          (AlgebraicClosure K) π hpairwise hcomplete
      let c := b.repr x
      have hx :
          ∑ i, c i • ((b i : R[AlgebraicClosure K](Q8)) : Q8 → AlgebraicClosure K) =
            ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft Q8) χ := by
        -- Expand the algebraic-closure character in the explicit five-slot basis.
        simpa [b, c, x] using
          congrArg
            (fun z : R[AlgebraicClosure K](Q8) ↦ (z : Q8 → AlgebraicClosure K))
            (b.sum_repr x)
      have hχL_mem :
          ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft Q8) χ ∈
            characterRingOverFieldInExtension K (AlgebraicClosure K) Q8 := by
        rw [← hx]
        change
          ∑ i, c i • ((b i : R[AlgebraicClosure K](Q8)) : Q8 → AlgebraicClosure K) ∈
            (characterRingOverFieldInExtension K (AlgebraicClosure K) Q8).toSubmodule
        refine Submodule.sum_mem _ ?_
        intro i _
        have hb_char :
            ((b i : R[AlgebraicClosure K](Q8)) : Q8 → AlgebraicClosure K) = (π i).character := by
          -- The basis vectors are the ordinary irreducible characters of the five slots.
          simpa [b] using
            congrArg
              (fun z : R[AlgebraicClosure K](Q8) ↦ (z : Q8 → AlgebraicClosure K))
              (irreducible_characters_basis_of_complete_family_apply
                (K := AlgebraicClosure K) (π := π) hpairwise hcomplete i)
        exact Submodule.smul_mem _ _ (by simpa [hb_char] using hslot_mem i)
      -- Pull the algebraic-closure extension witness back to the source character ring.
      rcases Subalgebra.mem_map.mp hχL_mem with ⟨χK, hχK, hχK_eq⟩
      have hχ_eq : χK = χ := by
        ext g
        exact (algebraMap K (AlgebraicClosure K)).injective (congrFun hχK_eq g)
      simpa [hχ_eq] using hχK
    have hEq : R[K](Q8) = R̄[K](Q8) := by
      exact le_antisymm
        (characterRingOverField_le_overlineCharacterRing K Q8)
        hoverline_le
    exact
      (characterRing_eq_overlineCharacterRing_iff_isQuasisplitGroupAlgebra
        (K := K) (G := Q8)).1 hEq

-- Proof sketch: a quaternion algebra over a field splits if and only if its defining parameter
-- `-1` is represented by the norm form `x^2 + y^2`; for `ℍ[ℚ]`, this is exactly the condition
-- that `-1` be a sum of two squares in `K`.
/-- Exercise 12-12.2-5 (5): the scalar extension of the rational quaternion algebra to `K`
splits if and only if `-1` is a sum of two squares in `K`. -/
theorem tensorQuaternion_split_iff_neg_one_sum_two_squares :
    Nonempty (K ⊗[ℚ] ℍ[ℚ] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) ↔
      ∃ a b : K, -(1 : K) = a ^ 2 + b ^ 2 :=
  by
    constructor
    · intro hsplit
      -- Reuse the tensor/base-change helper proved just above the owner-level theorem.
      exact neg_one_sum_two_squares_of_tensorQuaternion_split (K := K) hsplit
    · intro hsum
      -- The converse is the explicit split-model construction transported across base change.
      exact tensorQuaternion_split_of_neg_one_sum_two_squares (K := K) hsum

end

end

end Representation
