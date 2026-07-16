import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_6_3.DirectSL2F4
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_6_3.Shared
import LinearRepresentations_Serre_1977.Serre.Chap08.Proposition_8_8_3_7

open scoped MatrixGroups

noncomputable section

universe u

namespace Representation

local notation "A5" => alternatingGroup (Fin 5)
local notation "𝔽₄" => FiniteField.Extension (ZMod 2) 2 2

/-- Helper for Exercise 18-18.6-3: the finite field `𝔽₄` has four elements. -/
private theorem f4_card_eq_four :
    Nat.card 𝔽₄ = 4 := by
  -- This is the standard cardinality formula for a degree-two extension of `𝔽₂`.
  simpa using (FiniteField.natCard_extension (k := ZMod 2) (p := 2) (n := 2))

/-- Helper for Exercise 18-18.6-3: every element of `𝔽₄` is fixed by the fourth-power map. -/
private theorem f4_pow_four_eq_self (a : 𝔽₄) :
    a ^ 4 = a := by
  -- Finite fields satisfy `x ^ |𝔽₄| = x`; substitute the computed cardinality.
  letI : Fintype 𝔽₄ := Fintype.ofFinite 𝔽₄
  have hcard : Fintype.card 𝔽₄ = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact f4_card_eq_four
  simpa only [hcard] using (FiniteField.pow_card a)

/-- Helper for Exercise 18-18.6-3: every nonzero element of `𝔽₄` is the square of a unit. -/
theorem f4_exists_unit_sq_eq {a : 𝔽₄} (ha : a ≠ 0) :
    ∃ r : 𝔽₄ˣ, (r : 𝔽₄) ^ 2 = a := by
  -- The inverse Frobenius square is `a ↦ a²`, since `(a²)² = a⁴ = a`.
  refine ⟨Units.mk0 (a ^ 2) (pow_ne_zero 2 ha), ?_⟩
  exact calc
    ((Units.mk0 (a ^ 2) (pow_ne_zero 2 ha) : 𝔽₄ˣ) : 𝔽₄) ^ 2 = (a ^ 2) ^ 2 := by
      simp only [Units.val_mk0]
    _ = a ^ 4 := by ring
    _ = a := f4_pow_four_eq_self a

/-- Helper for Exercise 18-18.6-3: the field `𝔽₄` has characteristic `2`. -/
private theorem f4_two_eq_zero : (2 : 𝔽₄) = 0 := by
  -- Push the numeral through the structure map from `ZMod 2`.
  calc
    (2 : 𝔽₄) = algebraMap (ZMod 2) 𝔽₄ (2 : ZMod 2) :=
      (map_natCast (algebraMap (ZMod 2) 𝔽₄) 2).symm
    _ = algebraMap (ZMod 2) 𝔽₄ 0 := by
      have h : (2 : ZMod 2) = 0 := by decide
      rw [h]
    _ = 0 := map_zero _

/-- Helper for Exercise 18-18.6-3: in `𝔽₄`, adding `1` to itself gives zero. -/
private theorem f4_one_add_one_eq_zero : (1 : 𝔽₄) + 1 = 0 := by
  -- This is the entrywise form of characteristic `2` used in the elementary matrix products.
  calc
    (1 : 𝔽₄) + 1 = 2 := by norm_num
    _ = 0 := f4_two_eq_zero

/-- Helper for Exercise 18-18.6-3: in `𝔽₄`, the two signs of `1` coincide. -/
private theorem f4_neg_one_eq_one : (-1 : 𝔽₄) = 1 := by
  -- Characteristic `2` turns `-1 - 1` into zero.
  rw [← sub_eq_zero]
  calc
    (-1 : 𝔽₄) - 1 = -(2 : 𝔽₄) := by ring
    _ = 0 := by rw [f4_two_eq_zero, neg_zero]

/-- Helper for Exercise 18-18.6-3: determinant-one condition for an upper unipotent matrix. -/
theorem sl2F4Upper_det (a : 𝔽₄) :
    (!![(1 : 𝔽₄), a; 0, 1] : Matrix (Fin 2) (Fin 2) 𝔽₄).det = 1 := by
  -- The determinant is the product of the diagonal entries.
  simp [Matrix.det_fin_two_of]

/-- Helper for Exercise 18-18.6-3: the upper unipotent element of `SL(2, 𝔽₄)`. -/
def sl2F4Upper (a : 𝔽₄) : SL(2, 𝔽₄) :=
  ⟨!![(1 : 𝔽₄), a; 0, 1], sl2F4Upper_det a⟩

/-- Helper for Exercise 18-18.6-3: the zero upper unipotent is the identity. -/
theorem sl2F4Upper_zero : sl2F4Upper 0 = 1 := by
  -- Compare the four matrix entries.
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sl2F4Upper]

/-- Helper for Exercise 18-18.6-3: upper unipotents multiply by adding their parameters. -/
theorem sl2F4Upper_mul (a b : 𝔽₄) :
    sl2F4Upper (a + b) = sl2F4Upper a * sl2F4Upper b := by
  -- Matrix multiplication leaves only the upper-right additive parameter.
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2F4Upper, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, add_comm]

/-- Helper for Exercise 18-18.6-3: the upper unipotent parameter is recoverable from the matrix. -/
theorem sl2F4Upper_injective : Function.Injective sl2F4Upper := by
  intro a b h
  -- Read off the upper-right entry.
  have h01 :=
    congrArg (fun g : SL(2, 𝔽₄) => (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 0 1) h
  simpa [sl2F4Upper] using h01

/-- Helper for Exercise 18-18.6-3: determinant-one condition for a lower unipotent matrix. -/
theorem sl2F4Lower_det (a : 𝔽₄) :
    (!![(1 : 𝔽₄), 0; a, 1] : Matrix (Fin 2) (Fin 2) 𝔽₄).det = 1 := by
  -- The determinant is the product of the diagonal entries.
  simp [Matrix.det_fin_two_of]

/-- Helper for Exercise 18-18.6-3: the lower unipotent element of `SL(2, 𝔽₄)`. -/
def sl2F4Lower (a : 𝔽₄) : SL(2, 𝔽₄) :=
  ⟨!![(1 : 𝔽₄), 0; a, 1], sl2F4Lower_det a⟩

/-- Helper for Exercise 18-18.6-3: lower unipotents multiply by adding their parameters. -/
theorem sl2F4Lower_mul (a b : 𝔽₄) :
    sl2F4Lower (a + b) = sl2F4Lower a * sl2F4Lower b := by
  -- Matrix multiplication leaves only the lower-left additive parameter.
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2F4Lower, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, add_comm]

/-- Helper for Exercise 18-18.6-3: the lower unipotent parameter is recoverable from the matrix. -/
theorem sl2F4Lower_injective : Function.Injective sl2F4Lower := by
  intro a b h
  -- Read off the lower-left entry.
  have h10 :=
    congrArg (fun g : SL(2, 𝔽₄) => (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 1 0) h
  simpa [sl2F4Lower] using h10

/-- Helper for Exercise 18-18.6-3: determinant-one condition for the diagonal torus element. -/
theorem sl2F4Diag_det (r : 𝔽₄ˣ) :
    (!![(r : 𝔽₄), 0; 0, ((r⁻¹ : 𝔽₄ˣ) : 𝔽₄)] :
      Matrix (Fin 2) (Fin 2) 𝔽₄).det = 1 := by
  -- The determinant is `r * r⁻¹`.
  simp [Matrix.det_fin_two_of]

/-- Helper for Exercise 18-18.6-3: the diagonal torus element `diag(r,r⁻¹)`. -/
def sl2F4Diag (r : 𝔽₄ˣ) : SL(2, 𝔽₄) :=
  ⟨!![(r : 𝔽₄), 0; 0, ((r⁻¹ : 𝔽₄ˣ) : 𝔽₄)], sl2F4Diag_det r⟩

/-- Helper for Exercise 18-18.6-3: diagonal torus elements multiply as expected. -/
theorem sl2F4Diag_mul (r s : 𝔽₄ˣ) :
    sl2F4Diag (r * s) = sl2F4Diag r * sl2F4Diag s := by
  -- Compare the diagonal entries after matrix multiplication.
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2F4Diag, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, mul_comm]

/-- Helper for Exercise 18-18.6-3: the inverse diagonal torus element has inverse parameter. -/
theorem sl2F4Diag_inv (r : 𝔽₄ˣ) :
    (sl2F4Diag r)⁻¹ = sl2F4Diag r⁻¹ := by
  -- Multiplying the two displayed diagonal matrices gives the identity.
  rw [inv_eq_iff_mul_eq_one]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2F4Diag, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]

/-- Helper for Exercise 18-18.6-3: the torus conjugates upper unipotents by `a ↦ r²a`. -/
theorem sl2F4Diag_conj_upper (r : 𝔽₄ˣ) (a : 𝔽₄) :
    sl2F4Diag r * sl2F4Upper a * (sl2F4Diag r)⁻¹ =
      sl2F4Upper ((r : 𝔽₄) ^ 2 * a) := by
  -- Normalize the inverse diagonal and compare the four matrix entries.
  rw [sl2F4Diag_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2F4Diag, sl2F4Upper, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, pow_two, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 18-18.6-3: inverse-free form of the torus action on upper unipotents. -/
theorem sl2F4Diag_mul_upper (r : 𝔽₄ˣ) (a : 𝔽₄) :
    sl2F4Diag r * sl2F4Upper a =
      sl2F4Upper ((r : 𝔽₄) ^ 2 * a) * sl2F4Diag r := by
  -- This is the same diagonal-conjugation calculation, arranged for comparing coordinate
  -- matrices without introducing the matrix of an inverse.
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2F4Diag, sl2F4Upper, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, pow_two, mul_assoc, mul_comm]

/-- Helper for Exercise 18-18.6-3: determinant-one condition for the Weyl element. -/
theorem sl2F4Weyl_det :
    (!![(0 : 𝔽₄), 1; 1, 0] : Matrix (Fin 2) (Fin 2) 𝔽₄).det = 1 := by
  -- In characteristic `2`, the determinant `-1` is equal to `1`.
  rw [Matrix.det_fin_two_of]
  simp [f4_neg_one_eq_one]

/-- Helper for Exercise 18-18.6-3: the Weyl element swapping the two basis vectors. -/
def sl2F4Weyl : SL(2, 𝔽₄) :=
  ⟨!![(0 : 𝔽₄), 1; 1, 0], sl2F4Weyl_det⟩

/-- Helper for Exercise 18-18.6-3: the Weyl element is an involution. -/
theorem sl2F4Weyl_sq : sl2F4Weyl * sl2F4Weyl = 1 := by
  -- Squaring the swap matrix gives the identity.
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2F4Weyl, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]

/-- Helper for Exercise 18-18.6-3: the Weyl element is its own inverse. -/
theorem sl2F4Weyl_inv : (sl2F4Weyl)⁻¹ = sl2F4Weyl := by
  -- The involution identity is exactly the inverse characterization.
  rw [inv_eq_iff_mul_eq_one]
  exact sl2F4Weyl_sq

/-- Helper for Exercise 18-18.6-3: conjugating an upper unipotent by the Weyl element gives the
corresponding lower unipotent. -/
theorem sl2F4Weyl_conj_upper (a : 𝔽₄) :
    sl2F4Weyl * sl2F4Upper a * (sl2F4Weyl)⁻¹ = sl2F4Lower a := by
  -- Replace the inverse by the same Weyl matrix and multiply explicitly.
  rw [sl2F4Weyl_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2F4Upper, sl2F4Lower, sl2F4Weyl,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]

/-- Helper for Exercise 18-18.6-3: the Weyl element is a product of elementary unipotents. -/
theorem sl2F4Weyl_eq_upper_lower_upper :
    sl2F4Weyl = sl2F4Upper 1 * sl2F4Lower 1 * sl2F4Upper 1 := by
  -- In characteristic `2`, the usual elementary product has middle diagonal entry `0`.
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i
  · fin_cases j
    · simp [sl2F4Upper, sl2F4Lower, sl2F4Weyl,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      simpa using f4_one_add_one_eq_zero.symm
    · simp [sl2F4Upper, sl2F4Lower, sl2F4Weyl,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      simpa using f4_one_add_one_eq_zero
  · fin_cases j
    · simp [sl2F4Upper, sl2F4Lower, sl2F4Weyl,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    · simp [sl2F4Upper, sl2F4Lower, sl2F4Weyl,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      simpa using f4_one_add_one_eq_zero.symm

/-- Helper for Exercise 18-18.6-3: each diagonal torus element is generated by elementary
unipotents and the Weyl element. -/
theorem sl2F4Diag_eq_upper_lower_upper_weyl (r : 𝔽₄ˣ) :
    sl2F4Diag r =
      sl2F4Upper (r : 𝔽₄) * sl2F4Lower ((r : 𝔽₄)⁻¹) *
        sl2F4Upper (r : 𝔽₄) * sl2F4Weyl := by
  -- Multiply the four displayed matrices and use `r * r⁻¹ = 1`.
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i
  · fin_cases j
    · simp [sl2F4Upper, sl2F4Lower, sl2F4Diag, sl2F4Weyl,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      simpa using f4_one_add_one_eq_zero
    · simp [sl2F4Upper, sl2F4Lower, sl2F4Diag, sl2F4Weyl,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      simpa using f4_one_add_one_eq_zero.symm
  · fin_cases j
    · simp [sl2F4Upper, sl2F4Lower, sl2F4Diag, sl2F4Weyl,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      simpa using f4_one_add_one_eq_zero.symm
    · simp [sl2F4Upper, sl2F4Lower, sl2F4Diag, sl2F4Weyl,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]

/-- Helper for Exercise 18-18.6-3: the additive upper unipotents form a monoid hom from the
additive group of `𝔽₄`, written multiplicatively. -/
theorem sl2F4UpperHom_map_one :
    sl2F4Upper (Multiplicative.toAdd (1 : Multiplicative 𝔽₄)) = 1 := by
  -- The multiplicative identity of `Multiplicative 𝔽₄` is the additive zero.
  simpa using sl2F4Upper_zero

/-- Helper for Exercise 18-18.6-3: the upper-unipotent hom respects multiplication in
`Multiplicative 𝔽₄`. -/
theorem sl2F4UpperHom_map_mul (a b : Multiplicative 𝔽₄) :
    sl2F4Upper (Multiplicative.toAdd (a * b)) =
      sl2F4Upper (Multiplicative.toAdd a) *
        sl2F4Upper (Multiplicative.toAdd b) := by
  -- Multiplication in `Multiplicative 𝔽₄` is addition in `𝔽₄`.
  simpa using sl2F4Upper_mul (Multiplicative.toAdd a) (Multiplicative.toAdd b)

/-- Helper for Exercise 18-18.6-3: the upper unipotent subgroup as the range of the additive
parameter hom. -/
def sl2F4UpperHom : Multiplicative 𝔽₄ →* SL(2, 𝔽₄) where
  toFun a := sl2F4Upper (Multiplicative.toAdd a)
  map_one' := sl2F4UpperHom_map_one
  map_mul' := sl2F4UpperHom_map_mul

/-- Helper for Exercise 18-18.6-3: the upper-unipotent hom is injective. -/
theorem sl2F4UpperHom_injective : Function.Injective sl2F4UpperHom := by
  intro a b h
  -- Injectivity follows from the displayed upper-right matrix entry.
  apply Multiplicative.toAdd.injective
  exact sl2F4Upper_injective h

/-- Helper for Exercise 18-18.6-3: the subgroup of upper unipotents in `SL(2, 𝔽₄)`. -/
abbrev sl2F4UpperSubgroup : Subgroup (SL(2, 𝔽₄)) :=
  sl2F4UpperHom.range

/-- Helper for Exercise 18-18.6-3: each displayed upper unipotent lies in the upper subgroup. -/
theorem sl2F4Upper_mem_upperSubgroup (a : 𝔽₄) :
    sl2F4Upper a ∈ sl2F4UpperSubgroup := by
  -- Use the element with additive parameter `a`.
  exact ⟨Multiplicative.ofAdd a, rfl⟩

/-- Helper for Exercise 18-18.6-3: the upper unipotent subgroup has order `4`. -/
theorem sl2F4UpperSubgroup_card :
    Nat.card sl2F4UpperSubgroup = 4 := by
  -- The parameter hom identifies the subgroup with the additive group of `𝔽₄`.
  calc
    Nat.card sl2F4UpperSubgroup = Nat.card (Multiplicative 𝔽₄) := by
      exact
        (Nat.card_congr
          (MonoidHom.ofInjective sl2F4UpperHom_injective).toEquiv).symm
    _ = Nat.card 𝔽₄ := Nat.card_congr Multiplicative.ofAdd.symm
    _ = 4 := f4_card_eq_four

/-- Helper for Exercise 18-18.6-3: the upper unipotent subgroup is a `2`-group. -/
theorem sl2F4UpperSubgroup_isPGroup :
    IsPGroup 2 sl2F4UpperSubgroup := by
  -- Its order is `4 = 2²`.
  exact IsPGroup.of_card (show Nat.card sl2F4UpperSubgroup = 2 ^ 2 by
    simpa [pow_two] using sl2F4UpperSubgroup_card)

/-- Helper for Exercise 18-18.6-3: an irreducible two-dimensional representation has a nonzero
vector fixed by every upper unipotent. -/
theorem sl2F4_upperFixedVector_exists
    {K : Type*} [Field K] [Algebra 𝔽₄ K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (σ : Representation K (SL(2, 𝔽₄)) V) [σ.IsIrreducible]
    (hV : Module.finrank K V = 2) :
    ∃ v : V, v ≠ 0 ∧ ∀ a : 𝔽₄, σ (sl2F4Upper a) v = v := by
  -- The positive finrank hypothesis supplies the nonzero module required by the p-group
  -- invariant-vector theorem.
  letI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  have hF4Char : CharP 𝔽₄ 2 := by
    rw [← Algebra.charP_iff (ZMod 2) 𝔽₄ 2]
    exact ZMod.charP 2
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap 𝔽₄ K).injective 2
  let σU : Representation K sl2F4UpperSubgroup V := σ.comp sl2F4UpperSubgroup.subtype
  have hInv_ne_bot : σU.invariants ≠ ⊥ := by
    -- The upper subgroup has order `2²`, so its invariants are nontrivial in characteristic `2`.
    exact invariants_ne_bot_of_isPGroup_charP (ρ := σU) sl2F4UpperSubgroup_isPGroup
  rcases σU.invariants.ne_bot_iff.mp hInv_ne_bot with ⟨v, hvInv, hv0⟩
  refine ⟨v, hv0, ?_⟩
  intro a
  -- Unpack invariant membership at the displayed upper unipotent element.
  have hfix :=
    (σU.mem_invariants v).1 hvInv ⟨sl2F4Upper a, sl2F4Upper_mem_upperSubgroup a⟩
  simpa [σU] using hfix

/-- Helper for Exercise 18-18.6-3: the elementary upper/lower unipotent generators of
`SL(2, 𝔽₄)`. -/
def sl2F4ElementarySet : Set (SL(2, 𝔽₄)) :=
  Set.range sl2F4Upper ∪ Set.range sl2F4Lower

/-- Helper for Exercise 18-18.6-3: the subgroup generated by the elementary upper/lower
unipotents. -/
abbrev sl2F4ElementarySubgroup : Subgroup (SL(2, 𝔽₄)) :=
  Subgroup.closure sl2F4ElementarySet

/-- Helper for Exercise 18-18.6-3: every upper unipotent is elementary. -/
theorem sl2F4Upper_mem_elementarySubgroup (a : 𝔽₄) :
    sl2F4Upper a ∈ sl2F4ElementarySubgroup := by
  -- The upper unipotents are one half of the generating set.
  exact Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)

/-- Helper for Exercise 18-18.6-3: every lower unipotent is elementary. -/
theorem sl2F4Lower_mem_elementarySubgroup (a : 𝔽₄) :
    sl2F4Lower a ∈ sl2F4ElementarySubgroup := by
  -- The lower unipotents are the other half of the generating set.
  exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)

/-- Helper for Exercise 18-18.6-3: the Weyl element belongs to the elementary subgroup. -/
theorem sl2F4Weyl_mem_elementarySubgroup :
    sl2F4Weyl ∈ sl2F4ElementarySubgroup := by
  -- Use the explicit elementary factorization of the Weyl element.
  rw [sl2F4Weyl_eq_upper_lower_upper]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (sl2F4Upper_mem_elementarySubgroup 1)
      (sl2F4Lower_mem_elementarySubgroup 1))
    (sl2F4Upper_mem_elementarySubgroup 1)

/-- Helper for Exercise 18-18.6-3: diagonal torus elements belong to the elementary subgroup. -/
theorem sl2F4Diag_mem_elementarySubgroup (r : 𝔽₄ˣ) :
    sl2F4Diag r ∈ sl2F4ElementarySubgroup := by
  -- Use the displayed elementary factorization of `diag(r,r⁻¹)`.
  rw [sl2F4Diag_eq_upper_lower_upper_weyl]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (sl2F4Upper_mem_elementarySubgroup (r : 𝔽₄))
        (sl2F4Lower_mem_elementarySubgroup ((r : 𝔽₄)⁻¹)))
      (sl2F4Upper_mem_elementarySubgroup (r : 𝔽₄)))
    sl2F4Weyl_mem_elementarySubgroup

/-- Helper for Exercise 18-18.6-3: if the top-left entry is nonzero, Gaussian elimination writes
an `SL₂` element as `lower * diagonal * upper`. -/
theorem sl2F4_eq_lower_diag_upper_of_left_ne_zero
    (g : SL(2, 𝔽₄))
    (hg00 : (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 0 0 ≠ 0) :
    g = sl2F4Lower (((g : Matrix (Fin 2) (Fin 2) 𝔽₄) 1 0) /
          ((g : Matrix (Fin 2) (Fin 2) 𝔽₄) 0 0)) *
        sl2F4Diag (Units.mk0 ((g : Matrix (Fin 2) (Fin 2) 𝔽₄) 0 0) hg00) *
        sl2F4Upper (((g : Matrix (Fin 2) (Fin 2) 𝔽₄) 0 1) /
          ((g : Matrix (Fin 2) (Fin 2) 𝔽₄) 0 0)) := by
  -- The determinant equation supplies the bottom-right entry after clearing the pivot.
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hdet :
      (g : Matrix (Fin 2) (Fin 2) 𝔽₄).det = 1 := g.2
  have hdet_entries :
      (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 0 0 *
        (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 0 1 *
        (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    exact hdet
  fin_cases i
  · fin_cases j
    · simp [sl2F4Upper, sl2F4Lower, sl2F4Diag,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    · simp [sl2F4Upper, sl2F4Lower, sl2F4Diag,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      field_simp [hg00]
  · fin_cases j
    · simp [sl2F4Upper, sl2F4Lower, sl2F4Diag,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      field_simp [hg00]
    · simp [sl2F4Upper, sl2F4Lower, sl2F4Diag,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      field_simp [hg00]
      linear_combination hdet_entries

/-- Helper for Exercise 18-18.6-3: every element of `SL(2, 𝔽₄)` lies in the elementary subgroup. -/
theorem sl2F4_mem_elementarySubgroup (g : SL(2, 𝔽₄)) :
    g ∈ sl2F4ElementarySubgroup := by
  -- Pivot on the top-left entry; if it vanishes, multiply by the Weyl element to make the pivot
  -- nonzero and then undo that multiplication inside the generated subgroup.
  by_cases hg00 : (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 0 0 ≠ 0
  · rw [sl2F4_eq_lower_diag_upper_of_left_ne_zero g hg00]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (sl2F4Lower_mem_elementarySubgroup _)
        (sl2F4Diag_mem_elementarySubgroup _))
      (sl2F4Upper_mem_elementarySubgroup _)
  · have hg00_zero : (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 0 0 = 0 := not_not.mp hg00
    have hdet :
        (g : Matrix (Fin 2) (Fin 2) 𝔽₄).det = 1 := g.2
    have hdet_entries :
        (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 0 0 *
          (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 1 1 -
        (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 0 1 *
          (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 1 0 = 1 := by
      rw [Matrix.det_fin_two] at hdet
      exact hdet
    have hg10_ne_zero : (g : Matrix (Fin 2) (Fin 2) 𝔽₄) 1 0 ≠ 0 := by
      intro hg10_zero
      have hzero : (0 : 𝔽₄) = 1 := by
        simp [hg00_zero, hg10_zero] at hdet_entries
      exact zero_ne_one hzero
    have hWg00 :
        ((sl2F4Weyl * g : SL(2, 𝔽₄)) :
          Matrix (Fin 2) (Fin 2) 𝔽₄) 0 0 ≠ 0 := by
      -- The Weyl element swaps the two rows, so the new top-left entry is the old lower-left one.
      simpa [sl2F4Weyl, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
        using hg10_ne_zero
    have hWg_mem : sl2F4Weyl * g ∈ sl2F4ElementarySubgroup := by
      rw [sl2F4_eq_lower_diag_upper_of_left_ne_zero (sl2F4Weyl * g) hWg00]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _
          (sl2F4Lower_mem_elementarySubgroup _)
          (sl2F4Diag_mem_elementarySubgroup _))
        (sl2F4Upper_mem_elementarySubgroup _)
    have hg_eq : g = sl2F4Weyl * (sl2F4Weyl * g) := by
      calc
        g = (sl2F4Weyl * sl2F4Weyl) * g := by
          rw [sl2F4Weyl_sq]
          simp
        _ = sl2F4Weyl * (sl2F4Weyl * g) := by rw [mul_assoc]
    rw [hg_eq]
    exact Subgroup.mul_mem _ sl2F4Weyl_mem_elementarySubgroup hWg_mem

/-- Helper for Exercise 18-18.6-3: upper and lower unipotents generate all of `SL(2, 𝔽₄)`. -/
theorem sl2F4Elementary_closure_eq_top :
    sl2F4ElementarySubgroup = ⊤ := by
  -- The membership theorem gives the reverse inclusion into the generated subgroup.
  ext g
  constructor
  · intro _hg
    simp
  · intro _hg
    exact sl2F4_mem_elementarySubgroup g

/-- Helper for Exercise 18-18.6-3: if a nonzero upper-fixed vector had its Weyl translate on the
same line, that line would be a proper nonzero subrepresentation, contradicting irreducibility. -/
theorem sl2F4_weylTranslate_not_mem_span
    {K : Type*} [Field K] [Algebra 𝔽₄ K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (σ : Representation K (SL(2, 𝔽₄)) V) [σ.IsIrreducible]
    {v : V} (hv0 : v ≠ 0) (hUpper : ∀ a : 𝔽₄, σ (sl2F4Upper a) v = v)
    (hV : Module.finrank K V = 2) :
    σ sl2F4Weyl v ∉ K ∙ v := by
  classical
  intro hWmem
  let L : Submodule K V := K ∙ v
  have hUpper_forward : ∀ a : 𝔽₄, ∀ x : V, x ∈ L → σ (sl2F4Upper a) x ∈ L := by
    intro a x hx
    -- Upper unipotents fix the line because they fix its generator.
    rcases Submodule.mem_span_singleton.mp (by simpa [L] using hx) with ⟨c, rfl⟩
    simpa [L, map_smul, hUpper a] using
      (Submodule.smul_mem (K ∙ v) c (Submodule.mem_span_singleton_self v))
  have hWeyl_forward : ∀ x : V, x ∈ L → σ sl2F4Weyl x ∈ L := by
    intro x hx
    -- The assumed Weyl-dependence says the Weyl element also preserves the same line.
    rcases Submodule.mem_span_singleton.mp (by simpa [L] using hx) with ⟨c, rfl⟩
    simpa [L, map_smul] using
      (Submodule.smul_mem (K ∙ v) c (by simpa [L] using hWmem))
  let H : Subgroup (SL(2, 𝔽₄)) :=
    { carrier := {g | ∀ x : V, σ g x ∈ L ↔ x ∈ L}
      one_mem' := by
        intro x
        simp
      mul_mem' := by
        intro g h hg hh x
        -- Stability is closed under composition of representation operators.
        simpa [map_mul] using (hg (σ h x)).trans (hh x)
      inv_mem' := by
        intro g hg x
        -- For an inverse, apply the equivalence for `g` to `σ g⁻¹ x`.
        have h := (hg (σ g⁻¹ x)).symm
        have hcancel : σ g (σ g⁻¹ x) = x := by
          calc
            σ g (σ g⁻¹ x) = σ (g * g⁻¹) x := by simp
            _ = x := by simp
        simpa [hcancel] using h }
  have hUpper_H : ∀ a : 𝔽₄, sl2F4Upper a ∈ H := by
    intro a x
    constructor
    · intro hx
      -- The inverse upper unipotent has parameter `-a`, so reverse stability follows from the
      -- same fixed-line calculation.
      have hx' := hUpper_forward (-a) (σ (sl2F4Upper a) x) hx
      have hcancel : σ (sl2F4Upper (-a)) (σ (sl2F4Upper a) x) = x := by
        calc
          σ (sl2F4Upper (-a)) (σ (sl2F4Upper a) x)
              = σ (sl2F4Upper (-a) * sl2F4Upper a) x := by simp [map_mul]
          _ = σ (sl2F4Upper ((-a) + a)) x := by rw [← sl2F4Upper_mul (-a) a]
          _ = x := by simp [sl2F4Upper_zero]
      simpa [hcancel] using hx'
    · intro hx
      exact hUpper_forward a x hx
  have hWeyl_H : sl2F4Weyl ∈ H := by
    intro x
    constructor
    · intro hx
      -- The Weyl element is an involution, so one-sided preservation gives reverse preservation.
      have hx' := hWeyl_forward (σ sl2F4Weyl x) hx
      have hcancel : σ sl2F4Weyl (σ sl2F4Weyl x) = x := by
        calc
          σ sl2F4Weyl (σ sl2F4Weyl x) = σ (sl2F4Weyl * sl2F4Weyl) x := by
            simp [map_mul]
          _ = x := by rw [sl2F4Weyl_sq]; simp
      simpa [hcancel] using hx'
    · intro hx
      exact hWeyl_forward x hx
  have hLower_H : ∀ a : 𝔽₄, sl2F4Lower a ∈ H := by
    intro a
    -- Lower unipotents are Weyl conjugates of upper unipotents, so they preserve the line too.
    rw [← sl2F4Weyl_conj_upper a]
    exact H.mul_mem (H.mul_mem hWeyl_H (hUpper_H a)) (H.inv_mem hWeyl_H)
  have hElementary_le_H : sl2F4ElementarySubgroup ≤ H := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact hUpper_H a
    · exact hLower_H a
  have hAll_H : ∀ g : SL(2, 𝔽₄), g ∈ H := by
    intro g
    apply hElementary_le_H
    rw [sl2F4Elementary_closure_eq_top]
    simp
  let U : Subrepresentation σ :=
    { toSubmodule := L
      apply_mem_toSubmodule := by
        intro g x hx
        exact ((show ∀ y : V, σ g y ∈ L ↔ y ∈ L from hAll_H g) x).2 hx }
  have hL_ne_bot : L ≠ ⊥ := by
    -- The fixed line is nonzero because its generator is nonzero.
    simpa [L, Submodule.span_singleton_eq_bot] using hv0
  have hL_ne_top : L ≠ ⊤ := by
    -- A one-generator span cannot fill a two-dimensional space.
    have hL_lt_top : L < ⊤ := by
      refine span_lt_top_of_card_lt_finrank (R := K) (M := V)
        (s := ({v} : Set V)) ?_
      simp [hV]
    exact hL_lt_top.ne
  have hU_ne_bot : U ≠ ⊥ := by
    intro hU
    exact hL_ne_bot (by simpa [U] using congrArg Subrepresentation.toSubmodule hU)
  have hU_ne_top : U ≠ ⊤ := by
    intro hU
    exact hL_ne_top (by simpa [U] using congrArg Subrepresentation.toSubmodule hU)
  -- Irreducibility forces every nonzero subrepresentation to be top, contradiction.
  have hU_top : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
  exact hU_ne_top hU_top

/-- Helper for Exercise 18-18.6-3: a nonzero upper-fixed vector and its Weyl translate form a
basis in which the Weyl element has the swap matrix. -/
theorem sl2F4_weylBasis_of_upperFixedVector
    {K : Type*} [Field K] [Algebra 𝔽₄ K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (σ : Representation K (SL(2, 𝔽₄)) V) [σ.IsIrreducible]
    {v : V} (hv0 : v ≠ 0) (hUpper : ∀ a : 𝔽₄, σ (sl2F4Upper a) v = v)
    (hV : Module.finrank K V = 2) :
    ∃ b : Module.Basis (Fin 2) K V,
      b 0 = v ∧ b 1 = σ sl2F4Weyl v ∧
        LinearMap.toMatrix b b (σ sl2F4Weyl) =
          !![(0 : K), 1; 1, 0] := by
  classical
  -- Package the two intended basis vectors as a `Fin 2`-family.
  let w : Fin 2 → V := fun i => if i = 0 then v else σ sl2F4Weyl v
  have hw0 : w 0 = v := by simp [w]
  have hw1 : w 1 = σ sl2F4Weyl v := by simp [w]
  have hlin : LinearIndependent K w := by
    -- The previous line-stability contradiction is exactly the second-vector condition for
    -- `linearIndependent_fin2`.
    rw [linearIndependent_fin2]
    constructor
    · simpa [hw1] using fun h =>
        sl2F4_weylTranslate_not_mem_span σ hv0 hUpper hV (by
          rw [h]
          exact Submodule.zero_mem _)
    · intro a ha
      by_cases ha0 : a = 0
      · exact hv0 (by
          rw [← hw0, ← ha, ha0, zero_smul])
      have hw1_eq_smul : w 1 = a⁻¹ • w 0 := by
        calc
          w 1 = 1 • w 1 := (one_smul K (w 1)).symm
          _ = (a⁻¹ * a) • w 1 := by rw [inv_mul_cancel₀ ha0]
          _ = a⁻¹ • (a • w 1) := by rw [mul_smul]
          _ = a⁻¹ • w 0 := by rw [ha]
      have hmem : σ sl2F4Weyl v ∈ K ∙ v := by
        rw [← hw1, hw1_eq_smul, hw0]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
      exact sl2F4_weylTranslate_not_mem_span σ hv0 hUpper hV hmem
  -- Since the family has two vectors and the representation has finrank two, it is a basis.
  let b : Module.Basis (Fin 2) K V :=
    basisOfLinearIndependentOfCardEqFinrank hlin (by simp [hV])
  have hb0 : b 0 = v := by simp [b, w]
  have hb1 : b 1 = σ sl2F4Weyl v := by simp [b, w]
  refine ⟨b, hb0, hb1, ?_⟩
  -- Read the Weyl action on the two basis vectors from `W² = 1`.
  have hW0 : σ sl2F4Weyl (b 0) = b 1 := by
    rw [hb0, hb1]
  have hW1 : σ sl2F4Weyl (b 1) = b 0 := by
    calc
      σ sl2F4Weyl (b 1) = σ sl2F4Weyl (σ sl2F4Weyl v) := by rw [hb1]
      _ = σ (sl2F4Weyl * sl2F4Weyl) v := by simp [map_mul]
      _ = b 0 := by rw [sl2F4Weyl_sq]; simp [hb0]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, hW0, hW1]

/-- Helper for Exercise 18-18.6-3: every multiplicative character of `SL(2, 𝔽₄)` is trivial. -/
theorem sl2F4_units_hom_eq_one_over_any_field {L : Type*} [Field L]
    (χ : SL(2, 𝔽₄) →* Lˣ) :
    χ = 1 := by
  -- Transport the character to `A₅`, use perfectness there, and pull the equality back.
  rcases _root_.alternatingGroup_fin5_mulEquiv_sl2_f4_direct with ⟨e⟩
  have hcomp : χ.comp e.toMonoidHom = 1 :=
    alternatingGroup_fin5_units_hom_eq_one_over_any_field (χ.comp e.toMonoidHom)
  ext g
  have h := DFunLike.congr_fun hcomp (e.symm g)
  simpa using h

/-- Helper for Exercise 18-18.6-3: every finite matrix determinant character attached to an
`SL(2,𝔽₄)` representation is trivial. -/
theorem sl2F4_representation_matrix_det_eq_one
    {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module K V]
    (σ : Representation K (SL(2, 𝔽₄)) V) (b : Module.Basis ι K V)
    (g : SL(2, 𝔽₄)) :
    Matrix.det (LinearMap.toMatrix b b (σ g)) = 1 := by
  let χ : SL(2, 𝔽₄) →* Kˣ :=
    { toFun := fun h =>
        Units.mk0 (Matrix.det (LinearMap.toMatrix b b (σ h))) (by
          intro hzero
          have hdet_mul :
              Matrix.det (LinearMap.toMatrix b b (σ h)) *
                  Matrix.det (LinearMap.toMatrix b b (σ h⁻¹)) = (1 : K) := by
            calc
              Matrix.det (LinearMap.toMatrix b b (σ h)) *
                  Matrix.det (LinearMap.toMatrix b b (σ h⁻¹))
                  = Matrix.det ((LinearMap.toMatrix b b (σ h)) *
                      (LinearMap.toMatrix b b (σ h⁻¹))) := by
                        rw [Matrix.det_mul]
              _ = Matrix.det (LinearMap.toMatrix b b ((σ h) * (σ h⁻¹))) := by
                        rw [← LinearMap.toMatrix_mul b]
              _ = Matrix.det (LinearMap.toMatrix b b (σ (h * h⁻¹))) := by
                        rw [σ.map_mul]
              _ = Matrix.det (LinearMap.toMatrix b b (σ 1)) := by rw [mul_inv_cancel]
              _ = 1 := by simp
          rw [hzero, zero_mul] at hdet_mul
          exact zero_ne_one hdet_mul)
      map_one' := by
        apply Units.ext
        simp
      map_mul' := by
        intro h k
        -- Determinants of the action matrices multiply because the representation and matrix
        -- coordinate map both preserve products.
        apply Units.ext
        simp [σ.map_mul] }
  have hχ : χ = 1 := sl2F4_units_hom_eq_one_over_any_field χ
  -- Evaluating the trivial determinant character at `g` gives the desired scalar equality.
  have hg := congrArg (fun f : SL(2, 𝔽₄) →* Kˣ => f g) hχ
  exact Units.ext_iff.mp hg

/-- Helper for Exercise 18-18.6-3: if the first basis vector is upper-fixed, every upper
unipotent action matrix has the displayed unipotent form. -/
theorem sl2F4_upperMatrix_unipotent_of_fixedBasis
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (σ : Representation K (SL(2, 𝔽₄)) V)
    (b : Module.Basis (Fin 2) K V)
    (hUpper0 : ∀ a : 𝔽₄, σ (sl2F4Upper a) (b 0) = b 0) :
    ∃ lambdaParam : 𝔽₄ → K, ∀ a : 𝔽₄,
      LinearMap.toMatrix b b (σ (sl2F4Upper a)) =
        !![(1 : K), lambdaParam a; 0, 1] := by
  let lambdaParam : 𝔽₄ → K :=
    fun a => LinearMap.toMatrix b b (σ (sl2F4Upper a)) 0 1
  refine ⟨lambdaParam, ?_⟩
  intro a
  -- The fixed first basis vector determines the first column of the matrix.
  have h00 : LinearMap.toMatrix b b (σ (sl2F4Upper a)) 0 0 = 1 := by
    rw [LinearMap.toMatrix_apply, hUpper0 a, b.repr_self]
    simp
  have h10 : LinearMap.toMatrix b b (σ (sl2F4Upper a)) 1 0 = 0 := by
    rw [LinearMap.toMatrix_apply, hUpper0 a, b.repr_self]
    simp
  have hdet : Matrix.det (LinearMap.toMatrix b b (σ (sl2F4Upper a))) = 1 :=
    sl2F4_representation_matrix_det_eq_one σ b (sl2F4Upper a)
  have h11 : LinearMap.toMatrix b b (σ (sl2F4Upper a)) 1 1 = 1 := by
    -- With first column `(1,0)`, determinant one forces the lower-right entry to be one.
    rw [Matrix.det_fin_two] at hdet
    simpa [h00, h10] using hdet
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using h00
  · simp [lambdaParam]
  · simpa using h10
  · simpa using h11

/-- Helper for Exercise 18-18.6-3: the upper-unipotent matrix parameter sends zero to zero. -/
theorem sl2F4_upperMatrix_parameter_zero
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (σ : Representation K (SL(2, 𝔽₄)) V)
    (b : Module.Basis (Fin 2) K V)
    {lambdaParam : 𝔽₄ → K}
    (hUpperMatrix : ∀ a : 𝔽₄,
      LinearMap.toMatrix b b (σ (sl2F4Upper a)) =
        !![(1 : K), lambdaParam a; 0, 1]) :
    lambdaParam 0 = 0 := by
  -- Evaluate the `0,1` entry of the identity upper-unipotent matrix.
  have hentry :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) (hUpperMatrix 0)
  rw [sl2F4Upper_zero] at hentry
  simp at hentry
  exact hentry.symm

/-- Helper for Exercise 18-18.6-3: the upper-unipotent matrix parameter is additive. -/
theorem sl2F4_upperMatrix_parameter_add
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (σ : Representation K (SL(2, 𝔽₄)) V)
    (b : Module.Basis (Fin 2) K V)
    {lambdaParam : 𝔽₄ → K}
    (hUpperMatrix : ∀ a : 𝔽₄,
      LinearMap.toMatrix b b (σ (sl2F4Upper a)) =
        !![(1 : K), lambdaParam a; 0, 1]) :
    ∀ a c : 𝔽₄, lambdaParam (a + c) = lambdaParam a + lambdaParam c := by
  intro a c
  have hmat :
      LinearMap.toMatrix b b (σ (sl2F4Upper (a + c))) =
        LinearMap.toMatrix b b (σ (sl2F4Upper a)) *
          LinearMap.toMatrix b b (σ (sl2F4Upper c)) := by
    -- Convert upper-unipotent multiplication into multiplication of coordinate matrices.
    calc
      LinearMap.toMatrix b b (σ (sl2F4Upper (a + c))) =
          LinearMap.toMatrix b b (σ (sl2F4Upper a * sl2F4Upper c)) := by
            rw [sl2F4Upper_mul]
      _ = LinearMap.toMatrix b b ((σ (sl2F4Upper a)) * (σ (sl2F4Upper c))) := by
            rw [map_mul]
      _ = LinearMap.toMatrix b b (σ (sl2F4Upper a)) *
          LinearMap.toMatrix b b (σ (sl2F4Upper c)) := by
            rw [LinearMap.toMatrix_mul]
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hmat
  rw [hUpperMatrix (a + c), hUpperMatrix a, hUpperMatrix c] at hentry
  simpa [Matrix.mul_apply, add_comm, add_left_comm, add_assoc] using hentry

/-- Helper for Exercise 18-18.6-3: in a Weyl-swap basis, lower-unipotent matrices use the same
parameter as the upper-unipotent matrices. -/
theorem sl2F4_lowerMatrix_unipotent_of_weylBasis
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (σ : Representation K (SL(2, 𝔽₄)) V)
    (b : Module.Basis (Fin 2) K V)
    {lambdaParam : 𝔽₄ → K}
    (hWeyl : LinearMap.toMatrix b b (σ sl2F4Weyl) = !![(0 : K), 1; 1, 0])
    (hUpperMatrix : ∀ a : 𝔽₄,
      LinearMap.toMatrix b b (σ (sl2F4Upper a)) =
        !![(1 : K), lambdaParam a; 0, 1]) :
    ∀ a : 𝔽₄,
      LinearMap.toMatrix b b (σ (sl2F4Lower a)) =
        !![(1 : K), 0; lambdaParam a, 1] := by
  intro a
  have hLowerEq : sl2F4Lower a = sl2F4Weyl * sl2F4Upper a * sl2F4Weyl := by
    rw [← sl2F4Weyl_conj_upper a, sl2F4Weyl_inv]
  -- Conjugating by the Weyl swap matrix moves the upper parameter to the lower-left entry.
  calc
    LinearMap.toMatrix b b (σ (sl2F4Lower a)) =
        LinearMap.toMatrix b b (σ (sl2F4Weyl * sl2F4Upper a * sl2F4Weyl)) := by
          rw [hLowerEq]
    _ = LinearMap.toMatrix b b (σ sl2F4Weyl) *
        LinearMap.toMatrix b b (σ (sl2F4Upper a)) *
        LinearMap.toMatrix b b (σ sl2F4Weyl) := by
          simp [map_mul, LinearMap.toMatrix_mul, mul_assoc]
    _ = !![(1 : K), 0; lambdaParam a, 1] := by
          rw [hWeyl, hUpperMatrix a]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- Helper for Exercise 18-18.6-3: the Weyl factorization forces the upper parameter of `1` to
be `1`. -/
theorem sl2F4_upperMatrix_parameter_one
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (σ : Representation K (SL(2, 𝔽₄)) V)
    (b : Module.Basis (Fin 2) K V)
    {lambdaParam : 𝔽₄ → K}
    (hWeyl : LinearMap.toMatrix b b (σ sl2F4Weyl) = !![(0 : K), 1; 1, 0])
    (hUpperMatrix : ∀ a : 𝔽₄,
      LinearMap.toMatrix b b (σ (sl2F4Upper a)) =
        !![(1 : K), lambdaParam a; 0, 1])
    (hLowerMatrix : ∀ a : 𝔽₄,
      LinearMap.toMatrix b b (σ (sl2F4Lower a)) =
        !![(1 : K), 0; lambdaParam a, 1]) :
    lambdaParam 1 = 1 := by
  have hmat :
      LinearMap.toMatrix b b (σ sl2F4Weyl) =
        LinearMap.toMatrix b b (σ (sl2F4Upper 1)) *
          LinearMap.toMatrix b b (σ (sl2F4Lower 1)) *
            LinearMap.toMatrix b b (σ (sl2F4Upper 1)) := by
    -- Compare coordinate matrices in the elementary factorization `W = U(1)L(1)U(1)`.
    calc
      LinearMap.toMatrix b b (σ sl2F4Weyl) =
          LinearMap.toMatrix b b (σ (sl2F4Upper 1 * sl2F4Lower 1 * sl2F4Upper 1)) := by
            rw [sl2F4Weyl_eq_upper_lower_upper]
      _ = LinearMap.toMatrix b b (σ (sl2F4Upper 1)) *
          LinearMap.toMatrix b b (σ (sl2F4Lower 1)) *
            LinearMap.toMatrix b b (σ (sl2F4Upper 1)) := by
            simp [map_mul, LinearMap.toMatrix_mul, mul_assoc]
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hmat
  rw [hWeyl, hUpperMatrix 1, hLowerMatrix 1] at hentry
  simpa [Matrix.mul_apply] using hentry.symm

/-- Helper for Exercise 18-18.6-3: torus conjugation forces multiplication by square
parameters for the upper-unipotent coefficient. -/
theorem sl2F4_upperMatrix_parameter_square_mul
    {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (σ : Representation K (SL(2, 𝔽₄)) V)
    (b : Module.Basis (Fin 2) K V)
    {lambdaParam : 𝔽₄ → K}
    (hUpperMatrix : ∀ a : 𝔽₄,
      LinearMap.toMatrix b b (σ (sl2F4Upper a)) =
        !![(1 : K), lambdaParam a; 0, 1])
    (hLambda_one : lambdaParam 1 = 1) :
    ∀ (r : 𝔽₄ˣ) (a : 𝔽₄),
      lambdaParam ((r : 𝔽₄) ^ 2 * a) =
        lambdaParam ((r : 𝔽₄) ^ 2) * lambdaParam a := by
  intro r a
  let D : Matrix (Fin 2) (Fin 2) K :=
    LinearMap.toMatrix b b (σ (sl2F4Diag r))
  let s : 𝔽₄ := (r : 𝔽₄) ^ 2
  have hmat : ∀ x : 𝔽₄,
      D * !![(1 : K), lambdaParam x; 0, 1] =
        !![(1 : K), lambdaParam (s * x); 0, 1] * D := by
    intro x
    -- Rewrite the inverse-free torus relation as an equality of coordinate matrices.
    have hrep :
        LinearMap.toMatrix b b (σ (sl2F4Diag r)) *
            LinearMap.toMatrix b b (σ (sl2F4Upper x)) =
          LinearMap.toMatrix b b (σ (sl2F4Upper ((r : 𝔽₄) ^ 2 * x))) *
            LinearMap.toMatrix b b (σ (sl2F4Diag r)) := by
      calc
        LinearMap.toMatrix b b (σ (sl2F4Diag r)) *
            LinearMap.toMatrix b b (σ (sl2F4Upper x)) =
            LinearMap.toMatrix b b (σ (sl2F4Diag r) * σ (sl2F4Upper x)) := by
              exact (LinearMap.toMatrix_mul b
                (σ (sl2F4Diag r)) (σ (sl2F4Upper x))).symm
        _ = LinearMap.toMatrix b b (σ (sl2F4Diag r * sl2F4Upper x)) := by
              rw [σ.map_mul]
        _ = LinearMap.toMatrix b b
            (σ (sl2F4Upper ((r : 𝔽₄) ^ 2 * x) * sl2F4Diag r)) := by
              rw [sl2F4Diag_mul_upper]
        _ = LinearMap.toMatrix b b
            (σ (sl2F4Upper ((r : 𝔽₄) ^ 2 * x)) * σ (sl2F4Diag r)) := by
              rw [σ.map_mul]
        _ = LinearMap.toMatrix b b (σ (sl2F4Upper ((r : 𝔽₄) ^ 2 * x))) *
            LinearMap.toMatrix b b (σ (sl2F4Diag r)) := by
              exact LinearMap.toMatrix_mul b
                (σ (sl2F4Upper ((r : 𝔽₄) ^ 2 * x))) (σ (sl2F4Diag r))
    simpa [D, s, hUpperMatrix x, hUpperMatrix (s * x)] using hrep
  have hD10 : D 1 0 = 0 := by
    -- The lower-right entry of the torus relation at `x = 1` kills the lower-left entry of `D`.
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) (hmat 1)
    simpa [Matrix.mul_apply, hLambda_one] using hentry
  have hD00_eq : D 0 0 = lambdaParam s * D 1 1 := by
    -- The upper-right entry at `x = 1` identifies the diagonal ratio with `λ(s)`.
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) (hmat 1)
    have hentry' : D 0 0 + D 0 1 = D 0 1 + lambdaParam s * D 1 1 := by
      simpa [Matrix.mul_apply, hD10, hLambda_one, add_comm, add_left_comm, add_assoc]
        using hentry
    calc
      D 0 0 = (D 0 0 + D 0 1) - D 0 1 := by ring
      _ = (D 0 1 + lambdaParam s * D 1 1) - D 0 1 := by rw [hentry']
      _ = lambdaParam s * D 1 1 := by ring
  have hD00_mul :
      D 0 0 * lambdaParam a = lambdaParam (s * a) * D 1 1 := by
    -- The same upper-right entry at `a` gives the desired relation after canceling `D 1 1`.
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) (hmat a)
    have hentry' :
        D 0 0 * lambdaParam a + D 0 1 =
          D 0 1 + lambdaParam (s * a) * D 1 1 := by
      simpa [Matrix.mul_apply, hD10, add_comm, add_left_comm, add_assoc] using hentry
    calc
      D 0 0 * lambdaParam a = (D 0 0 * lambdaParam a + D 0 1) - D 0 1 := by ring
      _ = (D 0 1 + lambdaParam (s * a) * D 1 1) - D 0 1 := by rw [hentry']
      _ = lambdaParam (s * a) * D 1 1 := by ring
  have hD11_ne_zero : D 1 1 ≠ 0 := by
    -- The determinant of the representation matrix is one, and `D 1 0 = 0`.
    intro hD11_zero
    have hdet : Matrix.det D = 1 := by
      simpa [D] using sl2F4_representation_matrix_det_eq_one σ b (sl2F4Diag r)
    have hdet_entries :
        D 0 0 * D 1 1 - D 0 1 * D 1 0 = 1 := by
      simpa using (by
        rw [Matrix.det_fin_two] at hdet
        exact hdet)
    have hzero : (0 : K) = 1 := by
      simp [hD10, hD11_zero] at hdet_entries
    exact zero_ne_one hzero
  have hcancel :
      (lambdaParam s * lambdaParam a) * D 1 1 =
        lambdaParam (s * a) * D 1 1 := by
    calc
      (lambdaParam s * lambdaParam a) * D 1 1 =
          (lambdaParam s * D 1 1) * lambdaParam a := by ring
      _ = D 0 0 * lambdaParam a := by rw [← hD00_eq]
      _ = lambdaParam (s * a) * D 1 1 := hD00_mul
  exact (mul_right_cancel₀ hD11_ne_zero hcancel).symm

/-- Helper for Exercise 18-18.6-3: a parameter satisfying all square-multiplier identities over
`𝔽₄` is multiplicative. -/
theorem f4_parameter_mul_of_square_mul
    {K : Type*} [Field K]
    (lambdaParam : 𝔽₄ → K)
    (hLambda_zero : lambdaParam 0 = 0)
    (hLambda_square_mul : ∀ (r : 𝔽₄ˣ) (a : 𝔽₄),
      lambdaParam ((r : 𝔽₄) ^ 2 * a) =
        lambdaParam ((r : 𝔽₄) ^ 2) * lambdaParam a) :
    ∀ a b : 𝔽₄, lambdaParam (a * b) = lambdaParam a * lambdaParam b := by
  intro a b
  -- The zero multiplier is immediate from the already known zero value.
  by_cases hb : b = 0
  · rw [hb, mul_zero, hLambda_zero, mul_zero]
  -- A nonzero element of `𝔽₄` is a square, so the square-multiplier relation applies to `b`.
  rcases f4_exists_unit_sq_eq hb with ⟨r, hr⟩
  have hsquare := hLambda_square_mul r a
  calc
    lambdaParam (a * b) = lambdaParam ((r : 𝔽₄) ^ 2 * a) := by
      rw [hr, mul_comm]
    _ = lambdaParam ((r : 𝔽₄) ^ 2) * lambdaParam a := hsquare
    _ = lambdaParam b * lambdaParam a := by rw [hr]
    _ = lambdaParam a * lambdaParam b := by rw [mul_comm]

/-- Helper for Exercise 18-18.6-3: the normalized upper-unipotent parameter packages as a
ring homomorphism `𝔽₄ → K`. -/
theorem f4_ringHom_of_additive_squareMul_parameter
    {K : Type*} [Field K]
    (lambdaParam : 𝔽₄ → K)
    (hLambda_zero : lambdaParam 0 = 0)
    (hLambda_add : ∀ a c : 𝔽₄, lambdaParam (a + c) = lambdaParam a + lambdaParam c)
    (hLambda_one : lambdaParam 1 = 1)
    (hLambda_square_mul : ∀ (r : 𝔽₄ˣ) (a : 𝔽₄),
      lambdaParam ((r : 𝔽₄) ^ 2 * a) =
        lambdaParam ((r : 𝔽₄) ^ 2) * lambdaParam a) :
    ∃ φ : 𝔽₄ →+* K, ∀ a : 𝔽₄, φ a = lambdaParam a := by
  -- The preceding finite-field lemma supplies the only missing ring-hom field.
  have hLambda_mul : ∀ a b : 𝔽₄, lambdaParam (a * b) =
      lambdaParam a * lambdaParam b :=
    f4_parameter_mul_of_square_mul lambdaParam hLambda_zero hLambda_square_mul
  let φ : 𝔽₄ →+* K :=
    { toFun := lambdaParam
      map_zero' := hLambda_zero
      map_one' := hLambda_one
      map_add' := hLambda_add
      map_mul' := hLambda_mul }
  refine ⟨φ, ?_⟩
  intro a
  rfl

/-- Helper for Exercise 18-18.6-3: every ring endomorphism of `𝔽₄` is either the identity or
the Frobenius square map. -/
theorem f4_ringEnd_eq_id_or_frobenius (φ : 𝔽₄ →+* 𝔽₄) :
    (∀ a : 𝔽₄, φ a = a) ∨ (∀ a : 𝔽₄, φ a = a ^ 2) := by
  -- View the ring endomorphism as a `ZMod 2`-algebra endomorphism, since finite-field
  -- automorphisms are generated by Frobenius over the prime field.
  letI : Algebra (ZMod 2) 𝔽₄ := FiniteField.instAlgebraExtension (ZMod 2) 2 2
  let φAlg : 𝔽₄ →ₐ[ZMod 2] 𝔽₄ :=
    { toRingHom := φ
      commutes' := by
        intro r
        fin_cases r
        · calc
            φ ((algebraMap (ZMod 2) 𝔽₄) 0) = φ 0 := by rw [map_zero]
            _ = 0 := map_zero φ
            _ = (algebraMap (ZMod 2) 𝔽₄) 0 := (map_zero _).symm
        · calc
            φ ((algebraMap (ZMod 2) 𝔽₄) 1) = φ 1 := by rw [map_one]
            _ = 1 := map_one φ
            _ = (algebraMap (ZMod 2) 𝔽₄) 1 := (map_one _).symm }
  have hφAlg_bij : Function.Bijective φAlg := by
    -- A nonzero field homomorphism is injective, and an injective self-map of a finite type is
    -- surjective.
    have hφAlg_inj : Function.Injective φAlg := by
      exact RingHom.injective φ
    exact ⟨hφAlg_inj, Finite.surjective_of_injective hφAlg_inj⟩
  let e : Gal(𝔽₄/ZMod 2) := AlgEquiv.ofBijective φAlg hφAlg_bij
  rcases FiniteField.Extension.exists_frob_pow_eq (ZMod 2) 2 2 e with ⟨i, hi, he⟩
  interval_cases i
  · left
    intro a
    -- The zeroth Frobenius power is the identity.
    have happ := congrArg (fun τ : Gal(𝔽₄/ZMod 2) => τ a) he
    simpa [e, φAlg] using happ.symm
  · right
    intro a
    -- The first Frobenius power over `ZMod 2` is the square map.
    have happ := congrArg (fun τ : Gal(𝔽₄/ZMod 2) => τ a) he
    have hfrob : (FiniteField.Extension.frob (ZMod 2) 2 2) a = a ^ 2 := by
      simp
    simpa [e, φAlg, hfrob] using happ.symm

/-- Helper for Exercise 18-18.6-3: a ring homomorphism from `𝔽₄` into an extension field is
either the chosen embedding or that embedding precomposed with Frobenius. -/
theorem f4_ringHom_eq_algebraMap_or_frobenius
    {K : Type*} [Field K] [Algebra 𝔽₄ K] (φ : 𝔽₄ →+* K) :
    (∀ a : 𝔽₄, φ a = algebraMap 𝔽₄ K a) ∨
      (∀ a : 𝔽₄, φ a = algebraMap 𝔽₄ K (a ^ 2)) := by
  -- Work over the prime field. The two embeddings of the splitting field `𝔽₄` into `K` have the
  -- same range, because both ranges are the subalgebra generated by the roots of `X^4 - X`.
  letI : Algebra (ZMod 2) 𝔽₄ := FiniteField.instAlgebraExtension (ZMod 2) 2 2
  letI : Algebra (ZMod 2) K :=
    RingHom.toAlgebra ((algebraMap 𝔽₄ K).comp (algebraMap (ZMod 2) 𝔽₄))
  let φAlg : 𝔽₄ →ₐ[ZMod 2] K :=
    { toRingHom := φ
      commutes' := by
        intro r
        fin_cases r
        · calc
            φ ((algebraMap (ZMod 2) 𝔽₄) 0) = φ 0 := by rw [map_zero]
            _ = 0 := map_zero φ
            _ = (algebraMap (ZMod 2) K) 0 := (map_zero _).symm
        · calc
            φ ((algebraMap (ZMod 2) 𝔽₄) 1) = φ 1 := by rw [map_one]
            _ = 1 := map_one φ
            _ = (algebraMap (ZMod 2) K) 1 := (map_one _).symm }
  let baseAlg : 𝔽₄ →ₐ[ZMod 2] K :=
    { toRingHom := algebraMap 𝔽₄ K
      commutes' := by
        intro r
        rfl }
  have hRange_eq : φAlg.range = baseAlg.range := by
    let p : Polynomial (ZMod 2) := Polynomial.X ^ Nat.card (ZMod 2) ^ 2 - Polynomial.X
    have hφRange : Algebra.adjoin (ZMod 2) (p.rootSet K) = φAlg.range := by
      simpa [p] using
        (Polynomial.IsSplittingField.adjoin_rootSet_eq_range (L := 𝔽₄) (F := K) p φAlg)
    have hbaseRange : Algebra.adjoin (ZMod 2) (p.rootSet K) = baseAlg.range := by
      simpa [p] using
        (Polynomial.IsSplittingField.adjoin_rootSet_eq_range (L := 𝔽₄) (F := K) p baseAlg)
    exact hφRange.symm.trans hbaseRange
  have hmem : ∀ a : 𝔽₄, φ a ∈ baseAlg.range := by
    intro a
    -- Transfer membership from the range of `φ` to the range of the chosen embedding.
    have ha : φAlg a ∈ φAlg.range := ⟨a, rfl⟩
    simpa [φAlg] using (show φAlg a ∈ baseAlg.range from by simpa [hRange_eq] using ha)
  choose ψ hψ using hmem
  let ψRing : 𝔽₄ →+* 𝔽₄ :=
    { toFun := ψ
      map_zero' := by
        apply (algebraMap 𝔽₄ K).injective
        calc
          algebraMap 𝔽₄ K (ψ 0) = φ 0 := hψ 0
          _ = 0 := map_zero φ
          _ = algebraMap 𝔽₄ K 0 := (map_zero _).symm
      map_one' := by
        apply (algebraMap 𝔽₄ K).injective
        calc
          algebraMap 𝔽₄ K (ψ 1) = φ 1 := hψ 1
          _ = 1 := map_one φ
          _ = algebraMap 𝔽₄ K 1 := (map_one _).symm
      map_add' := by
        intro a b
        apply (algebraMap 𝔽₄ K).injective
        calc
          algebraMap 𝔽₄ K (ψ (a + b)) = φ (a + b) := hψ (a + b)
          _ = φ a + φ b := map_add φ a b
          _ = algebraMap 𝔽₄ K (ψ a) + algebraMap 𝔽₄ K (ψ b) := by rw [hψ a, hψ b]
          _ = algebraMap 𝔽₄ K (ψ a + ψ b) := (map_add _ _ _).symm
      map_mul' := by
        intro a b
        apply (algebraMap 𝔽₄ K).injective
        calc
          algebraMap 𝔽₄ K (ψ (a * b)) = φ (a * b) := hψ (a * b)
          _ = φ a * φ b := map_mul φ a b
          _ = algebraMap 𝔽₄ K (ψ a) * algebraMap 𝔽₄ K (ψ b) := by rw [hψ a, hψ b]
          _ = algebraMap 𝔽₄ K (ψ a * ψ b) := (map_mul _ _ _).symm }
  -- Classify the induced endomorphism of `𝔽₄`, then map the conclusion back into `K`.
  rcases f4_ringEnd_eq_id_or_frobenius ψRing with hψid | hψfrob
  · left
    intro a
    calc
      φ a = algebraMap 𝔽₄ K (ψRing a) := (hψ a).symm
      _ = algebraMap 𝔽₄ K a := by rw [hψid a]
  · right
    intro a
    calc
      φ a = algebraMap 𝔽₄ K (ψRing a) := (hψ a).symm
      _ = algebraMap 𝔽₄ K (a ^ 2) := by rw [hψfrob a]

/-- Helper for Exercise 18-18.6-3: the standard basis of the natural two-dimensional
`𝔽₄`-module. -/
abbrev sl2F4StandardBasis : Module.Basis (Fin 2) 𝔽₄ (Fin 2 → 𝔽₄) :=
  Pi.basisFun 𝔽₄ (Fin 2)

/-- Helper for Exercise 18-18.6-3: the natural matrix representation of `SL(2,𝔽₄)` on
`𝔽₄²`. -/
def sl2F4NaturalRep : Representation 𝔽₄ (SL(2, 𝔽₄)) (Fin 2 → 𝔽₄) :=
  (Representation.ofDistribMulAction 𝔽₄
      (SpecialLinearGroup 𝔽₄ (Fin 2 → 𝔽₄)) (Fin 2 → 𝔽₄)).comp
    (Matrix.SpecialLinearGroup.toLin'_equiv (R := 𝔽₄) (n := Fin 2)).toMonoidHom

/-- Helper for Exercise 18-18.6-3: Frobenius on `𝔽₄` as a ring homomorphism. -/
def f4FrobeniusRingHom : 𝔽₄ →+* 𝔽₄ :=
  letI : Algebra (ZMod 2) 𝔽₄ := FiniteField.instAlgebraExtension (ZMod 2) 2 2
  (FiniteField.Extension.frob (ZMod 2) 2 2).toRingHom

/-- Helper for Exercise 18-18.6-3: Frobenius on `𝔽₄` is the square map. -/
theorem f4FrobeniusRingHom_apply (a : 𝔽₄) :
    f4FrobeniusRingHom a = a ^ 2 := by
  -- Use the standard finite-field Frobenius computation, with the algebra instance fixed to the
  -- extension-field one used by `FiniteField.Extension.frob`.
  letI : Algebra (ZMod 2) 𝔽₄ := FiniteField.instAlgebraExtension (ZMod 2) 2 2
  simp [f4FrobeniusRingHom, FiniteField.Extension.frob_apply]

/-- Helper for Exercise 18-18.6-3: entrywise Frobenius as a group endomorphism of
`SL(2,𝔽₄)`. -/
def sl2F4FrobeniusHom : SL(2, 𝔽₄) →* SL(2, 𝔽₄) :=
  Matrix.SpecialLinearGroup.map (n := Fin 2) f4FrobeniusRingHom

/-- Helper for Exercise 18-18.6-3: Frobenius sends upper elementary matrices to the same
matrices with squared parameter. -/
theorem sl2F4FrobeniusHom_upper (a : 𝔽₄) :
    sl2F4FrobeniusHom (sl2F4Upper a) = sl2F4Upper (a ^ 2) := by
  -- Check the four entries after applying the ring endomorphism.
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2F4FrobeniusHom, Matrix.SpecialLinearGroup.map, sl2F4Upper,
      f4FrobeniusRingHom_apply]

/-- Helper for Exercise 18-18.6-3: Frobenius sends lower elementary matrices to the same
matrices with squared parameter. -/
theorem sl2F4FrobeniusHom_lower (a : 𝔽₄) :
    sl2F4FrobeniusHom (sl2F4Lower a) = sl2F4Lower (a ^ 2) := by
  -- The lower-left entry is the only nontrivial parameter.
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2F4FrobeniusHom, Matrix.SpecialLinearGroup.map, sl2F4Lower,
      f4FrobeniusRingHom_apply]

/-- Helper for Exercise 18-18.6-3: the Frobenius-twisted natural representation. -/
def sl2F4FrobeniusRep : Representation 𝔽₄ (SL(2, 𝔽₄)) (Fin 2 → 𝔽₄) :=
  sl2F4NaturalRep.comp sl2F4FrobeniusHom

/-- Helper for Exercise 18-18.6-3: the natural source model has the expected upper elementary
matrix in the standard basis. -/
theorem sl2F4NaturalRep_upper_toMatrix (a : 𝔽₄) :
    LinearMap.toMatrix sl2F4StandardBasis sl2F4StandardBasis
        (sl2F4NaturalRep (sl2F4Upper a)) =
      !![(1 : 𝔽₄), a; 0, 1] := by
  -- The matrix action on coordinate functions is exactly multiplication by the displayed matrix.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2F4NaturalRep, sl2F4StandardBasis, sl2F4Upper,
      SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.toLin'_equiv,
      Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 18-18.6-3: the natural source model has the expected lower elementary
matrix in the standard basis. -/
theorem sl2F4NaturalRep_lower_toMatrix (a : 𝔽₄) :
    LinearMap.toMatrix sl2F4StandardBasis sl2F4StandardBasis
        (sl2F4NaturalRep (sl2F4Lower a)) =
      !![(1 : 𝔽₄), 0; a, 1] := by
  -- This is the same direct matrix-action computation for lower unipotents.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2F4NaturalRep, sl2F4StandardBasis, sl2F4Lower,
      SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.toLin'_equiv,
      Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 18-18.6-3: after scalar extension, the natural source upper elementary
matrices have entries mapped by `algebraMap`. -/
theorem sl2F4NaturalRep_scalarExtension_upper_toMatrix
    {K : Type*} [Field K] [Algebra 𝔽₄ K] (a : 𝔽₄) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis K sl2F4StandardBasis)
      (Algebra.TensorProduct.basis K sl2F4StandardBasis)
        ((Representation.scalarExtension (k := K) sl2F4NaturalRep) (sl2F4Upper a)) =
      !![(1 : K), algebraMap 𝔽₄ K a; 0, 1] := by
  -- Reduce scalar extension of the action to `LinearMap.toMatrix_baseChange`, then map entries.
  have hbase :
      ((Representation.scalarExtension (k := K) sl2F4NaturalRep) (sl2F4Upper a)) =
        (sl2F4NaturalRep (sl2F4Upper a)).baseChange K := rfl
  rw [hbase]
  have h := LinearMap.toMatrix_baseChange K
    (sl2F4NaturalRep (sl2F4Upper a)) sl2F4StandardBasis sl2F4StandardBasis
  rw [sl2F4NaturalRep_upper_toMatrix a] at h
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Helper for Exercise 18-18.6-3: after scalar extension, the natural source lower elementary
matrices have entries mapped by `algebraMap`. -/
theorem sl2F4NaturalRep_scalarExtension_lower_toMatrix
    {K : Type*} [Field K] [Algebra 𝔽₄ K] (a : 𝔽₄) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis K sl2F4StandardBasis)
      (Algebra.TensorProduct.basis K sl2F4StandardBasis)
        ((Representation.scalarExtension (k := K) sl2F4NaturalRep) (sl2F4Lower a)) =
      !![(1 : K), 0; algebraMap 𝔽₄ K a, 1] := by
  -- The lower formula is the base-change of the source lower matrix table.
  have hbase :
      ((Representation.scalarExtension (k := K) sl2F4NaturalRep) (sl2F4Lower a)) =
        (sl2F4NaturalRep (sl2F4Lower a)).baseChange K := rfl
  rw [hbase]
  have h := LinearMap.toMatrix_baseChange K
    (sl2F4NaturalRep (sl2F4Lower a)) sl2F4StandardBasis sl2F4StandardBasis
  rw [sl2F4NaturalRep_lower_toMatrix a] at h
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Helper for Exercise 18-18.6-3: scalar extension of the Frobenius source model has upper
elementary matrices with squared parameter. -/
theorem sl2F4FrobeniusRep_scalarExtension_upper_toMatrix
    {K : Type*} [Field K] [Algebra 𝔽₄ K] (a : 𝔽₄) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis K sl2F4StandardBasis)
      (Algebra.TensorProduct.basis K sl2F4StandardBasis)
        ((Representation.scalarExtension (k := K) sl2F4FrobeniusRep) (sl2F4Upper a)) =
      !![(1 : K), algebraMap 𝔽₄ K (a ^ 2); 0, 1] := by
  -- Precomposition by Frobenius turns `U(a)` into `U(a²)`, so reuse the natural table.
  have hact :
      ((Representation.scalarExtension (k := K) sl2F4FrobeniusRep) (sl2F4Upper a)) =
        ((Representation.scalarExtension (k := K) sl2F4NaturalRep)
          (sl2F4Upper (a ^ 2))) := by
    simp [sl2F4FrobeniusRep, sl2F4FrobeniusHom_upper, Representation.scalarExtension]
  rw [hact]
  exact sl2F4NaturalRep_scalarExtension_upper_toMatrix (K := K) (a ^ 2)

/-- Helper for Exercise 18-18.6-3: scalar extension of the Frobenius source model has lower
elementary matrices with squared parameter. -/
theorem sl2F4FrobeniusRep_scalarExtension_lower_toMatrix
    {K : Type*} [Field K] [Algebra 𝔽₄ K] (a : 𝔽₄) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis K sl2F4StandardBasis)
      (Algebra.TensorProduct.basis K sl2F4StandardBasis)
        ((Representation.scalarExtension (k := K) sl2F4FrobeniusRep) (sl2F4Lower a)) =
      !![(1 : K), 0; algebraMap 𝔽₄ K (a ^ 2), 1] := by
  -- Again reduce the Frobenius-twist table to the natural lower table at `a²`.
  have hact :
      ((Representation.scalarExtension (k := K) sl2F4FrobeniusRep) (sl2F4Lower a)) =
        ((Representation.scalarExtension (k := K) sl2F4NaturalRep)
          (sl2F4Lower (a ^ 2))) := by
    simp [sl2F4FrobeniusRep, sl2F4FrobeniusHom_lower, Representation.scalarExtension]
  rw [hact]
  exact sl2F4NaturalRep_scalarExtension_lower_toMatrix (K := K) (a ^ 2)

/-- Helper for Exercise 18-18.6-3: equal coordinate matrices in two bases make the basis-change
linear equivalence intertwine the two endomorphisms. -/
theorem basisEquiv_intertwines_of_toMatrix_eq
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (bV : Module.Basis (Fin 2) K V) (bW : Module.Basis (Fin 2) K W)
    {f : V →ₗ[K] V} {g : W →ₗ[K] W}
    (h : LinearMap.toMatrix bV bV f = LinearMap.toMatrix bW bW g) :
    let e : V ≃ₗ[K] W := bV.equiv bW (_root_.Equiv.refl (Fin 2))
    e.toLinearMap.comp f = g.comp e.toLinearMap := by
  intro e
  -- Compare the two composites on each source basis vector and read the target coordinates.
  apply bV.ext
  intro i
  apply bW.ext_elem
  intro j
  have hij := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M j i) h
  simpa [e, Module.Basis.equiv_apply, Module.Basis.equiv, LinearMap.toMatrix_apply] using hij

/-- Helper for Exercise 18-18.6-3: intertwining identities are closed under multiplication in
the acting group. -/
private theorem intertwines_mul_of_intertwines
    {K G V W : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K G V) (τ : Representation K G W) (e : V ≃ₗ[K] W)
    {g h : G}
    (hg : e.toLinearMap.comp (ρ g) = (τ g).comp e.toLinearMap)
    (hh : e.toLinearMap.comp (ρ h) = (τ h).comp e.toLinearMap) :
    e.toLinearMap.comp (ρ (g * h)) = (τ (g * h)).comp e.toLinearMap := by
  -- Evaluate on a vector; the representation multiplication law gives the two-step action.
  ext x
  have hgx : e (ρ g (ρ h x)) = τ g (e (ρ h x)) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hg (ρ h x)
  have hhx : e (ρ h x) = τ h (e x) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hh x
  calc
    e (ρ (g * h) x) = e (ρ g (ρ h x)) := by simp [map_mul]
    _ = τ g (e (ρ h x)) := hgx
    _ = τ g (τ h (e x)) := by rw [hhx]
    _ = τ (g * h) (e x) := by simp [map_mul]

/-- Helper for Exercise 18-18.6-3: an intertwining identity for an element gives the identity
for its inverse. -/
private theorem intertwines_inv_of_intertwines
    {K G V W : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K G V) (τ : Representation K G W) (e : V ≃ₗ[K] W)
    {g : G}
    (hg : e.toLinearMap.comp (ρ g) = (τ g).comp e.toLinearMap) :
    e.toLinearMap.comp (ρ g⁻¹) = (τ g⁻¹).comp e.toLinearMap := by
  -- Cancel the known identity by applying the inverse action on the target side.
  ext x
  have hτ : τ g (e (ρ g⁻¹ x)) = e x := by
    have h := LinearMap.congr_fun hg (ρ g⁻¹ x)
    simpa [LinearMap.comp_apply, ← map_mul] using h.symm
  calc
    e (ρ g⁻¹ x) = τ g⁻¹ (τ g (e (ρ g⁻¹ x))) := by
      simp
    _ = τ g⁻¹ (e x) := by rw [hτ]

/-- Helper for Exercise 18-18.6-3: upper and lower elementary matrix tables determine a
two-dimensional representation of `SL(2,𝔽₄)` up to equivalence. -/
theorem sl2F4_equiv_of_elementary_toMatrix
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K (SL(2, 𝔽₄)) V)
    (τ : Representation K (SL(2, 𝔽₄)) W)
    (bV : Module.Basis (Fin 2) K V) (bW : Module.Basis (Fin 2) K W)
    (hUpper : ∀ a : 𝔽₄,
      LinearMap.toMatrix bV bV (ρ (sl2F4Upper a)) =
        LinearMap.toMatrix bW bW (τ (sl2F4Upper a)))
    (hLower : ∀ a : 𝔽₄,
      LinearMap.toMatrix bV bV (ρ (sl2F4Lower a)) =
        LinearMap.toMatrix bW bW (τ (sl2F4Lower a))) :
    Nonempty (ρ.Equiv τ) := by
  let e : V ≃ₗ[K] W := bV.equiv bW (_root_.Equiv.refl (Fin 2))
  let H : Subgroup (SL(2, 𝔽₄)) :=
    { carrier := {g | e.toLinearMap.comp (ρ g) = (τ g).comp e.toLinearMap}
      one_mem' := by
        ext x
        simp [e]
      mul_mem' := by
        intro g h hg hh
        exact intertwines_mul_of_intertwines ρ τ e hg hh
      inv_mem' := by
        intro g hg
        exact intertwines_inv_of_intertwines ρ τ e hg }
  have hUpper_H : ∀ a : 𝔽₄, sl2F4Upper a ∈ H := by
    intro a
    -- Matrix equality for `U(a)` gives the intertwining identity for that generator.
    exact basisEquiv_intertwines_of_toMatrix_eq bV bW (hUpper a)
  have hLower_H : ∀ a : 𝔽₄, sl2F4Lower a ∈ H := by
    intro a
    -- The lower generators are handled by the same basis adapter.
    exact basisEquiv_intertwines_of_toMatrix_eq bV bW (hLower a)
  have hElementary_le_H : sl2F4ElementarySubgroup ≤ H := by
    -- The subgroup of intertwined elements contains both halves of the elementary generating set.
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact hUpper_H a
    · exact hLower_H a
  have hAll : ∀ g : SL(2, 𝔽₄),
      e.toLinearMap.comp (ρ g) = (τ g).comp e.toLinearMap := by
    intro g
    -- Upper and lower unipotents generate all of `SL(2,𝔽₄)`.
    exact hElementary_le_H (by rw [sl2F4Elementary_closure_eq_top]; simp)
  exact ⟨Representation.Equiv.mk e hAll⟩

/-- Helper for Exercise 18-18.6-3: the `ULift` transport map preserves products. -/
private theorem uliftSourceRepresentation_map_one
    {k G W : Type*} [Field k] [Group G]
    [AddCommGroup W] [Module k W]
    (ρ : Representation k G W) :
    (fun g : G => ((ULift.moduleEquiv : ULift.{u} W ≃ₗ[k] W).symm).conj (ρ g)) 1 =
      1 := by
  -- The transported identity action is still the identity after removing the `ULift` wrapper.
  ext x
  simp [LinearEquiv.conj_apply_apply]

/-- Helper for Exercise 18-18.6-3: the `ULift` transport map preserves products. -/
private theorem uliftSourceRepresentation_map_mul
    {k G W : Type*} [Field k] [Group G]
    [AddCommGroup W] [Module k W]
    (ρ : Representation k G W) :
    ∀ g h : G,
      (fun g : G => ((ULift.moduleEquiv : ULift.{u} W ≃ₗ[k] W).symm).conj (ρ g)) (g * h) =
        (fun g : G => ((ULift.moduleEquiv : ULift.{u} W ≃ₗ[k] W).symm).conj (ρ g)) g *
          (fun g : G => ((ULift.moduleEquiv : ULift.{u} W ≃ₗ[k] W).symm).conj (ρ g)) h := by
  intro g h
  -- Remove the `ULift` wrapper and use the representation's multiplication law.
  ext x
  simp [LinearEquiv.conj_apply_apply, map_mul]

/-- Helper for Exercise 18-18.6-3: move a source representation into the target universe by
transporting the action to `ULift`. -/
private def uliftSourceRepresentation
    {k G W : Type*} [Field k] [Group G]
    [AddCommGroup W] [Module k W]
    (ρ : Representation k G W) : Representation k G (ULift.{u} W) where
  toFun g := ((ULift.moduleEquiv : ULift.{u} W ≃ₗ[k] W).symm).conj (ρ g)
  map_one' := uliftSourceRepresentation_map_one ρ
  map_mul' := uliftSourceRepresentation_map_mul ρ

/-- Helper for Exercise 18-18.6-3: the `ULift` source action is intertwined with the original
source action by the wrapper equivalence. -/
private theorem uliftSourceRepresentation_intertwining
    {k G W : Type*} [Field k] [Group G]
    [AddCommGroup W] [Module k W]
    (ρ : Representation k G W) :
    let eLift : W ≃ₗ[k] ULift.{u} W :=
      (ULift.moduleEquiv : ULift.{u} W ≃ₗ[k] W).symm
    ∀ g : G,
      eLift.toLinearMap.comp (ρ g) =
        ((uliftSourceRepresentation ρ : Representation k G (ULift.{u} W)) g).comp
          eLift.toLinearMap := by
  intro eLift g
  -- Both sides evaluate to the same wrapped vector.
  ext x
  simp [uliftSourceRepresentation, eLift, LinearEquiv.conj_apply_apply]

/-- Helper for Exercise 18-18.6-3: the `ULift` source representation is equivalent to the
original one. -/
private def uliftSourceRepresentationEquiv
    {k G W : Type*} [Field k] [Group G]
    [AddCommGroup W] [Module k W]
    (ρ : Representation k G W) :
    ρ.Equiv (uliftSourceRepresentation ρ : Representation k G (ULift.{u} W)) :=
  let eLift : W ≃ₗ[k] ULift.{u} W :=
    (ULift.moduleEquiv : ULift.{u} W ≃ₗ[k] W).symm
  Representation.Equiv.mk eLift (uliftSourceRepresentation_intertwining ρ)

/-- Helper for Exercise 18-18.6-3: a source representation equivalence remains an equivalence
after scalar extension. -/
private theorem sl2F4_scalarExtensionEquiv_of_equiv
    {k₀ k G W W' : Type*} [Field k₀] [Field k] [Algebra k₀ k] [Group G]
    [AddCommGroup W] [Module k₀ W] [AddCommGroup W'] [Module k₀ W']
    {ρ : Representation k₀ G W} {σ : Representation k₀ G W'}
    (e : ρ.Equiv σ) :
    Nonempty
      ((Representation.scalarExtension (k := k) ρ).Equiv
        (Representation.scalarExtension (k := k) σ)) := by
  -- Base-change the intertwining linear equivalence and check equivariance on pure tensors.
  refine ⟨Representation.Equiv.mk (e.toLinearEquiv.baseChange k₀ k W W') ?_⟩
  intro g
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  have hx := LinearMap.congr_fun (e.isIntertwining' g) x
  simpa [Representation.scalarExtension]
    using congrArg (fun y ↦ a ⊗ₜ[k₀] y) hx

/-- Helper for Exercise 18-18.6-3: upper/lower elementary normal form with an embedding
`φ : 𝔽₄ →+* K` descends to either the natural or Frobenius source model over `𝔽₄`. -/
theorem sl2F4_realizableOver_of_elementaryEmbeddingNormalForm
    {K : Type*} [Field K] [Algebra 𝔽₄ K]
    {V : Type u} [AddCommGroup V] [Module K V]
    (σ : Representation K (SL(2, 𝔽₄)) V)
    (b : Module.Basis (Fin 2) K V) (φ : 𝔽₄ →+* K)
    (hUpper : ∀ a : 𝔽₄,
      LinearMap.toMatrix b b (σ (sl2F4Upper a)) =
        !![(1 : K), φ a; 0, 1])
    (hLower : ∀ a : 𝔽₄,
      LinearMap.toMatrix b b (σ (sl2F4Lower a)) =
        !![(1 : K), 0; φ a, 1])
    (hφ : (∀ a : 𝔽₄, φ a = algebraMap 𝔽₄ K a) ∨
      (∀ a : 𝔽₄, φ a = algebraMap 𝔽₄ K (a ^ 2))) :
    Representation.IsRealizableOver 𝔽₄ σ := by
  let bSrc := Algebra.TensorProduct.basis K sl2F4StandardBasis
  rcases hφ with hφid | hφfrob
  · have hEquiv :
        Nonempty (σ.Equiv
          (Representation.scalarExtension (k := K) sl2F4NaturalRep)) := by
      -- In the identity-embedding case, the target and natural source have identical generator
      -- matrices in the chosen bases.
      apply sl2F4_equiv_of_elementary_toMatrix σ
        (Representation.scalarExtension (k := K) sl2F4NaturalRep) b bSrc
      · intro a
        calc
          LinearMap.toMatrix b b (σ (sl2F4Upper a)) =
              !![(1 : K), φ a; 0, 1] := hUpper a
          _ = !![(1 : K), algebraMap 𝔽₄ K a; 0, 1] := by rw [hφid a]
          _ = LinearMap.toMatrix bSrc bSrc
              ((Representation.scalarExtension (k := K) sl2F4NaturalRep)
                (sl2F4Upper a)) :=
                (sl2F4NaturalRep_scalarExtension_upper_toMatrix (K := K) a).symm
      · intro a
        calc
          LinearMap.toMatrix b b (σ (sl2F4Lower a)) =
              !![(1 : K), 0; φ a, 1] := hLower a
          _ = !![(1 : K), 0; algebraMap 𝔽₄ K a, 1] := by rw [hφid a]
          _ = LinearMap.toMatrix bSrc bSrc
              ((Representation.scalarExtension (k := K) sl2F4NaturalRep)
                (sl2F4Lower a)) :=
                (sl2F4NaturalRep_scalarExtension_lower_toMatrix (K := K) a).symm
    rcases hEquiv with ⟨e⟩
    let ρLift : Representation 𝔽₄ (SL(2, 𝔽₄)) (ULift.{u} (Fin 2 → 𝔽₄)) :=
      uliftSourceRepresentation sl2F4NaturalRep
    have hSource : sl2F4NaturalRep.Equiv ρLift :=
      uliftSourceRepresentationEquiv sl2F4NaturalRep
    rcases sl2F4_scalarExtensionEquiv_of_equiv (k := K) hSource with ⟨eLift⟩
    -- Move the finite source carrier into the target universe before packaging realizability.
    exact Representation.isRealizableOver_of_equiv_scalarExtension ρLift (e.trans eLift)
  · have hEquiv :
        Nonempty (σ.Equiv
          (Representation.scalarExtension (k := K) sl2F4FrobeniusRep)) := by
      -- In the Frobenius case, the source tables have the squared parameter.
      apply sl2F4_equiv_of_elementary_toMatrix σ
        (Representation.scalarExtension (k := K) sl2F4FrobeniusRep) b bSrc
      · intro a
        calc
          LinearMap.toMatrix b b (σ (sl2F4Upper a)) =
              !![(1 : K), φ a; 0, 1] := hUpper a
          _ = !![(1 : K), algebraMap 𝔽₄ K (a ^ 2); 0, 1] := by rw [hφfrob a]
          _ = LinearMap.toMatrix bSrc bSrc
              ((Representation.scalarExtension (k := K) sl2F4FrobeniusRep)
                (sl2F4Upper a)) :=
                (sl2F4FrobeniusRep_scalarExtension_upper_toMatrix (K := K) a).symm
      · intro a
        calc
          LinearMap.toMatrix b b (σ (sl2F4Lower a)) =
              !![(1 : K), 0; φ a, 1] := hLower a
          _ = !![(1 : K), 0; algebraMap 𝔽₄ K (a ^ 2), 1] := by rw [hφfrob a]
          _ = LinearMap.toMatrix bSrc bSrc
              ((Representation.scalarExtension (k := K) sl2F4FrobeniusRep)
                (sl2F4Lower a)) :=
                (sl2F4FrobeniusRep_scalarExtension_lower_toMatrix (K := K) a).symm
    rcases hEquiv with ⟨e⟩
    let ρLift : Representation 𝔽₄ (SL(2, 𝔽₄)) (ULift.{u} (Fin 2 → 𝔽₄)) :=
      uliftSourceRepresentation sl2F4FrobeniusRep
    have hSource : sl2F4FrobeniusRep.Equiv ρLift :=
      uliftSourceRepresentationEquiv sl2F4FrobeniusRep
    rcases sl2F4_scalarExtensionEquiv_of_equiv (k := K) hSource with ⟨eLift⟩
    -- The same universe-lift packaging works for the Frobenius-twisted source model.
    exact Representation.isRealizableOver_of_equiv_scalarExtension ρLift (e.trans eLift)

/-- Helper for Exercise 18-18.6-3: the rank-one classification frontier. Every
irreducible degree-`2` representation of `SL(2,𝔽₄)` over an extension field of `𝔽₄` should be
obtained by scalar extension from an `𝔽₄`-model. -/
theorem sl2F4_irreducible_degreeTwo_realizableOver_f4_core :
    ∀ {K : Type*} [Field K] [Algebra 𝔽₄ K]
      {V : Type*} [AddCommGroup V] [Module K V]
      (σ : Representation K (SL(2, 𝔽₄)) V) [σ.IsIrreducible],
      Module.finrank K V = 2 → Representation.IsRealizableOver 𝔽₄ σ := by
  intro K _ _ V _ _ σ _ hV
  -- The invariant-vector and Weyl-basis stages are now formalized; the remaining frontier is the
  -- upper-unipotent parameter normal form and the final source-model comparison.
  obtain ⟨v, hv0, hUpper⟩ := sl2F4_upperFixedVector_exists σ hV
  obtain ⟨b, hb0, hb1, hWeyl⟩ :=
    sl2F4_weylBasis_of_upperFixedVector σ hv0 hUpper hV
  have hUpper_b0 : ∀ a : 𝔽₄, σ (sl2F4Upper a) (b 0) = b 0 := by
    intro a
    rw [hb0, hUpper a]
  obtain ⟨lambdaParam, hUpperMatrix⟩ :=
    sl2F4_upperMatrix_unipotent_of_fixedBasis σ b hUpper_b0
  have hLambda_zero := sl2F4_upperMatrix_parameter_zero σ b hUpperMatrix
  have hLambda_add := sl2F4_upperMatrix_parameter_add σ b hUpperMatrix
  have hLowerMatrix :=
    sl2F4_lowerMatrix_unipotent_of_weylBasis σ b hWeyl hUpperMatrix
  have hLambda_one :=
    sl2F4_upperMatrix_parameter_one σ b hWeyl hUpperMatrix hLowerMatrix
  have hLambda_square_mul :
      ∀ (r : 𝔽₄ˣ) (a : 𝔽₄),
        lambdaParam ((r : 𝔽₄) ^ 2 * a) =
          lambdaParam ((r : 𝔽₄) ^ 2) * lambdaParam a :=
    -- Diagonal conjugation has been separated out as the square-multiplier part of
    -- multiplicativity; the remaining step only has to remove the square restriction in `𝔽₄`.
    sl2F4_upperMatrix_parameter_square_mul σ b hUpperMatrix hLambda_one
  have hF4_unit_square : ∀ {a : 𝔽₄}, a ≠ 0 → ∃ r : 𝔽₄ˣ, (r : 𝔽₄) ^ 2 = a := by
    -- This supplies the finite-field side condition needed to turn diagonal-conjugation
    -- identities for square parameters into arbitrary nonzero-parameter identities.
    intro a ha
    exact f4_exists_unit_sq_eq ha
  have hLambda_mul :
      ∀ a b : 𝔽₄, lambdaParam (a * b) = lambdaParam a * lambdaParam b := by
    -- The finite-field square-surjectivity removes the square restriction from the torus relation.
    exact f4_parameter_mul_of_square_mul lambdaParam hLambda_zero hLambda_square_mul
  obtain ⟨φ, hφ⟩ :=
    f4_ringHom_of_additive_squareMul_parameter lambdaParam hLambda_zero hLambda_add
      hLambda_one hLambda_square_mul
  have hφDichotomy :
      (∀ a : 𝔽₄, φ a = algebraMap 𝔽₄ K a) ∨
        (∀ a : 𝔽₄, φ a = algebraMap 𝔽₄ K (a ^ 2)) :=
    -- The finite-field dichotomy requested by the source route is now available; the remaining
    -- work is the representation-level comparison with the natural or Frobenius source model.
    f4_ringHom_eq_algebraMap_or_frobenius φ
  have hUpperφ : ∀ a : 𝔽₄,
      LinearMap.toMatrix b b (σ (sl2F4Upper a)) =
        !![(1 : K), φ a; 0, 1] := by
    intro a
    -- Replace the additive parameter by the packaged field embedding `φ`.
    rw [hUpperMatrix a, hφ a]
  have hLowerφ : ∀ a : 𝔽₄,
      LinearMap.toMatrix b b (σ (sl2F4Lower a)) =
        !![(1 : K), 0; φ a, 1] := by
    intro a
    -- The lower matrices use the same parameter, so the same replacement applies.
    rw [hLowerMatrix a, hφ a]
  -- Compare the generator tables with the natural or Frobenius source model, according to the
  -- finite-field dichotomy for `φ`.
  exact sl2F4_realizableOver_of_elementaryEmbeddingNormalForm σ b φ hUpperφ hLowerφ
    hφDichotomy

end Representation
