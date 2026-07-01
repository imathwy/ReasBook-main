import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial

universe u

noncomputable section

variable {K : Type u} [CommSemiring K]

/-- Helper for Example 1.3.55: the first orbit representative has total degree `6`. -/
lemma shape_321_witness0_card :
    ({(0 : Fin 3), 0, 0, 1, 2, 2} : Multiset (Fin 3)).card = 6 := by
  rfl

/-- Helper for Example 1.3.55: the second orbit representative has total degree `6`. -/
lemma shape_321_witness1_card :
    ({(1 : Fin 3), 1, 1, 0, 2, 2} : Multiset (Fin 3)).card = 6 := by
  rfl

/-- Helper for Example 1.3.55: the third orbit representative has total degree `6`. -/
lemma shape_321_witness2_card :
    ({(2 : Fin 3), 2, 2, 1, 0, 0} : Multiset (Fin 3)).card = 6 := by
  rfl

/-- Helper for Example 1.3.55: the fourth orbit representative has total degree `6`. -/
lemma shape_321_witness3_card :
    ({(0 : Fin 3), 0, 0, 2, 1, 1} : Multiset (Fin 3)).card = 6 := by
  rfl

/-- Helper for Example 1.3.55: the fifth orbit representative has total degree `6`. -/
lemma shape_321_witness4_card :
    ({(1 : Fin 3), 1, 1, 2, 0, 0} : Multiset (Fin 3)).card = 6 := by
  rfl

/-- Helper for Example 1.3.55: the sixth orbit representative has total degree `6`. -/
lemma shape_321_witness5_card :
    ({(2 : Fin 3), 2, 2, 0, 1, 1} : Multiset (Fin 3)).card = 6 := by
  rfl

/-- Helper for Example 1.3.55: the squarefree representative has total degree `3`. -/
lemma shape_111_witness_card :
    ({(0 : Fin 3), 1, 2} : Multiset (Fin 3)).card = 3 := by
  rfl

/-- Helper for Example 1.3.55: the first orbit representative has partition `(3,2,1)`. -/
lemma shape_321_witness0_partition :
    Nat.Partition.ofSym
        (Sym.mk ({(0 : Fin 3), 0, 0, 1, 2, 2} : Multiset (Fin 3)) shape_321_witness0_card) =
      Nat.Partition.ofMultiset ({3, 2, 1} : Multiset ℕ) := by
  rw [Nat.Partition.ext_iff]
  decide

/-- Helper for Example 1.3.55: the second orbit representative has partition `(3,2,1)`. -/
lemma shape_321_witness1_partition :
    Nat.Partition.ofSym
        (Sym.mk ({(1 : Fin 3), 1, 1, 0, 2, 2} : Multiset (Fin 3)) shape_321_witness1_card) =
      Nat.Partition.ofMultiset ({3, 2, 1} : Multiset ℕ) := by
  rw [Nat.Partition.ext_iff]
  decide

/-- Helper for Example 1.3.55: the third orbit representative has partition `(3,2,1)`. -/
lemma shape_321_witness2_partition :
    Nat.Partition.ofSym
        (Sym.mk ({(2 : Fin 3), 2, 2, 1, 0, 0} : Multiset (Fin 3)) shape_321_witness2_card) =
      Nat.Partition.ofMultiset ({3, 2, 1} : Multiset ℕ) := by
  rw [Nat.Partition.ext_iff]
  decide

/-- Helper for Example 1.3.55: the fourth orbit representative has partition `(3,2,1)`. -/
lemma shape_321_witness3_partition :
    Nat.Partition.ofSym
        (Sym.mk ({(0 : Fin 3), 0, 0, 2, 1, 1} : Multiset (Fin 3)) shape_321_witness3_card) =
      Nat.Partition.ofMultiset ({3, 2, 1} : Multiset ℕ) := by
  rw [Nat.Partition.ext_iff]
  decide

/-- Helper for Example 1.3.55: the fifth orbit representative has partition `(3,2,1)`. -/
lemma shape_321_witness4_partition :
    Nat.Partition.ofSym
        (Sym.mk ({(1 : Fin 3), 1, 1, 2, 0, 0} : Multiset (Fin 3)) shape_321_witness4_card) =
      Nat.Partition.ofMultiset ({3, 2, 1} : Multiset ℕ) := by
  rw [Nat.Partition.ext_iff]
  decide

/-- Helper for Example 1.3.55: the sixth orbit representative has partition `(3,2,1)`. -/
lemma shape_321_witness5_partition :
    Nat.Partition.ofSym
        (Sym.mk ({(2 : Fin 3), 2, 2, 0, 1, 1} : Multiset (Fin 3)) shape_321_witness5_card) =
      Nat.Partition.ofMultiset ({3, 2, 1} : Multiset ℕ) := by
  rw [Nat.Partition.ext_iff]
  decide

/-- Helper for Example 1.3.55: the squarefree representative has partition `(1,1,1)`. -/
lemma shape_111_witness_partition :
    Nat.Partition.ofSym
        (Sym.mk ({(0 : Fin 3), 1, 2} : Multiset (Fin 3)) shape_111_witness_card) =
      Nat.Partition.ofMultiset ({1, 1, 1} : Multiset ℕ) := by
  rw [Nat.Partition.ext_iff]
  decide

/-- Helper for Example 1.3.55: the six orbit representatives indexed in the theorem order. -/
def shape_321_witnesses :
    Fin 6 →
      {s : Sym (Fin 3) 6 //
        Nat.Partition.ofSym s = Nat.Partition.ofMultiset ({3, 2, 1} : Multiset ℕ)}
  | 0 =>
      ⟨Sym.mk ({(0 : Fin 3), 0, 0, 1, 2, 2} : Multiset (Fin 3)) shape_321_witness0_card,
        shape_321_witness0_partition⟩
  | 1 =>
      ⟨Sym.mk ({(1 : Fin 3), 1, 1, 0, 2, 2} : Multiset (Fin 3)) shape_321_witness1_card,
        shape_321_witness1_partition⟩
  | 2 =>
      ⟨Sym.mk ({(2 : Fin 3), 2, 2, 1, 0, 0} : Multiset (Fin 3)) shape_321_witness2_card,
        shape_321_witness2_partition⟩
  | 3 =>
      ⟨Sym.mk ({(0 : Fin 3), 0, 0, 2, 1, 1} : Multiset (Fin 3)) shape_321_witness3_card,
        shape_321_witness3_partition⟩
  | 4 =>
      ⟨Sym.mk ({(1 : Fin 3), 1, 1, 2, 0, 0} : Multiset (Fin 3)) shape_321_witness4_card,
        shape_321_witness4_partition⟩
  | 5 =>
      ⟨Sym.mk ({(2 : Fin 3), 2, 2, 0, 1, 1} : Multiset (Fin 3)) shape_321_witness5_card,
        shape_321_witness5_partition⟩

/-- Helper for Example 1.3.55: the unique squarefree shape witness. -/
def shape_111_witness :
    {s : Sym (Fin 3) 3 //
      Nat.Partition.ofSym s = Nat.Partition.ofMultiset ({1, 1, 1} : Multiset ℕ)} :=
  ⟨Sym.mk ({(0 : Fin 3), 1, 2} : Multiset (Fin 3)) shape_111_witness_card,
    shape_111_witness_partition⟩

/-- Helper for Example 1.3.55: there are exactly six shape `(3,2,1)` symmetric monomials in
three variables. -/
lemma shape_321_subtype_card :
    Fintype.card
        {s : Sym (Fin 3) 6 //
          Nat.Partition.ofSym s = Nat.Partition.ofMultiset ({3, 2, 1} : Multiset ℕ)} = 6 := by
  native_decide

/-- Helper for Example 1.3.55: the six explicit representatives exhaust the shape `(3,2,1)`
subtype. -/
lemma shape_321_witnesses_bijective :
    Function.Bijective shape_321_witnesses := by
  native_decide

/-- Helper for Example 1.3.55: the shape `(1,1,1)` subtype has exactly one element. -/
lemma shape_111_subtype_card :
    Fintype.card
        {s : Sym (Fin 3) 3 //
          Nat.Partition.ofSym s = Nat.Partition.ofMultiset ({1, 1, 1} : Multiset ℕ)} = 1 := by
  native_decide

/-- Helper for Example 1.3.55: the squarefree shape subtype is a singleton. -/
lemma shape_111_subsingleton :
    Subsingleton {s : Sym (Fin 3) 3 //
      Nat.Partition.ofSym s = Nat.Partition.ofMultiset ({1, 1, 1} : Multiset ℕ)} := by
  have hle :
      Fintype.card
          {s : Sym (Fin 3) 3 //
            Nat.Partition.ofSym s = Nat.Partition.ofMultiset ({1, 1, 1} : Multiset ℕ)} ≤ 1 := by
    have hcard := shape_111_subtype_card
    omega
  exact (Fintype.card_le_one_iff_subsingleton).mp hle

/-- Helper for Example 1.3.55: the first explicit shape `(3,2,1)` witness gives the monomial
`X 0 ^ 3 * X 1 * X 2 ^ 2`. -/
lemma shape_321_witness0_prod :
    (((shape_321_witnesses 0).1.1.map X).prod : MvPolynomial (Fin 3) K) =
      X (0 : Fin 3) ^ 3 * X (1 : Fin 3) * X (2 : Fin 3) ^ 2 := by
  simp [shape_321_witnesses, pow_succ]
  ac_rfl

/-- Helper for Example 1.3.55: the second explicit shape `(3,2,1)` witness gives the monomial
`X 1 ^ 3 * X 0 * X 2 ^ 2`. -/
lemma shape_321_witness1_prod :
    (((shape_321_witnesses 1).1.1.map X).prod : MvPolynomial (Fin 3) K) =
      X (1 : Fin 3) ^ 3 * X (0 : Fin 3) * X (2 : Fin 3) ^ 2 := by
  simp [shape_321_witnesses, pow_succ]
  ac_rfl

/-- Helper for Example 1.3.55: the third explicit shape `(3,2,1)` witness gives the monomial
`X 2 ^ 3 * X 1 * X 0 ^ 2`. -/
lemma shape_321_witness2_prod :
    (((shape_321_witnesses 2).1.1.map X).prod : MvPolynomial (Fin 3) K) =
      X (2 : Fin 3) ^ 3 * X (1 : Fin 3) * X (0 : Fin 3) ^ 2 := by
  simp [shape_321_witnesses, pow_succ]
  ac_rfl

/-- Helper for Example 1.3.55: the fourth explicit shape `(3,2,1)` witness gives the monomial
`X 0 ^ 3 * X 2 * X 1 ^ 2`. -/
lemma shape_321_witness3_prod :
    (((shape_321_witnesses 3).1.1.map X).prod : MvPolynomial (Fin 3) K) =
      X (0 : Fin 3) ^ 3 * X (2 : Fin 3) * X (1 : Fin 3) ^ 2 := by
  simp [shape_321_witnesses, pow_succ]
  ac_rfl

/-- Helper for Example 1.3.55: the fifth explicit shape `(3,2,1)` witness gives the monomial
`X 1 ^ 3 * X 2 * X 0 ^ 2`. -/
lemma shape_321_witness4_prod :
    (((shape_321_witnesses 4).1.1.map X).prod : MvPolynomial (Fin 3) K) =
      X (1 : Fin 3) ^ 3 * X (2 : Fin 3) * X (0 : Fin 3) ^ 2 := by
  simp [shape_321_witnesses, pow_succ]
  ac_rfl

/-- Helper for Example 1.3.55: the sixth explicit shape `(3,2,1)` witness gives the monomial
`X 2 ^ 3 * X 0 * X 1 ^ 2`. -/
lemma shape_321_witness5_prod :
    (((shape_321_witnesses 5).1.1.map X).prod : MvPolynomial (Fin 3) K) =
      X (2 : Fin 3) ^ 3 * X (0 : Fin 3) * X (1 : Fin 3) ^ 2 := by
  simp [shape_321_witnesses, pow_succ]
  ac_rfl

/-- Helper for Example 1.3.55: the unique shape `(1,1,1)` witness gives the squarefree monomial
`X 0 * X 1 * X 2`. -/
lemma shape_111_witness_prod :
    (((shape_111_witness.1.1.map X).prod : MvPolynomial (Fin 3) K)) =
      (X (0 : Fin 3) * X (1 : Fin 3) * X (2 : Fin 3) : MvPolynomial (Fin 3) K) := by
  simp [shape_111_witness, mul_assoc]

-- Proof sketch: `msymm (Fin 3) K` is the canonical owner for the symmetrization of a monomial by
-- its exponent partition. For the partition `(3, 2, 1)`, the defining sum has one term for each
-- permutation of the exponents across the three variables, giving the six distinct monomials.
/-- Example 1.3.55 (1): the symmetrization of `X₁^3 X₂ X₃^2` is the monomial symmetric polynomial
attached to the partition `(3, 2, 1)`, namely the sum of the six distinct monomials obtained by
permuting the variables. -/
theorem symmetrization_of_X0_cubed_mul_X1_mul_X2_squared :
    msymm (Fin 3) K (Nat.Partition.ofMultiset ({3, 2, 1} : Multiset ℕ)) =
      X (0 : Fin 3) ^ 3 * X (1 : Fin 3) * X (2 : Fin 3) ^ 2
        + X (1 : Fin 3) ^ 3 * X (0 : Fin 3) * X (2 : Fin 3) ^ 2
        + X (2 : Fin 3) ^ 3 * X (1 : Fin 3) * X (0 : Fin 3) ^ 2
        + X (0 : Fin 3) ^ 3 * X (2 : Fin 3) * X (1 : Fin 3) ^ 2
        + X (1 : Fin 3) ^ 3 * X (2 : Fin 3) * X (0 : Fin 3) ^ 2
        + X (2 : Fin 3) ^ 3 * X (0 : Fin 3) * X (1 : Fin 3) ^ 2 := by
  -- Rewrite the defining sum through the six explicit orbit representatives.
  rw [MvPolynomial.msymm]
  have hsum :
      (∑ s : {a : Sym (Fin 3) 6 //
          Nat.Partition.ofSym a = Nat.Partition.ofMultiset ({3, 2, 1} : Multiset ℕ)},
        ((s.1.1.map X).prod : MvPolynomial (Fin 3) K)) =
        ∑ i : Fin 6, (((shape_321_witnesses i).1.1.map X).prod : MvPolynomial (Fin 3) K) := by
    symm
    exact Fintype.sum_equiv
      (Equiv.ofBijective shape_321_witnesses shape_321_witnesses_bijective)
      (fun i => (((shape_321_witnesses i).1.1.map X).prod : MvPolynomial (Fin 3) K))
      (fun s => ((s.1.1.map X).prod : MvPolynomial (Fin 3) K))
      (fun _ => rfl)
  calc
    (∑ s : {a : Sym (Fin 3) 6 //
        Nat.Partition.ofSym a = Nat.Partition.ofMultiset ({3, 2, 1} : Multiset ℕ)},
      ((s.1.1.map X).prod : MvPolynomial (Fin 3) K))
        = ∑ i : Fin 6, (((shape_321_witnesses i).1.1.map X).prod : MvPolynomial (Fin 3) K) := hsum
    _ = X (0 : Fin 3) ^ 3 * X (1 : Fin 3) * X (2 : Fin 3) ^ 2
          + X (1 : Fin 3) ^ 3 * X (0 : Fin 3) * X (2 : Fin 3) ^ 2
          + X (2 : Fin 3) ^ 3 * X (1 : Fin 3) * X (0 : Fin 3) ^ 2
          + X (0 : Fin 3) ^ 3 * X (2 : Fin 3) * X (1 : Fin 3) ^ 2
          + X (1 : Fin 3) ^ 3 * X (2 : Fin 3) * X (0 : Fin 3) ^ 2
          + X (2 : Fin 3) ^ 3 * X (0 : Fin 3) * X (1 : Fin 3) ^ 2 := by
            rw [Fin.sum_univ_six]
            rw [shape_321_witness0_prod, shape_321_witness1_prod, shape_321_witness2_prod,
              shape_321_witness3_prod, shape_321_witness4_prod, shape_321_witness5_prod]

-- Proof sketch: for the partition `(1, 1, 1)`, there is only one monomial in three variables
-- having that exponent multiset, namely `X 0 * X 1 * X 2`.
/-- Example 1.3.55 (2): the symmetrization of `X₁ X₂ X₃` is the monomial symmetric polynomial
attached to the partition `(1, 1, 1)`, which is just `X₁ X₂ X₃`. -/
theorem symmetrization_of_X0_mul_X1_mul_X2 :
    msymm (Fin 3) K (Nat.Partition.ofMultiset ({1, 1, 1} : Multiset ℕ)) =
      (X (0 : Fin 3) * X (1 : Fin 3) * X (2 : Fin 3) : MvPolynomial (Fin 3) K) := by
  -- Collapse the defining sum using that the shape `(1,1,1)` subtype is a singleton.
  rw [MvPolynomial.msymm]
  letI :
      Subsingleton {a : Sym (Fin 3) 3 //
        Nat.Partition.ofSym a = Nat.Partition.ofMultiset ({1, 1, 1} : Multiset ℕ)} :=
    shape_111_subsingleton
  calc
    (∑ s : {a : Sym (Fin 3) 3 //
        Nat.Partition.ofSym a = Nat.Partition.ofMultiset ({1, 1, 1} : Multiset ℕ)},
      ((s.1.1.map X).prod : MvPolynomial (Fin 3) K))
        = (((shape_111_witness.1.1.map X).prod : MvPolynomial (Fin 3) K)) := by
            simpa using
              (Fintype.sum_subsingleton
                (fun s : {a : Sym (Fin 3) 3 //
                    Nat.Partition.ofSym a =
                      Nat.Partition.ofMultiset ({1, 1, 1} : Multiset ℕ)} =>
                  ((s.1.1.map X).prod : MvPolynomial (Fin 3) K))
                shape_111_witness)
    _ = (X (0 : Fin 3) * X (1 : Fin 3) * X (2 : Fin 3) : MvPolynomial (Fin 3) K) := by
          exact shape_111_witness_prod
