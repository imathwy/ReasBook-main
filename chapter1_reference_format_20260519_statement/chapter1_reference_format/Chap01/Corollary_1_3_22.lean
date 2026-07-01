import Mathlib
import chapter1_reference_format.Chap01.Remark_1_3_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Polynomial
open Polynomial

noncomputable section

attribute [local instance] Classical.decEq

/-- If `P ∈ 𝔽_p[X]` is irreducible, then `AdjoinRoot P`, i.e. `𝔽_p[X] / (P)`, is finite. -/
lemma adjoinRoot_finite_of_irreducible
    {p : ℕ} [Fact p.Prime] {P : (ZMod p)[X]} (hP : Irreducible P) :
    Finite (AdjoinRoot P) := by
  let _ : Module.Finite (ZMod p) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  exact Module.finite_of_finite (ZMod p)

instance {p : ℕ} [Fact p.Prime] {P : (ZMod p)[X]} (hP : Irreducible P) :
    Finite (AdjoinRoot P) :=
  adjoinRoot_finite_of_irreducible hP

/-- The finset of nonzero residue classes in `AdjoinRoot P = 𝔽_p[X] / (P)`. This is the
operational bridge from the canonical quotient owner to the finite product statements below. -/
noncomputable def adjoinRootNonzeroClasses
    {p : ℕ} [Fact p.Prime] (P : (ZMod p)[X]) (hP : Irreducible P) :
    Finset (AdjoinRoot P) :=
  let _ : Fintype (AdjoinRoot P) := @Fintype.ofFinite _ (adjoinRoot_finite_of_irreducible hP)
  Finset.univ.erase 0

section

variable {p : ℕ} [Fact p.Prime] (P : (ZMod p)[X]) (hP : Irreducible P)

/-- Corollary 1.3.22: if `P ∈ 𝔽_p[X]` is irreducible, then in the canonical quotient owner
`AdjoinRoot P = 𝔽_p[X] / (P)`, the polynomial `T^(q - 1) - 1`, where `q = #AdjoinRoot P`, factors
as the product of the linear factors `T - a` over all nonzero residue classes `a`. -/
-- Proof sketch: in `AdjoinRoot P`, `FiniteField.pow_card_sub_one_eq_one` identifies the nonzero
-- elements with the roots of `T^(#F - 1) - 1`, and
-- `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq` turns that root description into
-- the displayed factorization.
theorem adjoinRoot_X_pow_card_sub_one_sub_one_eq_prod_nonzero :
    (X ^ (Nat.card (AdjoinRoot P) - 1) - 1 : Polynomial (AdjoinRoot P)) =
      ∏ a ∈ adjoinRootNonzeroClasses P hP, (X - C a) := by
  letI : Fact (Irreducible P) := ⟨hP⟩
  letI : Fintype (AdjoinRoot P) := @Fintype.ofFinite _ (adjoinRoot_finite_of_irreducible hP)
  -- Work in the finite field `F = 𝔽_p[X] / (P)` and identify the target finset with
  -- `Finset.univ.erase 0`.
  suffices
      (X ^ (Fintype.card (AdjoinRoot P) - 1) - 1 : Polynomial (AdjoinRoot P)) =
        ∏ a ∈ Finset.univ.erase (0 : AdjoinRoot P), (X - C a) by
    simpa [adjoinRootNonzeroClasses, Nat.card_eq_fintype_card] using this
  have hqgt : 1 < Fintype.card (AdjoinRoot P) := Fintype.one_lt_card
  have hq : Fintype.card (AdjoinRoot P) = Fintype.card (AdjoinRoot P) - 1 + 1 := by
    omega
  -- The finite-field polynomial `X^q - X` is monic of degree `q`, so its roots determine it.
  have hmonic : Monic (X ^ Fintype.card (AdjoinRoot P) - X : Polynomial (AdjoinRoot P)) := by
    exact Polynomial.monic_X_pow_sub (p := (X : Polynomial (AdjoinRoot P))) (by
      simpa [Polynomial.degree_X] using
        (show (1 : WithBot ℕ) < (Fintype.card (AdjoinRoot P) : WithBot ℕ) by
          exact_mod_cast hqgt))
  have hnatDegree :
      (X ^ Fintype.card (AdjoinRoot P) - X : Polynomial (AdjoinRoot P)).natDegree =
        Fintype.card (AdjoinRoot P) := by
    refine Polynomial.natDegree_eq_of_degree_eq_some ?_
    rw [Polynomial.degree_sub_eq_left_of_degree_lt]
    · simp
    · simpa [Polynomial.degree_X, Polynomial.degree_X_pow] using
        (show (1 : WithBot ℕ) < (Fintype.card (AdjoinRoot P) : WithBot ℕ) by
          exact_mod_cast hqgt)
  have hroots :
      (X ^ Fintype.card (AdjoinRoot P) - X : Polynomial (AdjoinRoot P)).roots.card =
        (X ^ Fintype.card (AdjoinRoot P) - X : Polynomial (AdjoinRoot P)).natDegree := by
    simpa [FiniteField.roots_X_pow_card_sub_X (K := AdjoinRoot P)] using hnatDegree.symm
  have hall :
      (∏ a : AdjoinRoot P, (X - C a : Polynomial (AdjoinRoot P))) =
        (X ^ Fintype.card (AdjoinRoot P) - X : Polynomial (AdjoinRoot P)) := by
    simpa [FiniteField.roots_X_pow_card_sub_X (K := AdjoinRoot P)] using
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
        (p := (X ^ Fintype.card (AdjoinRoot P) - X : Polynomial (AdjoinRoot P))) hmonic hroots)
  have hpow :
      (X ^ (Fintype.card (AdjoinRoot P) - 1 + 1) : Polynomial (AdjoinRoot P)) =
        X * X ^ (Fintype.card (AdjoinRoot P) - 1) := by
    simpa using
      (pow_succ' (X : Polynomial (AdjoinRoot P)) (Fintype.card (AdjoinRoot P) - 1))
  have hfactorX :
      (X ^ Fintype.card (AdjoinRoot P) - X : Polynomial (AdjoinRoot P)) =
        X * (X ^ (Fintype.card (AdjoinRoot P) - 1) - 1) := by
    conv_lhs =>
      rw [hq]
    rw [hpow, mul_sub]
    simp
  -- Split off the zero factor from `∏ a : F, (X - a)` and cancel the common factor `X`.
  have hall' :
      X * (∏ a ∈ Finset.univ.erase (0 : AdjoinRoot P), (X - C a)) =
        X * (X ^ (Fintype.card (AdjoinRoot P) - 1) - 1 : Polynomial (AdjoinRoot P)) := by
    calc
      X * (∏ a ∈ Finset.univ.erase (0 : AdjoinRoot P), (X - C a))
          = (X - C (0 : AdjoinRoot P)) *
              ∏ a ∈ Finset.univ.erase (0 : AdjoinRoot P), (X - C a) := by
              simp
      _ = ∏ a : AdjoinRoot P, (X - C a : Polynomial (AdjoinRoot P)) := by
            exact
              (Finset.mul_prod_erase
                (s := Finset.univ)
                (f := fun a : AdjoinRoot P ↦ (X - C a : Polynomial (AdjoinRoot P)))
                (a := 0) (by simp))
      _ = (X ^ Fintype.card (AdjoinRoot P) - X : Polynomial (AdjoinRoot P)) := hall
      _ = X * (X ^ (Fintype.card (AdjoinRoot P) - 1) - 1 : Polynomial (AdjoinRoot P)) := hfactorX
  exact mul_left_cancel₀
      (show (X : Polynomial (AdjoinRoot P)) ≠ 0 by exact X_ne_zero) <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hall'.symm

/-- In the finite field `AdjoinRoot P = 𝔽_p[X] / (P)`, the product of all nonzero residue classes
is `-1`. -/
-- Proof sketch: this is the nonzero-elements form of
-- `FiniteField.prod_univ_units_id_eq_neg_one`, transported across
-- `Units.mk0 : {a : AdjoinRoot P // a ≠ 0} ≃ (AdjoinRoot P)ˣ`.
theorem adjoinRoot_prod_nonzero_eq_neg_one :
    (∏ a ∈ adjoinRootNonzeroClasses P hP, a) = (-1 : AdjoinRoot P) := by
  letI : Fact (Irreducible P) := ⟨hP⟩
  letI : Fintype (AdjoinRoot P) := @Fintype.ofFinite _ (adjoinRoot_finite_of_irreducible hP)
  -- Evaluate the factorization from the first theorem at `T = 0`.
  suffices (∏ a ∈ Finset.univ.erase (0 : AdjoinRoot P), a) = (-1 : AdjoinRoot P) by
    simpa [adjoinRootNonzeroClasses] using this
  have hqgt : 1 < Fintype.card (AdjoinRoot P) := Fintype.one_lt_card
  have hsubpos : 0 < Fintype.card (AdjoinRoot P) - 1 := Nat.sub_pos_of_lt hqgt
  have hzero_pow : (0 : AdjoinRoot P) ^ (Fintype.card (AdjoinRoot P) - 1) = 0 := by
    exact zero_pow (Nat.ne_of_gt hsubpos)
  have hfactor :
      (X ^ (Fintype.card (AdjoinRoot P) - 1) - 1 : Polynomial (AdjoinRoot P)) =
        ∏ a ∈ Finset.univ.erase (0 : AdjoinRoot P), (X - C a) := by
    simpa [adjoinRootNonzeroClasses, Nat.card_eq_fintype_card] using
      adjoinRoot_X_pow_card_sub_one_sub_one_eq_prod_nonzero (P := P) hP
  have heval : (-1 : AdjoinRoot P) = ∏ a ∈ Finset.univ.erase (0 : AdjoinRoot P), -a := by
    -- The left-hand side evaluates to `-1`, and each linear factor evaluates to `-a`.
    have heval_raw := congrArg (fun Q : Polynomial (AdjoinRoot P) ↦ Q.eval 0) hfactor
    simpa [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, hzero_pow, sub_eq_add_neg, zero_add] using heval_raw
  have hneg_prod :
      (∏ a ∈ Finset.univ.erase (0 : AdjoinRoot P), -a) =
        (-1 : AdjoinRoot P) ^ ((Finset.univ.erase (0 : AdjoinRoot P)).card) *
          ∏ a ∈ Finset.univ.erase (0 : AdjoinRoot P), a := by
    -- Pull out one factor `-1` from every term of the finite product.
    calc
      (∏ a ∈ Finset.univ.erase (0 : AdjoinRoot P), -a)
          = ∏ a ∈ Finset.univ.erase (0 : AdjoinRoot P), (-1 : AdjoinRoot P) * a := by
              refine Finset.prod_congr rfl ?_
              intro a ha
              exact neg_eq_neg_one_mul a
      _ = (∏ _a ∈ Finset.univ.erase (0 : AdjoinRoot P), (-1 : AdjoinRoot P)) *
            ∏ a ∈ Finset.univ.erase (0 : AdjoinRoot P), a := by
              rw [Finset.prod_mul_distrib]
      _ = (-1 : AdjoinRoot P) ^ ((Finset.univ.erase (0 : AdjoinRoot P)).card) *
            ∏ a ∈ Finset.univ.erase (0 : AdjoinRoot P), a := by
              rw [Finset.prod_const]
  have hpow_neg_one : (-1 : AdjoinRoot P) ^ (Fintype.card (AdjoinRoot P) - 1) = 1 := by
    exact FiniteField.pow_card_sub_one_eq_one
      (-1 : AdjoinRoot P) (neg_ne_zero.mpr one_ne_zero)
  have hcard_erase :
      (Finset.univ.erase (0 : AdjoinRoot P)).card = Fintype.card (AdjoinRoot P) - 1 := by
    exact Finset.card_erase_of_mem (s := Finset.univ) (a := (0 : AdjoinRoot P)) (by simp)
  simpa [hneg_prod, hcard_erase, hpow_neg_one] using heval.symm

end
