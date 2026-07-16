import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_111_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_111_4

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u v

section

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]

local notation "RFix" => FixedPoints.subring R G

/- Domain-style sampling for Remark 15.111.5:
- primary domain: invariant-theoretic fixed-point quotients for finite group actions when `|G|` is
  invertible
- sampled owner declarations:
  `fixedSubringQuotientToFixedQuotient`,
  `fixedSubringFixedQuotient`,
  `RingEquiv.ofBijective`,
  `Nat.card`
- best owner abstraction: the source-facing owner is still the canonical map
  `fixedSubringQuotientToFixedQuotient J` from `Lemma_15_111_4`; once bijectivity is proved, the
  canonical derived API is the induced ring equivalence
- primitive data: the ideal `J : Ideal RFix` and the invertibility hypothesis on `|G|`
- derived API: bijectivity of the canonical map and the resulting ring equivalence

Layer triage:
- `source-facing`: bijectivity of the canonical map `(R^G)/J → (R / JR)^G`
- `core/canonical`: `fixedSubringQuotientToFixedQuotient` from `Lemma_15_111_4`
- `bridge/view`: `RingEquiv.ofBijective` packaging that canonical map as an isomorphism

The public finiteness assumption should be `[Finite G]`; the proof may introduce a local
`Fintype` instance, but the theorem statement only depends on `Nat.card G`.
-/

-- Proof sketch: use the averaging operator `|G|⁻¹ ∑ g∈G g` on `R / JR`. When `|G|` is invertible
-- in `R`, averaging projects onto the fixed subring and gives an inverse to the canonical map
-- from `(R^G)/J`.
/-- Helper for Remark 15.111.5: natural-number scalars are fixed by the action. -/
private theorem natCast_fixed (n : ℕ) (g : G) :
    g • (n : R) = (n : R) := by
  induction n with
  | zero =>
      simp
  | succ n hn =>
      rw [Nat.cast_add, Nat.cast_one]
      simpa [smul_add, hn, add_comm, add_left_comm, add_assoc]

/-- Helper for Remark 15.111.5: a unit equal to a natural scalar is fixed by the group action. -/
private theorem unit_fixed_of_natCast_eq (u : Rˣ) (n : ℕ) (hu : (u : R) = n) :
    ∀ g : G, g • (u : R) = (u : R) := by
  -- Natural-number scalars are preserved by every semiring automorphism coming from the action.
  intro g
  simpa [hu] using natCast_fixed (R := R) (G := G) n g

/-- Helper for Remark 15.111.5: the inverse of a unit equal to a natural scalar is also fixed. -/
private theorem unit_inv_fixed_of_natCast_eq (u : Rˣ) (n : ℕ) (hu : (u : R) = n) :
    ∀ g : G, g • ((↑u⁻¹ : R)) = ↑u⁻¹ := by
  -- Map the unit through the action ring homomorphism and identify it from its value.
  intro g
  have hmap :
      Units.map (MulSemiringAction.toRingHom G R g).toMonoidHom u = u := by
    apply Units.ext
    simpa [hu] using unit_fixed_of_natCast_eq (R := R) (G := G) u n hu g
  simpa using congrArg (fun v : Rˣ ↦ ((v⁻¹ : Rˣ) : R)) hmap

/-- Helper for Remark 15.111.5: if `|G|` is a unit in `R`, then it is already a unit in `R^G`. -/
private theorem isUnit_card_fixedSubring (h_card : IsUnit (Nat.card G : R)) :
    IsUnit (Nat.card G : RFix) := by
  rcases h_card with ⟨u, hu⟩
  -- Build the unit inside the fixed subring from the ambient unit and its fixed inverse.
  refine ⟨?_, ?_⟩
  · refine
      { val := ⟨(u : R), unit_fixed_of_natCast_eq (R := R) (G := G) u (Nat.card G) hu⟩
        inv := ⟨(↑u⁻¹ : R), unit_inv_fixed_of_natCast_eq (R := R) (G := G) u (Nat.card G) hu⟩
        val_inv := Subtype.ext (by simp)
        inv_val := Subtype.ext (by simp) }
  · apply Subtype.ext
    simpa using hu

/-- Helper for Remark 15.111.5: the image of `|G|` remains a unit in the fixed quotient. -/
private theorem isUnit_card_fixedSubringQuotient
    (J : Ideal RFix) (h_card : IsUnit (Nat.card G : R)) :
    IsUnit (Nat.card G : RFix ⧸ J) := by
  -- Map the fixed-subring unit through the quotient homomorphism.
  exact (isUnit_card_fixedSubring (R := R) (G := G) h_card).map (Ideal.Quotient.mk J)

/-- Helper for Remark 15.111.5: the first lower coefficient of `(X - C z)^n` is `-nz`. -/
private theorem esymm_replicate_one (A : Type*) [CommRing A] (n : ℕ) (z : A) :
    (Multiset.replicate n z).esymm 1 = (n : A) * z := by
  -- The `1`-element submultisets are exactly the singleton copies of `z`, so the symmetric sum is
  -- the sum of `n` copies of `z`.
  rw [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
  simp [nsmul_eq_mul, mul_comm]

/-- Helper for Remark 15.111.5: the coefficient of degree `n - 1` in `(X - C z)^n` is `-nz`. -/
private theorem coeff_pred_X_sub_C_pow (A : Type*) [CommRing A] {n : ℕ} (hn : 0 < n) (z : A) :
    ((X - C z) ^ n).coeff (n - 1) = - (n : A) * z := by
  -- Rewrite the power as a repeated product of linear factors and specialize Vieta at degree
  -- `n - 1`.
  have hcoeff :=
    Multiset.prod_X_sub_C_coeff (s := Multiset.replicate n z) (k := n - 1)
      (by simpa using Nat.sub_le n 1)
  have hsub : n - (n - 1) = 1 := by
    omega
  -- The exponent `n - (n - 1)` is `1`, and the relevant elementary symmetric term is the
  -- replicate computation above.
  simpa [Multiset.prod_replicate, hsub, esymm_replicate_one (A := A) n z, pow_one,
    mul_comm, mul_left_comm, mul_assoc] using hcoeff

/-- Helper for Remark 15.111.5: if `|G|` is a unit, then every fixed quotient class lifts. -/
private theorem fixedSubringQuotientToFixedQuotient_surjective_of_isUnit_card
    (J : Ideal RFix) (h_card : IsUnit (Nat.card G : R)) :
    Function.Surjective (fixedSubringQuotientToFixedQuotient J) := by
  intro b
  obtain ⟨P, -, hPmap⟩ :=
    exists_monic_polynomial_over_fixedSubringQuotient_map_eq_X_sub_C_pow
      (R := R) (G := G) (J := J) b
  rcases isUnit_card_fixedSubringQuotient (R := R) (G := G) (J := J) h_card with ⟨u, hu⟩
  let v : (fixedSubringFixedQuotient J)ˣ :=
    Units.map (fixedSubringQuotientToFixedQuotient J).toMonoidHom u
  have hv : ((v : (fixedSubringFixedQuotient J)ˣ) : fixedSubringFixedQuotient J) =
      (Nat.card G : fixedSubringFixedQuotient J) := by
    -- Map the unit equality for `|G|` from the source quotient into the fixed quotient.
    change (fixedSubringQuotientToFixedQuotient J) (u : RFix ⧸ J) =
      (Nat.card G : fixedSubringFixedQuotient J)
    simpa [hu] using congrArg (fixedSubringQuotientToFixedQuotient J) hu
  have hcoeff :=
    congrArg
      (fun p : Polynomial (fixedSubringFixedQuotient J) ↦ p.coeff (Nat.card G - 1))
      hPmap
  have hcoeff_eq :
      (fixedSubringQuotientToFixedQuotient J) (P.coeff (Nat.card G - 1)) =
        - (Nat.card G : fixedSubringFixedQuotient J) * b := by
    -- Comparing the `|G| - 1` coefficient isolates the linear term in `b`.
    simpa [Polynomial.coeff_map,
      coeff_pred_X_sub_C_pow (A := fixedSubringFixedQuotient J) (hn := Nat.card_pos) b] using
      hcoeff
  refine ⟨(↑u⁻¹ : RFix ⧸ J) * (-(P.coeff (Nat.card G - 1))), ?_⟩
  -- Multiply the coefficient identity by the inverse unit to solve explicitly for `b`.
  calc
    fixedSubringQuotientToFixedQuotient J
        ((↑u⁻¹ : RFix ⧸ J) * (-(P.coeff (Nat.card G - 1)))) =
      (↑v⁻¹ : fixedSubringFixedQuotient J) *
        (-(fixedSubringQuotientToFixedQuotient J (P.coeff (Nat.card G - 1)))) := by
          simp [v, map_mul]
    _ = (↑v⁻¹ : fixedSubringFixedQuotient J) *
        ((Nat.card G : fixedSubringFixedQuotient J) * b) := by
          rw [hcoeff_eq]
          simp
    _ = (↑v⁻¹ : fixedSubringFixedQuotient J) * ((v : (fixedSubringFixedQuotient J)ˣ) * b) := by
          rw [hv]
    _ = b := by
          simp

/-- Helper for Remark 15.111.5: if `|G|` is a unit, then the canonical fixed quotient map has
trivial kernel. -/
private theorem fixedSubringQuotientToFixedQuotient_injective_of_isUnit_card
    (J : Ideal RFix) (h_card : IsUnit (Nat.card G : R)) :
    Function.Injective (fixedSubringQuotientToFixedQuotient J) := by
  intro x y hxy
  have hker :
      x - y ∈ RingHom.ker (fixedSubringQuotientToFixedQuotient J) := by
    -- Equality of images says that the difference lands in the kernel.
    simpa [RingHom.mem_ker, map_sub, hxy]
  have hzero_of_mem_ker :
      ∀ a : RingHom.ker (fixedSubringQuotientToFixedQuotient J), a.1 = 0 := by
    intro a
    rcases isUnit_card_fixedSubringQuotient (R := R) (G := G) (J := J) h_card with ⟨u, hu⟩
    have hpow :=
      kernelElement_X_sub_pow_eq_X_pow (R := R) (G := G) (J := J) a
    have hcoeff :=
      congrArg (fun p : Polynomial (RFix ⧸ J) ↦ p.coeff (Nat.card G - 1)) hpow
    have hcoeff_rhs : (X ^ Nat.card G : Polynomial (RFix ⧸ J)).coeff (Nat.card G - 1) = 0 := by
      -- The monomial `X ^ |G|` has no `|G| - 1` coefficient.
      have hne : Nat.card G - 1 ≠ Nat.card G := by
        exact Nat.ne_of_lt (Nat.sub_lt (Nat.card_pos) zero_lt_one)
      simp [Polynomial.coeff_X_pow, hne]
    have hmul_zero_neg : - (Nat.card G : RFix ⧸ J) * a.1 = 0 := by
      -- The coefficient comparison gives `-(|G|) * a = 0`.
      simpa [coeff_pred_X_sub_C_pow (A := RFix ⧸ J) (hn := Nat.card_pos) a.1, hcoeff_rhs] using
        hcoeff
    have hmul_zero : (Nat.card G : RFix ⧸ J) * a.1 = 0 := by
      -- Negating once removes the sign from the coefficient formula.
      simpa using congrArg Neg.neg hmul_zero_neg
    -- Cancel the unit `|G|` in the source quotient to show the kernel element itself vanishes.
    calc
      a.1 = (((↑u⁻¹ : RFix ⧸ J) * ↑u) * a.1) := by simp
      _ = (↑u⁻¹ : RFix ⧸ J) * ((↑u : RFix ⧸ J) * a.1) := by rw [mul_assoc]
      _ = 0 := by simp [hu, hmul_zero]
  have hsub : x - y = 0 := hzero_of_mem_ker ⟨x - y, hker⟩
  exact sub_eq_zero.mp hsub

/-- Remark 15.111.5: if `|G|` is a unit in `R`, then the canonical map
`(R^G)/J → (R / JR)^G` is bijective, hence an isomorphism. -/
theorem fixedSubringQuotientToFixedQuotient_bijective_of_isUnit_card
    (J : Ideal RFix) (h_card : IsUnit (Nat.card G : R)) :
    Function.Bijective (fixedSubringQuotientToFixedQuotient J) := by
  -- Route correction: use the polynomial identities from Lemma 15.111.4 and compare the
  -- `|G| - 1` coefficient, rather than introducing an averaging operator on the quotient.
  refine ⟨?_, ?_⟩
  · exact fixedSubringQuotientToFixedQuotient_injective_of_isUnit_card
      (R := R) (G := G) J h_card
  · exact fixedSubringQuotientToFixedQuotient_surjective_of_isUnit_card
      (R := R) (G := G) J h_card

/-- Remark 15.111.5, canonical isomorphism form: if `|G|` is a unit in `R`, then the canonical map
`(R^G)/J → (R / JR)^G` is an isomorphism of rings. -/
noncomputable def fixedSubringQuotientToFixedQuotientEquivOfIsUnit_card
    (J : Ideal RFix) (h_card : IsUnit (Nat.card G : R)) :
    RFix ⧸ J ≃+* fixedSubringFixedQuotient J :=
  RingEquiv.ofBijective (fixedSubringQuotientToFixedQuotient J)
    (fixedSubringQuotientToFixedQuotient_bijective_of_isUnit_card J h_card)

end
