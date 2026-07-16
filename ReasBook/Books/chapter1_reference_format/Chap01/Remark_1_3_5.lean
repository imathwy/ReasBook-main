import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Polynomial
open Nat.WithBot

variable {R : Type u} [CommRing R] [Nontrivial R]

/-- Remark 1.3.5: if the leading coefficient of `G` is a unit in a nontrivial commutative ring,
then every polynomial `F` admits a quotient-remainder decomposition `F = GQ + T` with
`degree T < degree G`. -/
-- Proof sketch: multiply `G` by the inverse of its unit leading coefficient to reduce to the
-- monic case, apply the canonical monic division algorithm, and then rescale the quotient back.
theorem polynomial_division_exists_of_isUnit_leadingCoeff {F G : R[X]}
    (hG : IsUnit G.leadingCoeff) :
    ∃ q r : R[X], F = G * q + r ∧ degree r < degree G := by
  let Gm : R[X] := hG.unit⁻¹ • G
  have hGm : Gm.Monic := by
    simpa [Gm] using monic_of_isUnit_leadingCoeff_inv_smul hG
  refine ⟨hG.unit⁻¹ • (F /ₘ Gm), F %ₘ Gm, ?_, ?_⟩
  · rw [show G * (hG.unit⁻¹ • (F /ₘ Gm)) = Gm * (F /ₘ Gm) by
      simp [Gm, mul_smul_comm, smul_mul_assoc]]
    simpa [add_comm] using (modByMonic_add_div F Gm).symm
  · calc
      degree (F %ₘ Gm) < degree Gm := degree_modByMonic_lt F hGm
      _ = degree G := by
        simpa [Gm, Units.smul_def, smul_eq_C_mul] using
          (degree_C_mul_of_isUnit hG.unit⁻¹.isUnit G)

/-- Division by a polynomial with unit leading coefficient has a unique quotient-remainder pair; in
particular, this applies over integral domains, such as monic divisors in `ℤ[X]`. -/
-- Proof sketch: normalize the divisor to a monic polynomial, use the monic uniqueness theorem
-- `Polynomial.div_modByMonic_unique`, and compare any two decompositions inside the domain.
theorem polynomial_division_existsUnique_of_isUnit_leadingCoeff {F G : R[X]}
    (hG : IsUnit G.leadingCoeff) :
    ∃! qr : R[X] × R[X], F = G * qr.1 + qr.2 ∧ degree qr.2 < degree G := by
  let Gm : R[X] := hG.unit⁻¹ • G
  have hGm : Gm.Monic := by
    simpa [Gm] using monic_of_isUnit_leadingCoeff_inv_smul hG
  have hdegGm : degree Gm = degree G := by
    change degree (hG.unit⁻¹ • G) = degree G
    rw [Units.smul_def, smul_eq_C_mul]
    exact degree_C_mul_of_isUnit hG.unit⁻¹.isUnit G
  refine ⟨(hG.unit⁻¹ • (F /ₘ Gm), F %ₘ Gm), ?_, ?_⟩
  · constructor
    · rw [show G * (hG.unit⁻¹ • (F /ₘ Gm)) = Gm * (F /ₘ Gm) by
        simp [Gm, mul_smul_comm, smul_mul_assoc]]
      simpa [add_comm] using (modByMonic_add_div F Gm).symm
    · calc
        degree (F %ₘ Gm) < degree Gm := degree_modByMonic_lt F hGm
        _ = degree G := hdegGm
  · intro qr hqr
    have hdiv : F /ₘ Gm = (hG.unit : Rˣ) • qr.1 ∧ F %ₘ Gm = qr.2 :=
      div_modByMonic_unique ((hG.unit : Rˣ) • qr.1) qr.2 hGm
        ⟨by
            calc
              qr.2 + Gm * ((hG.unit : Rˣ) • qr.1) = qr.2 + G * qr.1 := by
                congr 1
                change ((↑hG.unit⁻¹ : R) • G) * (G.leadingCoeff • qr.1) = G * qr.1
                rw [smul_mul_assoc, mul_smul_comm, smul_smul]
                simp
              _ = F := by simpa [add_comm] using hqr.1.symm,
          by
            calc
              degree qr.2 < degree G := hqr.2
              _ = degree Gm := hdegGm.symm⟩
    rcases hdiv with ⟨hq, hr⟩
    refine Prod.ext ?_ hr.symm
    have hqR : F /ₘ Gm = G.leadingCoeff • qr.1 := by
      simpa [Units.smul_def, hG.unit_spec] using hq
    rw [hqR]
    change qr.1 = (↑hG.unit⁻¹ : R) • (G.leadingCoeff • qr.1)
    simp [smul_smul]

/-- If `R` is not a field, then unrestricted Euclidean division by arbitrary nonzero polynomials
can fail in `R[X]`. -/
-- Proof sketch: choose a nonunit nonzero coefficient `a : R`, divide `1` by the constant
-- polynomial `C a`, and note that any remainder of degree `< 0` must be zero, forcing `a` to be a
-- unit.
theorem polynomial_division_can_fail_of_not_isField (hR : ¬ IsField R) :
    ∃ F G : R[X], G ≠ 0 ∧
      ¬ ∃ qr : R[X] × R[X], F = G * qr.1 + qr.2 ∧ degree qr.2 < degree G := by
  classical
  obtain ⟨a, ha0, haunit⟩ : ∃ a : R, a ≠ 0 ∧ ¬ IsUnit a := by
    by_contra h
    apply hR
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro x hx0
    have hxunit : IsUnit x := by
      by_contra hxunit
      exact h ⟨x, hx0, hxunit⟩
    exact isUnit_iff_exists_inv.mp hxunit
  refine ⟨1, C a, by simpa [C_eq_zero] using ha0, ?_⟩
  intro hdiv
  rcases hdiv with ⟨qr, hqr, hdeg⟩
  have hr0deg : degree qr.2 < 0 := by
    simpa [degree_C ha0] using hdeg
  have hr0 : qr.2 = 0 := by
    rw [← degree_eq_bot]
    exact lt_zero_iff.mp hr0deg
  have hunitC : IsUnit (C a) := by
    refine isUnit_iff_exists_inv.mpr ⟨qr.1, ?_⟩
    simpa [hr0] using hqr.symm
  exact haunit <| isUnit_C.mp hunitC
