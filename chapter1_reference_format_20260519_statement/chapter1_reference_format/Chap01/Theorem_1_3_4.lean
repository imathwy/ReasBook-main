import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Polynomial

variable {K : Type u} [Field K]

-- Proof sketch: existence is given by the canonical quotient and remainder `F / G` and `F % G`,
-- using `EuclideanDomain.div_add_mod` together with `Polynomial.degree_mod_lt`. For uniqueness,
-- compare any other decomposition `F = G * Q + T` with the canonical one and use the Euclidean
-- division uniqueness argument for polynomials over a field.
/-- Theorem 1.3.4: for polynomials `F, G ∈ K[X]` with `G ≠ 0`, there is a unique pair `(Q, T)`
such that `F = G * Q + T` and `T.degree < G.degree`. -/
theorem existsUnique_polynomial_quotient_remainder (F G : Polynomial K) (hG : G ≠ 0) :
    ∃! QT : Polynomial K × Polynomial K, F = G * QT.1 + QT.2 ∧ QT.2.degree < G.degree := by
  refine ⟨(F / G, F % G), ?_, ?_⟩
  · constructor
    · simpa using (EuclideanDomain.div_add_mod F G).symm
    · exact Polynomial.degree_mod_lt F hG
  · rintro ⟨Q, T⟩ ⟨hEq, hdegT⟩
    let Gm : Polynomial K := G * Polynomial.C G.leadingCoeff⁻¹
    have hGm : Gm.Monic := by
      simpa [Gm] using Polynomial.monic_mul_leadingCoeff_inv hG
    have hdeg : T.degree < Gm.degree := by
      simpa [Gm] using hdegT
    have hlc : G.leadingCoeff ≠ 0 := by
      simpa [Polynomial.leadingCoeff_eq_zero] using hG
    have hdecomp : T + Gm * (Polynomial.C G.leadingCoeff * Q) = F := by
      calc
        T + Gm * (Polynomial.C G.leadingCoeff * Q)
            =
              T + G * ((Polynomial.C G.leadingCoeff⁻¹ * Polynomial.C G.leadingCoeff) * Q) := by
                rw [show Gm = G * Polynomial.C G.leadingCoeff⁻¹ by rfl]
                ring_nf
        _ = T + G * Q := by simp [← Polynomial.C_mul, hlc]
        _ = F := by simpa [add_comm] using hEq.symm
    have hunique := Polynomial.div_modByMonic_unique (Polynomial.C G.leadingCoeff * Q) T hGm
      ⟨hdecomp, hdeg⟩
    have hQ : F / G = Q := by
      calc
        F / G = Polynomial.C G.leadingCoeff⁻¹ * (F /ₘ Gm) := by
          simp [Polynomial.div_def, Gm]
        _ = Polynomial.C G.leadingCoeff⁻¹ * (Polynomial.C G.leadingCoeff * Q) := by
          rw [hunique.1]
        _ = (Polynomial.C G.leadingCoeff⁻¹ * Polynomial.C G.leadingCoeff) * Q := by
          rw [mul_assoc]
        _ = Polynomial.C (G.leadingCoeff⁻¹ * G.leadingCoeff) * Q := by
          rw [← Polynomial.C_mul]
        _ = Q := by simp [hlc]
    have hT : F % G = T := by
      simpa [Polynomial.mod_def, Gm] using hunique.2
    exact Prod.ext hQ.symm hT.symm
