import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Polynomial

/- Domain triage:
* source-facing: integrality of an element in a finite product algebra.
* core/canonical owner: `IsIntegral`.
* bridge/view: `Polynomial.piEquiv`, the evaluation maps `Pi.evalRingHom`, and the binary owner
  theorem `IsIntegral.pair_iff`.
Primitive data remains exactly the witness polynomial from `IsIntegral`; the componentwise
criterion is derived API. -/

namespace IsIntegral

/-- Lemma 10.36.8: an element of a finite product ring is integral over the product ring if and
only if each component is integral over the corresponding factor. -/
-- Proof sketch: use `Polynomial.piEquiv` to pass between a polynomial over the product ring and
-- its tuple of component polynomials. For the reverse implication, pad the component annihilating
-- polynomials to a common degree before reassembling them into a single monic polynomial over the
-- product ring.
theorem pi_iff {ι : Type u} [Finite ι] {R : ι → Type v} {S : ι → Type w}
    [∀ i, CommRing (R i)] [∀ i, Ring (S i)] [∀ i, Algebra (R i) (S i)] {s : Π i, S i} :
    IsIntegral (Π i, R i) s ↔ ∀ i, IsIntegral (R i) (s i) := by
  classical
  let _ := Fintype.ofFinite ι
  let e := piEquiv R
  have h_eval (r : Polynomial (Π i, R i)) (i : ι) :
      Pi.evalRingHom S i (aeval s r) = aeval (s i) (e r i) := by
    simpa [e, piEquiv] using
      r.map_aeval_eq_aeval_map
        (show (algebraMap (R i) (S i)).comp (Pi.evalRingHom R i) =
            (Pi.evalRingHom S i).comp (algebraMap (Π i, R i) (Π i, S i)) by
          ext x
          rfl)
        s
  constructor
  · rintro ⟨p, hpM, hp0⟩ i
    refine ⟨e p i, hpM.map (Pi.evalRingHom R i), ?_⟩
    have h : Pi.evalRingHom S i (aeval s p) = 0 := congrArg (Pi.evalRingHom S i) hp0
    rw [h_eval p i] at h
    exact h
  · intro hs
    choose p hpM hp0 using hs
    let N : ℕ := Finset.univ.sup fun i : ι ↦ (p i).natDegree
    let qfun : Π i, Polynomial (R i) := fun i ↦ p i * X ^ (N - (p i).natDegree)
    let q : Polynomial (Π i, R i) := e.symm qfun
    have hle (i : ι) : (p i).natDegree ≤ N := by
      let f : ι → ℕ := fun j ↦ (p j).natDegree
      change f i ≤ (Finset.univ : Finset ι).sup f
      exact Finset.le_sup (show i ∈ (Finset.univ : Finset ι) by simp)
    have hq (i : ι) : e q i = qfun i := by
      simp [q, qfun]
    refine ⟨q, ?_, ?_⟩
    · refine monic_of_natDegree_le_of_coeff_eq_one N ?_ ?_
      · rw [natDegree_le_iff_coeff_eq_zero]
        intro n hn
        ext i
        have hle_i : (p i).natDegree ≤ N := hle i
        have hk : N - (p i).natDegree ≤ n := by
          omega
        have hqcoeff : (qfun i).coeff n = 0 := by
          dsimp [qfun]
          rw [coeff_mul_X_pow', if_pos hk]
          · apply Polynomial.coeff_eq_zero_of_natDegree_lt
            omega
        have : q.coeff n i = (qfun i).coeff n := by
          simpa [e, piEquiv] using
            congrArg (fun f : Polynomial (R i) ↦ f.coeff n) (hq i)
        exact this.trans hqcoeff
      · ext i
        have hqcoeff : (qfun i).coeff N = 1 := by
          dsimp [qfun]
          have hcoeff_mul :
              (p i * X ^ (N - (p i).natDegree)).coeff N = (p i).coeff (p i).natDegree := by
            simpa [Nat.add_sub_of_le (hle i)] using
              coeff_mul_X_pow (p i) (N - (p i).natDegree) (p i).natDegree
          exact hcoeff_mul.trans (hpM i).coeff_natDegree
        have : q.coeff N i = (qfun i).coeff N := by
          simpa [e, piEquiv] using
            congrArg (fun f : Polynomial (R i) ↦ f.coeff N) (hq i)
        exact this.trans hqcoeff
    · ext i
      have hzero : aeval (s i) (qfun i) = 0 := by
        dsimp [qfun]
        simp [Polynomial.aeval_def, hp0 i]
      calc
        (aeval s q) i = Pi.evalRingHom S i (aeval s q) := rfl
        _ = aeval (s i) (e q i) := h_eval q i
        _ = aeval (s i) (qfun i) := by simp [hq i]
        _ = 0 := hzero

end IsIntegral
