import Mathlib

universe u v

namespace Chap10Lemma10778

open Chap10Lemma10778

section

variable {R : Type u} [Ring R]
variable {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided]
variable {P : Type v} [AddCommGroup P] [Module R P]

/-- Helper for Lemma 10.77.8: if an endomorphism is the identity modulo `J`, then it fixes the
submodule `I • ⊤` whenever `I ∩ J = 0`. -/
theorem eq_on_left_smul_top_of_right_quotient_identity
    (hIJ : I ⊓ J = ⊥)
    (a : P →ₗ[R] P)
    (hQJ :
      ∀ x : P,
        (Submodule.mkQ (J • (⊤ : Submodule R P))) (a x) =
          (Submodule.mkQ (J • (⊤ : Submodule R P))) x) :
    ∀ x ∈ (I • (⊤ : Submodule R P)), a x = x := by
  intro x hx
  -- Reduce to generators `r • m` with `r ∈ I`; the quotient hypothesis makes the error term lie
  -- in `J • ⊤`, so multiplying by `r` lands in `(I * J) • ⊤ = 0`.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m _
    have hdiff :
        a m - m ∈ J • (⊤ : Submodule R P) := by
      exact (Submodule.Quotient.eq (J • (⊤ : Submodule R P))).mp (hQJ m)
    have hsmul :
        r • (a m - m) ∈ I • (J • (⊤ : Submodule R P)) := by
      exact Submodule.smul_mem_smul hr hdiff
    have hzeroSub : I • (J • (⊤ : Submodule R P)) = ⊥ := by
      apply le_antisymm
      · calc
          I • (J • (⊤ : Submodule R P)) = (I * J) • (⊤ : Submodule R P) := by
            simpa using (Submodule.mul_smul I J (⊤ : Submodule R P)).symm
          _ ≤ (I ⊓ J) • (⊤ : Submodule R P) := by
            simpa using
              (Submodule.smul_mono (N := (⊤ : Submodule R P)) Ideal.mul_le_inf le_rfl)
          _ = ⊥ := by simpa [hIJ]
      · exact bot_le
    have hsmul_zero : r • (a m - m) = 0 := by
      have : r • (a m - m) ∈ (⊥ : Submodule R P) := by
        simpa [hzeroSub] using hsmul
      simpa using this
    apply sub_eq_zero.mp
    calc
      a (r • m) - r • m = r • a m - r • m := by simp [map_smul]
      _ = r • (a m - m) := by rw [smul_sub]
      _ = 0 := hsmul_zero
  · intro y z hy hz
    -- The induction closes because the fixed-point condition is additive.
    simp [map_add, hy, hz]

/-- Helper for Lemma 10.77.8: an endomorphism that is the identity on a submodule and on the
quotient by that submodule is bijective. -/
theorem bijective_of_id_on_submodule_and_quotient
    {M : Type*} [AddCommGroup M] [Module R M]
    (a : M →ₗ[R] M)
    (N : Submodule R M)
    (hN : ∀ x ∈ N, a x = x)
    (hQ : ∀ x : M, (Submodule.mkQ N) (a x) = (Submodule.mkQ N) x) :
    Function.Bijective a := by
  constructor
  · intro x y hxy
    have hxyQ : (Submodule.mkQ N) x = (Submodule.mkQ N) y := by
      calc
        (Submodule.mkQ N) x = (Submodule.mkQ N) (a x) := by simpa using (hQ x).symm
        _ = (Submodule.mkQ N) (a y) := by simpa [hxy]
        _ = (Submodule.mkQ N) y := by simpa using hQ y
    have hsub : x - y ∈ N := by
      exact (Submodule.Quotient.eq N).mp hxyQ
    have hfix : a (x - y) = x - y := hN (x - y) hsub
    have hz : a (x - y) = 0 := by
      simp [hxy]
    have : x - y = 0 := by simpa [hfix] using hz
    exact sub_eq_zero.mp this
  · intro y
    have hdiff : y - a y ∈ N := by
      exact (Submodule.Quotient.eq N).mp (hQ y).symm
    let n : N := ⟨y - a y, hdiff⟩
    refine ⟨y + n, ?_⟩
    -- Correct `y` by the discrepancy term living in `N`.
    calc
      a (y + n) = a y + a n := by simp [map_add]
      _ = a y + n := by rw [hN _ n.property]
      _ = y := by
        simp [n, sub_eq_add_neg, add_left_comm]

end

end Chap10Lemma10778
