import Mathlib

namespace Serre.Chap13.Exercise_13_13_1_17

open Matrix
open Matrix.GeneralLinearGroup

noncomputable section

open Polynomial

section Exercise137

variable (p : ℕ) [Fact p.Prime]

section

variable (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (p ^ 2))))

local notation "GPrime" =>
  Multiplicative (ZMod (p ^ 2)) ⋊[φ] Multiplicative (ZMod p)

/-- Helper for Exercise 13-13.1-17: powers of `Multiplicative.ofAdd 1` record repeated addition in
`ZMod (p^2)`. -/
theorem ofAdd_one_pow (n : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) ^ n =
      Multiplicative.ofAdd ((n : ℕ) : ZMod (p ^ 2)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [pow_succ, ih]

/-- Helper for Exercise 13-13.1-17: the remaining Sylow-side blocker is to transport an arbitrary
Sylow `p`-subgroup of `GL₃(𝔽_p)` to the upper-unitriangular Heisenberg model and prove that every
element has `p`-th power equal to `1`. -/
theorem sylowGL3_pow_p_eq_one (hp2 : p ≠ 2)
    (P : Sylow p (GL (Fin 3) (ZMod p))) (x : P) :
    x ^ p = 1 := by
  let Gmat : Matrix (Fin 3) (Fin 3) (ZMod p) :=
    (((x : P) : GL (Fin 3) (ZMod p)) : Matrix _ _ _)
  let A : Matrix (Fin 3) (Fin 3) (ZMod p) := Gmat - 1
  have hp : Nat.Prime p := Fact.out
  obtain ⟨n, hn⟩ := P.isPGroup' x
  have hA_nilpotent : IsNilpotent A := by
    -- Route correction: work directly with the `p`-power torsion of `x`; in characteristic `p`,
    -- the relation `x^(p^n) = 1` forces `x - 1` to be nilpotent.
    refine ⟨p ^ n, ?_⟩
    obtain ⟨r, hr⟩ :=
      Commute.exists_add_pow_prime_pow_eq hp ((Commute.one_right Gmat).neg_right) n
    let f : P → Matrix (Fin 3) (Fin 3) (ZMod p) :=
      fun h => (((h : P) : GL (Fin 3) (ZMod p)) : Matrix _ _ _)
    have hgpow : Gmat ^ p ^ n = 1 := by
      simpa [f, Gmat] using congrArg f hn
    have hneg : (-(1 : Matrix (Fin 3) (Fin 3) (ZMod p))) ^ p ^ n = -1 := by
      have hodd : Odd (p ^ n) := (Nat.Prime.odd_of_ne_two hp hp2).pow
      simpa using hodd.neg_one_pow (α := Matrix (Fin 3) (Fin 3) (ZMod p))
    rw [show A = Gmat + -1 by simp [A, Gmat, sub_eq_add_neg]]
    rw [hr, hgpow, hneg]
    simp
  have hA3 : A ^ 3 = 0 := by
    -- A nilpotent endomorphism on a `3`-dimensional space has characteristic polynomial `X^3`,
    -- so Cayley-Hamilton forces the third power to vanish.
    have hA_toLin_nilpotent : IsNilpotent A.toLin' :=
      (Matrix.isNilpotent_toLin'_iff A).2 hA_nilpotent
    have hchar : LinearMap.charpoly A.toLin' = X ^ 3 := by
      simpa [Module.finrank_fintype_fun_eq_card] using
        (IsNilpotent.charpoly_eq_X_pow_finrank (R := ZMod p) (M := Fin 3 → ZMod p)
          hA_toLin_nilpotent)
    have hpowLin : A.toLin' ^ 3 = 0 := by
      simpa [hchar, aeval_X_pow] using (LinearMap.aeval_self_charpoly A.toLin')
    apply Matrix.toLin'.injective
    simpa [Matrix.toLin'_pow] using hpowLin
  have hp_gt_two : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hAp : A ^ p = 0 := by
    exact pow_eq_zero_of_le (by omega) hA3
  have hgpow : Gmat ^ p = 1 := by
    -- Apply the prime-power binomial identity once more to `1 + (x - 1)`; the nilpotent part
    -- dies because `A ^ p = 0`.
    obtain ⟨r, hr⟩ := Commute.exists_add_pow_prime_pow_eq hp (Commute.one_left A) 1
    have hsum : Gmat = 1 + A := by
      simp [A, Gmat]
    rw [hsum]
    simpa [pow_one, hAp] using hr
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simpa [Gmat] using congrFun (congrFun hgpow i) j

/-- Helper for Exercise 13-13.1-17: in the semidirect product `(Z / p²Z) ⋊ (Z / pZ)`, the obvious
generator from the `Z / p²Z` factor still has nontrivial `p`-th power. -/
theorem semidirect_inl_one_pow_p_ne_one :
    ((SemidirectProduct.inl (φ := φ) (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) : GPrime) ^ p) ≠
      1 := by
  have hp : Nat.Prime p := Fact.out
  have hp_lt : p < p ^ 2 := by
    nlinarith [hp.two_le]
  have hp_cast_ne_zero : ((p : ℕ) : ZMod (p ^ 2)) ≠ 0 := by
    intro hzero
    rw [ZMod.natCast_eq_zero_iff] at hzero
    exact (Nat.not_dvd_of_pos_of_lt hp.pos hp_lt) hzero
  intro hpow
  have hinl :
      SemidirectProduct.inl (φ := φ) (Multiplicative.ofAdd ((p : ℕ) : ZMod (p ^ 2))) = 1 := by
    -- Compute the `p`-th power through the inclusion of the normal factor.
    calc
      SemidirectProduct.inl (φ := φ) (Multiplicative.ofAdd ((p : ℕ) : ZMod (p ^ 2)))
          = ((SemidirectProduct.inl (φ := φ) (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) :
                GPrime) ^ p) := by
              symm
              calc
                ((SemidirectProduct.inl (φ := φ) (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) :
                    GPrime) ^ p)
                    = SemidirectProduct.inl (φ := φ)
                        ((Multiplicative.ofAdd (1 : ZMod (p ^ 2))) ^ p) := by
                            exact
                              ((SemidirectProduct.inl (φ := φ)).map_pow
                                (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) p).symm
                _ = SemidirectProduct.inl (φ := φ)
                      (Multiplicative.ofAdd ((p : ℕ) : ZMod (p ^ 2))) := by
                            rw [ofAdd_one_pow (p := p) p]
      _ = 1 := hpow
  have hzero : ((p : ℕ) : ZMod (p ^ 2)) = 0 := by
    exact (ofAdd_eq_one).1 (SemidirectProduct.inl_injective (by simpa using hinl))
  exact hp_cast_ne_zero hzero

end

end Exercise137

end

end Exercise_13_13_1_17

end Chap13

end Serre
