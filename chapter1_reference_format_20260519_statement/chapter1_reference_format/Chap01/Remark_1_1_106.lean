import Mathlib
import chapter1_reference_format.Chap01.Proposition_1_1_105

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: apply the preceding Hensel lemma to any simple root modulo `p`,
-- and iterate the lifting step to obtain roots modulo `p^(k + 1)` for every `k`.
/-- Remark 1.1.106: under the simple-root hypothesis from Hensel's lemma, solving
`P(x) ≡ 0 [ZMOD p]` already suffices to obtain a solution modulo every power `p^(k + 1)`. -/
theorem exists_root_mod_prime_powers_of_simple_root_mod_p
    (p : ℕ) (hp : Nat.Prime p) (P : Polynomial ℤ)
    (hroot : ∃ a : ℤ, P.eval a ≡ 0 [ZMOD p] ∧ ¬ (P.derivative.eval a ≡ 0 [ZMOD p])) :
    ∀ k : ℕ, ∃ x : ℤ, P.eval x ≡ 0 [ZMOD p ^ k.succ] := by
  intro k
  let k' : ℕ+ := ⟨k.succ, Nat.succ_pos k⟩
  rcases hroot with ⟨a, ha_root, ha_simple⟩
  have ha_root' : (P.map (Int.castRingHom (ZMod p))).IsRoot (a : ZMod p) := by
    change (P.map (Int.castRingHom (ZMod p))).eval (a : ZMod p) = 0
    rw [Polynomial.eval_map]
    have hdiv : (p : ℤ) ∣ P.eval a := Int.modEq_zero_iff_dvd.mp ha_root
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (P.eval a) p).2 hdiv
  have ha_simple' : ¬ (P.derivative.map (Int.castRingHom (ZMod p))).IsRoot (a : ZMod p) := by
    intro hzero
    apply ha_simple
    exact Int.modEq_zero_iff_dvd.mpr <| by
      simpa [Polynomial.IsRoot, Polynomial.eval_map] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd (P.derivative.eval a) p).mp <| by
          simpa [Polynomial.IsRoot, Polynomial.eval_map] using hzero
  have hlift :
      ∃! b : ZMod (p ^ k.succ),
        (P.map (Int.castRingHom (ZMod (p ^ k.succ)))).IsRoot b ∧
          ZMod.castHom
            (show p ∣ p ^ k.succ by exact dvd_pow_self p (Nat.succ_ne_zero k))
            (ZMod p) b = (a : ZMod p) := by
    simpa [k'] using
      existsUnique_root_mod_prime_pow_of_simple_root_mod_prime
        p hp k' P (a : ZMod p) ha_root' ha_simple'
  rcases hlift with ⟨b, hb, -⟩
  haveI : NeZero (p ^ k.succ) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine ⟨b.val, ?_⟩
  apply Int.modEq_zero_iff_dvd.mpr
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (P.eval (b.val : ℤ)) (p ^ k.succ)).mp
  calc
    ((P.eval (b.val : ℤ) : ℤ) : ZMod (p ^ k.succ))
        = (P.map (Int.castRingHom (ZMod (p ^ k.succ)))).eval ((b.val : ℕ) : ZMod (p ^ k.succ)) := by
          rw [Polynomial.eval_map]
          simpa using
            (P.eval₂_at_apply (Int.castRingHom (ZMod (p ^ k.succ))) (b.val : ℤ)).symm
    _ = (P.map (Int.castRingHom (ZMod (p ^ k.succ)))).eval b := by
          rw [ZMod.natCast_zmod_val b]
    _ = 0 := by
          simpa [Polynomial.IsRoot] using hb.1
