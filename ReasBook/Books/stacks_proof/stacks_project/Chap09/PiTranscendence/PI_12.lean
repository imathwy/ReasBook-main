import Mathlib
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_11

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for PI-12:
- primary domain: prime divisibility in `ℤ`, applied to the integer candidate produced in `PI_11`;
- sampled owner declarations:
  `Int.Prime.dvd_mul'`,
  `dvd_add_left`,
  `dvd_zero`,
  `dvd_mul_right`;
- best owner abstraction: the canonical integer Euclid lemma `Int.Prime.dvd_mul'`; the source
  statement should stay a direct corollary about the named integer candidate `Z_p`, with the
  additive divisibility step handled by `dvd_add_left`;
- primitive data: the explicit arithmetic relation `Z_p = D_p * C * n_p + p * Y_p`;
- derived API: if `Z_p = 0`, then `p` divides `D_p * C * n_p`, and the prime-divisibility owner
  forces `p` to divide one of `D_p`, `C`, or `n_p`.

Source/core/bridge triage:
- `source-facing`: the nonvanishing statement for the integer candidate `Z_p`;
- `core/canonical`: `Int.Prime.dvd_mul'`;
- `bridge/view`: the additive divisibility rewrite using `dvd_zero`, `dvd_mul_right`, and
  `dvd_add_left`;
- `layer`: `source-facing`.
-/

/-- Lemma PI-12: if `p` is prime and divides none of `n_p`, `C`, and the denominator integer
`D_p` from Lemma `PI-11`, then the corresponding integer `Z_p` from Lemma `PI-11` is nonzero. -/
theorem integer_candidate_with_leadingCoeff_power_denominator_z_ne_zero
    {C n_p D_p Y_p Z_p : ℤ} {p : ℕ}
    (hp : Nat.Prime p)
    (hZ_p : Z_p = D_p * C * n_p + (p : ℤ) * Y_p)
    (hn_p : ¬ ((p : ℤ) ∣ n_p))
    (hC : ¬ ((p : ℤ) ∣ C))
    (hD_p : ¬ ((p : ℤ) ∣ D_p)) :
    Z_p ≠ 0 := by
  intro hZ_zero
  have hZ_div : (p : ℤ) ∣ Z_p := by
    simpa [hZ_zero] using (dvd_zero (p : ℤ))
  have hsum : (p : ℤ) ∣ D_p * C * n_p + (p : ℤ) * Y_p := by
    simpa [hZ_p] using hZ_div
  have hpY_p : (p : ℤ) ∣ (p : ℤ) * Y_p := dvd_mul_right (p : ℤ) Y_p
  have hprod : (p : ℤ) ∣ D_p * C * n_p := (dvd_add_left hpY_p).mp hsum
  rcases Int.Prime.dvd_mul' hp hprod with hDC | hn_p'
  · rcases Int.Prime.dvd_mul' hp hDC with hD_p' | hC'
    · exact hD_p hD_p'
    · exact hC hC'
  · exact hn_p hn_p'
