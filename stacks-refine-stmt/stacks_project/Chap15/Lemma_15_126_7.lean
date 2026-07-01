import Mathlib
import stacks_project.Chap10.Definition_10_60_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter
open IsLocalRing
open scoped Ideal

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Proof sketch: let `I = parameterIdeal x`. Proposition 10.59.5 gives an eventual polynomial
-- representative `P` of the rationalized Hilbert-Samuel `χ`-function
-- `n ↦ ((χ_ I R n).toNat : ℚ)`, while the Hilbert-Samuel degree API together with
-- Proposition 10.60.9 identifies the degree of any such representative with `d` from
-- `hx : IsSystemOfParameters x`.
-- Compare the first difference
-- `length_R (R / I^(n + 1)) - length_R (R / I^n)` with the surjective map
-- `⨁_{i₁ + ··· + i_d = n} R / I ⟶ I^n / I^(n + 1)` induced by the monomials
-- `g₁ ^ i₁ * ··· * g_d ^ i_d`; this bounds the degree-`d - 1` leading term by
-- `length_R (R / I) / (d - 1)!`, which is equivalent to `e ≤ Module.length R (R ⧸ I)`.
/-- Lemma 15.126.7: let `(R, 𝔪)` be a Noetherian local ring, let `x` be a system of parameters of
length `d`, and let `I = parameterIdeal x`. If `P` is an eventual polynomial representative of the
canonical rationalized Hilbert-Samuel `χ`-function
`n ↦ ((χ_ I R n).toNat : ℚ)` and has leading
coefficient
`e / d!`, then `(e : ℕ∞) ≤ Module.length R (R ⧸ I)`. -/
theorem hilbertSamuelMultiplicity_le_length_quotient_parameterIdeal_of_isSystemOfParameters
    {d : ℕ} (x : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x) (P : Polynomial ℚ)
    (e : ℕ)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(parameterIdeal x) R n).toNat : ℚ))
    (hlead : P.leadingCoeff = (e : ℚ) / d.factorial) :
    (e : ℕ∞) ≤ Module.length R (R ⧸ parameterIdeal x) := sorry

end
