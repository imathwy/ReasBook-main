import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {B : Type u} [CommRing B]
variable {M : Type v} [Field M] [Algebra B M]

-- The primitive data are the coefficients `b₁` and `b₂`; the source-facing congruence follows by
-- adding the unchanged summand `ξ₁ + ξ₂` on both sides.
private theorem associated_pow_term_eq_negPow_of_eq_negPow
    {p e₁ n : ℕ} {π w : B} {ξ₁ ξ₂ : M} {b₁ b₂ : B}
    (hw : Associated w (π ^ e₁))
    (hξ₁ : ξ₁ = (algebraMap B M π) ^ (-(n : ℤ)) * algebraMap B M b₁)
    (hξ₂ : ξ₂ = (algebraMap B M π) ^ (-(n : ℤ)) * algebraMap B M b₂) :
    ∃ b : B,
      (algebraMap B M w) ^ p * ξ₁ * ξ₂ =
        (algebraMap B M π) ^ (-(2 * n : ℤ) + p * e₁) * algebraMap B M b := sorry

-- Proof sketch: write `ξ₁ = π^{-n} b₁` and `ξ₂ = π^{-n} b₂`. Since `w` is associated to `π ^ e₁`,
-- the factor `w ^ p` contributes valuation `p e₁`, so `w^p ξ₁ ξ₂` is divisible by
-- `π ^ (-2n + p e₁)`. Rewriting the displayed congruence in witness form gives the conclusion.
/-- 15.116.16.2: if `ξ₁, ξ₂ ∈ π^{-n}B` and `w` is associated to `π ^ e₁`, then
`ξ₁ + ξ₂ + w^p ξ₁ ξ₂ ≡ ξ₁ + ξ₂ mod π^{-2n + pe₁}B`. The statement only uses the displayed
associated-power hypothesis; no discrete-valuation structure on `B` enters the API. -/
theorem add_add_associated_pow_term_congruent_add_of_mem_negPow
    {p e₁ n : ℕ} {π w : B} {ξ₁ ξ₂ : M}
    (hw : Associated w (π ^ e₁))
    (hξ₁ : ∃ b₁ : B,
      ξ₁ = (algebraMap B M π) ^ (-(n : ℤ)) * algebraMap B M b₁)
    (hξ₂ : ∃ b₂ : B,
      ξ₂ = (algebraMap B M π) ^ (-(n : ℤ)) * algebraMap B M b₂) :
    ∃ b : B,
      ξ₁ + ξ₂ + (algebraMap B M w) ^ p * ξ₁ * ξ₂ =
        ξ₁ + ξ₂ + (algebraMap B M π) ^ (-(2 * n : ℤ) + p * e₁) * algebraMap B M b := by
  rcases hξ₁ with ⟨b₁, hξ₁⟩
  rcases hξ₂ with ⟨b₂, hξ₂⟩
  rcases associated_pow_term_eq_negPow_of_eq_negPow hw hξ₁ hξ₂ with ⟨b, hb⟩
  exact ⟨b, by simpa [hb]⟩

end
