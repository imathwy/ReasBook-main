import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open KaehlerDifferential

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Algebra ℚ S]
variable (f : S)
variable (hdf : ∃ θ : Ω[S⁄R] →ₗ[S] S, θ (D R S f) = 1)

-- Proof sketch: the hypothesis gives an `S`-linear functional `θ : Ω[S⁄R] →ₗ[S] S` with
-- `θ (df) = 1`. Via the owner equivalence `KaehlerDifferential.linearMapEquivDerivation`, this
-- yields an `R`-derivation `δ : S → S` with `δ f = 1`. If `f` were nilpotent, applying `δ` to a
-- minimal relation `f^n = 0` would give `n • f^(n - 1) = 0`; since `S` is a `ℚ`-algebra, `n` is
-- invertible, contradicting minimality.
/-- Lemma 10.140.6: if there exists an `S`-linear map `Ω[S⁄R] →ₗ[S] S` sending `df` to `1`
(equivalently, `df` generates a free rank-one direct summand of `Ω[S⁄R]`), then `f` is not
nilpotent. -/
theorem not_isNilpotent_of_kaehlerDifferential_directSummand :
    ¬ IsNilpotent f := sorry

-- Proof sketch: with the same derivation `δ` satisfying `δ f = 1`, any relation `f * a = 0`
-- yields `a = -f * δ a`, so `a ∈ (f)`. Iterating this argument shows `a ∈ (f^n)` for every `n`.
-- In a Noetherian local ring, Krull's intersection theorem gives `⋂ n, (f^n) = 0`, hence `a = 0`
-- and multiplication by `f` is injective.
/-- Under the same hypothesis that `df` admits an `S`-linear functional with value `1`, if `S` is
Noetherian local, then `f` is a nonzerodivisor. -/
theorem isRegular_of_kaehlerDifferential_directSummand
    [IsLocalRing S] [IsNoetherianRing S] :
    IsRegular f := sorry

end
