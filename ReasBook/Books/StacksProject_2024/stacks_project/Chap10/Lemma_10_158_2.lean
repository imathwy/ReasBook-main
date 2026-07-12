import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} {K : Type v} [Field k] [PerfectField k] [Field K] [Algebra k K]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

/- Domain triage:
- primary domain: Kähler differentials of field extensions in characteristic `p`, together with the
  Frobenius / perfect-field interface for `p`th powers;
- sampled owner declarations:
  `KaehlerDifferential.D`,
  `Derivation.leibniz_pow`,
  `exists_pth_root_of_minpoly_coeff_pth_powers`,
  `perfectField_iff_charZero_or_exists_pth_root`;
- best owner abstraction: the canonical universal derivation `KaehlerDifferential.D k K`;
- primitive data: the owner derivation itself and the ambient field/perfectness hypotheses;
- derived API: this source-facing kernel characterization of `KaehlerDifferential.D k K`.

Source/core/bridge triage:
- `source-facing`: `kaehlerDifferential_eq_zero_iff_exists_pth_root`;
- `core/canonical`: `KaehlerDifferential.D k K`;
- `bridge/view`: the `p`th-power side is the source-facing reformulation, while the eventual
  converse proof should reuse the Chapter 9/10 Frobenius and perfect-field owner lemmas rather than
  introduce any local wrapper around them.
-/

-- Proof sketch: if `a = b ^ p`, then the universal derivation kills `a` because
-- `d (b ^ p) = p • b ^ (p - 1) • db = 0` in characteristic `p`. Conversely, reduce to the finitely
-- generated case, choose a separating transcendence basis over the perfect base field, identify
-- `Ω[K⁄k]` with the free `K`-vector space on the differentials of that basis, deduce that the
-- coefficients of the minimal polynomial of `a` have zero differential, then reuse the canonical
-- Chapter 9/10 Frobenius/perfect-field bridge lemmas to conclude that `a` is a `p`th power.
/-- Lemma 10.158.2: over a perfect field `k` of characteristic `p > 0`, an element of an extension
field `K` has zero Kähler differential over `k` if and only if it is a `p`th power in `K`. -/
theorem kaehlerDifferential_eq_zero_iff_exists_pth_root (a : K) :
    KaehlerDifferential.D k K a = 0 ↔ ∃ b : K, b ^ p = a := by
  constructor
  · intro ha
    sorry
  · rintro ⟨b, rfl⟩
    letI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K]
    simp

end
