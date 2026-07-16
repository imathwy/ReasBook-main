import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_91_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace Module

open scoped PowerSeries

/-
Domain triage:
- `source-facing`: the coefficientwise `p`-adic divisibility-tail condition on `ℤ⟦X⟧` and
  the resulting submodule singled out in the remark;
- `core/canonical`: the chapter owner predicates `Module.Flat`, `Module.MittagLeffler`, and
  `Module.Projective`;
- `bridge/view`: the nonfree divisible-tail submodule obstructing projectivity of `ℤ⟦X⟧`.
Sampled owner-level declarations in this domain:
- `Module.MittagLeffler` from `Definition_10_88_7`;
- `Module.noetherian_pi_flat_and_mittagLeffler` from `Lemma_10_91_3`;
- `Module.noetherian_mvPowerSeries_flat_and_mittagLeffler` from `Lemma_10_91_4`;
- `Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated` from
  `Theorem_10_93_3`.
Primitive data are exactly `HasPAdicallyDivisibleTail` and the induced `Submodule`; the flat,
Mittag-Leffler, and projective clauses are derived API and should reuse the chapter owners rather
than a parallel local class. -/

/-- A formal power series over `ℤ` has an eventually `p`-adically divisible tail if, for every
integer `m`, only finitely many coefficients fail to be divisible by `p^(m + 1)`. This is the
same positive-exponent condition from the remark, reindexed to avoid a redundant positivity
guard. -/
def HasPAdicallyDivisibleTail (p : ℕ) (f : ℤ⟦X⟧) : Prop :=
  ∀ m : ℕ, Set.Finite {i : ℕ | ¬ ((p : ℤ) ^ (m + 1) ∣ PowerSeries.coeff i f)}

/-- Unfolding `HasPAdicallyDivisibleTail` gives the coefficientwise eventual divisibility condition
used in the remark, with the positive exponent written as `m + 1`. -/
theorem hasPAdicallyDivisibleTail_iff (p : ℕ) (f : ℤ⟦X⟧) :
    HasPAdicallyDivisibleTail p f ↔
      ∀ m : ℕ, Set.Finite {i : ℕ | ¬ ((p : ℤ) ^ (m + 1) ∣ PowerSeries.coeff i f)} :=
  Iff.rfl

-- Proof sketch: every coefficient of the zero series is `0`, so it is divisible by every power of
-- `p`; hence the exceptional set is empty for each exponent `m + 1`.
/-- The zero power series has an eventually `p`-adically divisible tail. -/
theorem hasPAdicallyDivisibleTail_zero (p : ℕ) :
    HasPAdicallyDivisibleTail p (0 : ℤ⟦X⟧) := sorry

-- Proof sketch: for each fixed `m`, the coefficients of `f + g` can fail to be divisible by
-- `p^(m + 1)`
-- only where the corresponding coefficient of `f` or of `g` already fails, so the exceptional set
-- is contained in the union of two finite sets.
/-- The eventually `p`-adically divisible-tail condition is closed under addition. -/
theorem hasPAdicallyDivisibleTail_add (p : ℕ) {f g : ℤ⟦X⟧}
    (hf : HasPAdicallyDivisibleTail p f) (hg : HasPAdicallyDivisibleTail p g) :
    HasPAdicallyDivisibleTail p (f + g) := sorry

-- Proof sketch: multiplying all coefficients by an integer scalar preserves divisibility by each
-- fixed power `p^(m + 1)`, so no new infinite exceptional set can appear.
/-- The eventually `p`-adically divisible-tail condition is closed under scalar multiplication. -/
theorem hasPAdicallyDivisibleTail_smul (p : ℕ) (n : ℤ) {f : ℤ⟦X⟧}
    (hf : HasPAdicallyDivisibleTail p f) :
    HasPAdicallyDivisibleTail p (n • f) := sorry

/-- The submodule of `ℤ[[x]]` whose coefficients are eventually divisible by every power of `p`. -/
def pAdicallyDivisibleTailSubmodule (p : ℕ) : Submodule ℤ ℤ⟦X⟧ where
  carrier := {f | HasPAdicallyDivisibleTail p f}
  zero_mem' := hasPAdicallyDivisibleTail_zero p
  add_mem' := fun hf hg ↦ hasPAdicallyDivisibleTail_add p hf hg
  smul_mem' := fun n _ hf ↦ hasPAdicallyDivisibleTail_smul p n hf

/-- Membership in `pAdicallyDivisibleTailSubmodule p` is exactly the eventual divisibility
condition on coefficients. -/
theorem mem_pAdicallyDivisibleTailSubmodule_iff (p : ℕ) (f : ℤ⟦X⟧) :
    f ∈ pAdicallyDivisibleTailSubmodule p ↔ HasPAdicallyDivisibleTail p f :=
  Iff.rfl

-- Proof sketch: the remark shows that `pAdicallyDivisibleTailSubmodule p` is uncountable, while
-- the residue classes of the monomials `x^i` span its quotient modulo `p`. A free abelian group of
-- uncountable rank would have uncountable dimension after reduction mod `p`, giving a
-- contradiction.
/-- For a prime `p`, the divisible-tail submodule from the remark is not free as an abelian
group. -/
theorem pAdicallyDivisibleTailSubmodule_not_free {p : ℕ} (hp : Nat.Prime p) :
    ¬ Module.Free ℤ ↥(pAdicallyDivisibleTailSubmodule p) := sorry

-- Proof sketch: identify `ℤ[[x]]` with the one-variable case of the formal power-series module
-- covered by the owner theorem `noetherian_pi_flat_and_mittagLeffler`.
/-- The `ℤ`-module `ℤ[[x]]`, formalized as `ℤ⟦X⟧`, is flat. -/
instance integerPowerSeries_flat : Module.Flat ℤ ℤ⟦X⟧ := by
  simpa [PowerSeries] using
    (noetherian_pi_flat_and_mittagLeffler :
      Module.Flat ℤ ((Unit →₀ ℕ) → ℤ) ∧ MittagLeffler ℤ ((Unit →₀ ℕ) → ℤ)).1

-- Proof sketch: apply the same owner theorem `noetherian_pi_flat_and_mittagLeffler` to the
-- coefficient module presentation of `ℤ⟦X⟧`.
/-- The `ℤ`-module `ℤ[[x]]`, formalized as `ℤ⟦X⟧`, is Mittag-Leffler. -/
instance integerPowerSeries_mittagLeffler : MittagLeffler ℤ ℤ⟦X⟧ := by
  simpa [PowerSeries] using
    (noetherian_pi_flat_and_mittagLeffler :
      Module.Flat ℤ ((Unit →₀ ℕ) → ℤ) ∧ MittagLeffler ℤ ((Unit →₀ ℕ) → ℤ)).2

-- Proof sketch: if `ℤ⟦X⟧` were projective, then as an abelian group it would be free, and
-- every submodule would also be free. For any prime `p`, the submodule
-- `pAdicallyDivisibleTailSubmodule p` is not free by the preceding theorem, contradiction.
/-- Remark 10.93.2: the `ℤ`-module `ℤ[[x]]`, formalized as `ℤ⟦X⟧`, is flat and Mittag-Leffler but
not projective. This is the source-facing counterexample showing that Lemma 10.93.1 fails without
the countable-generation assumption. -/
theorem integerPowerSeries_flat_mittagLeffler_and_not_projective :
    Module.Flat ℤ ℤ⟦X⟧ ∧ MittagLeffler ℤ ℤ⟦X⟧ ∧ ¬ Module.Projective ℤ ℤ⟦X⟧ := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  sorry

/-- The `ℤ`-module `ℤ[[x]]`, formalized as `ℤ⟦X⟧`, is not projective. -/
theorem integerPowerSeries_not_projective :
    ¬ Module.Projective ℤ ℤ⟦X⟧ :=
  integerPowerSeries_flat_mittagLeffler_and_not_projective.2.2

end Module
