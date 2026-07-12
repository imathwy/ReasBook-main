import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Finite (PrimeSpectrum R)]

-- Layering for this item:
-- * source-facing: a Noetherian ring with finite prime spectrum has dimension at most `1`.
-- * core/canonical owner: `Ring.KrullDimLE 1 R`.
-- * bridge/view: `ringKrullDim R ≤ 1` is recovered from the owner instance by
--   `Ring.krullDimLE_iff`.
-- Primitive data are exactly the assumptions `[IsNoetherianRing R]` and
-- `[Finite (PrimeSpectrum R)]`; the inequality theorem below is derived API from the owner
-- abstraction.

-- Proof sketch: first treat the local domain case using Lemma `10.61.1`, which rules out
-- Krull dimension at least `2` because a finite prime spectrum cannot contain an infinite nonempty
-- open subset. Then localize a domain at each maximal ideal and apply Lemma `10.60.4` to bound
-- `ringKrullDim R` by the supremum of maximal heights. For a general Noetherian ring, pass to each
-- quotient by a minimal prime and use Lemma `10.17.2` to see that every prime contains a minimal
-- prime, so all prime chains still have length at most `1`.
/-- Owner-level form of Lemma 10.61.2. The source-facing inequality
`ringKrullDim R ≤ 1` is the companion theorem below, obtained via `Ring.krullDimLE_iff`. -/
instance krullDimLE_one_of_finite_primeSpectrum : Ring.KrullDimLE 1 R := by
  sorry

end

section

variable {R : Type u} [CommRing R]

/-- Lemma 10.61.2, source-facing form: a Noetherian ring with finitely many prime ideals has
Krull dimension at most `1`. -/
theorem ringKrullDim_le_one_of_finite_primeSpectrum [IsNoetherianRing R] [Finite (PrimeSpectrum R)] :
    ringKrullDim R ≤ 1 :=
  Ring.krullDimLE_iff.mp inferInstance

end
