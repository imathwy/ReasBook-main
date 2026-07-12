import Mathlib
import StacksProject_2024.Chap10.Lemma_10_125_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: Krull-dimension bounds for quasi-finite maps from polynomial algebras over a
  field;
- sampled owner declarations:
  `Algebra.QuasiFinite`,
  `Algebra.FiniteType.of_restrictScalars_finiteType`,
  `ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt`,
  `ringKrullDim_le_iff_isMaximal_height_le`;
- best owner abstraction: the global owner `Algebra.QuasiFinite (MvPolynomial (Fin n) k) S`,
  with the primewise local-dimension inequality as derived API;
- primitive data: the polynomial-algebra structure on `S` and the ambient finite-type
  `k`-algebra structure, which canonically yields finite type over `MvPolynomial (Fin n) k` by
  restriction of scalars;
- derived API: quasi-finiteness at each prime of `S` and the maximal-ideal height bounds used to
  recover `ringKrullDim S ≤ n`.

Source/core/bridge triage:
- `source-facing`: the global dimension bound `ringKrullDim S ≤ n`;
- `core/canonical`: `Algebra.QuasiFinite`, `ringKrullDim`, and the polynomial-ring dimension
  theorem `MvPolynomial.ringKrullDim_of_isNoetherianRing`;
- `bridge/view`: finite-type restriction of scalars and the local bound
  `ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt`.
-/
-- Proof sketch: for each prime `q` of `S`, let `p` be its contraction to `k[t₁, …, tₙ]`.
-- Lemma `10.125.4` gives `dim S_q ≤ dim (k[t₁, …, tₙ])_p`. The latter is bounded by `n` via the
-- canonical height formula for localizations at primes together with the polynomial-ring dimension
-- theorem `MvPolynomial.ringKrullDim_of_isNoetherianRing`. Applying this bound to every maximal
-- ideal of `S` and invoking `ringKrullDim_le_iff_isMaximal_height_le` yields the result.
/-- Lemma 10.125.5: if `S` is a finite type `k`-algebra and `k[t_1, \ldots, t_n] → S`,
formalized by `MvPolynomial (Fin n) k → S`, is quasi-finite, then the Krull dimension of `S` is at
most `n`. -/
theorem ringKrullDim_le_of_quasiFinite_mvPolynomial_algebra
    {k : Type u} [Field k] {n : ℕ}
    {S : Type v} [CommRing S] [Algebra k S]
    [Algebra (MvPolynomial (Fin n) k) S]
    [IsScalarTower k (MvPolynomial (Fin n) k) S]
    [Algebra.FiniteType k S] [Algebra.QuasiFinite (MvPolynomial (Fin n) k) S] :
    ringKrullDim S ≤ n := by
  have hmv :
      ringKrullDim (MvPolynomial (Fin n) k) =
        ringKrullDim k + Nat.card (Fin n) :=
    MvPolynomial.ringKrullDim_of_isNoetherianRing
  letI : Algebra.FiniteType (MvPolynomial (Fin n) k) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (MvPolynomial (Fin n) k) S
  refine (ringKrullDim_le_iff_isMaximal_height_le n).2 fun q hq ↦ ?_
  letI : q.IsPrime := hq.isPrime
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
  have hq :
      ringKrullDim (Localization.AtPrime q) ≤
        ringKrullDim (Localization.AtPrime (q.under (MvPolynomial (Fin n) k))) :=
    ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt q
  refine hq.trans ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (q.under (MvPolynomial (Fin n) k))
    (Localization.AtPrime (q.under (MvPolynomial (Fin n) k)))]
  refine le_trans (Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top') ?_
  simp [hmv]
