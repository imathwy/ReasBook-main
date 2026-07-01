import Mathlib
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-
Domain-style sampling for Lemma 10.140.3:
- primary domain: smoothness at a prime ideal of a finite type algebra over a field, expressed via
  the residue-field fiber of Kähler differentials and regularity of the localized ring;
- sampled owner declarations:
  `Algebra.IsSmoothAt`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `IsRegularLocalRing.iff_finrank_cotangentSpace`,
  `finrank_kaehlerFiber_eq_finrank_cotangent`;
- best owner abstraction: the canonical owner is the prime-ideal predicate `Algebra.IsSmoothAt k q`
  for `q : Ideal S` with `[q.IsPrime]`; the corresponding residue-field fiber
  `Ideal.ResidueField q ⊗[S] Ω[S⁄k]` and localized ring `Localization.AtPrime q` are derived data
  on that owner, so the public theorems should live directly at the ideal level rather than
  through a parallel `PrimeSpectrum S` wrapper;
- primitive data: a prime ideal `q : Ideal S`;
- derived API: the finrank comparison on the Kähler fiber and the regular-local consequence for
  `Localization.AtPrime q`.

Source/core/bridge triage:
- `source-facing`: the primewise TFAE and the regular-local consequence stated for the given prime;
- `core/canonical`: `Algebra.IsSmoothAt k q`;
- `bridge/view`: the `PrimeSpectrum S` presentation used downstream in `SmoothAtPrime`-style
  statements and the maximal-ideal quotient bridge from `Lemma 10.140.1`.
-/

-- Proof sketch: first pass to an algebraic closure `K / k` and choose a maximal ideal of
-- `K ⊗[k] S` lying over `q`. The local smoothness condition `IsSmoothAt k q` transfers to
-- the lifted maximal ideal after base change, while base change for Kähler differentials
-- identifies the fiber dimension with the one over `q`. Then Lemma `10.140.2` gives the
-- equivalence between smoothness and the inequality/equality of the cotangent-space dimension at
-- the lifted maximal ideal, and the result descends back to `q`.
/-- Lemma 10.140.3: for a finite type `k`-algebra `S` over a field and a prime `q` of `S`, the
following are equivalent: `S` is smooth at `q` over `k`, formalized as `IsSmoothAt k q`;
the fiber of `Ω[S⁄k]` at `q` has `κ(q)`-dimension at most `dim(S_q)`; the same fiber dimension
equals `dim(S_q)`. -/
theorem isSmoothAt_tfae_finrank_kaehlerFiber_le_eq (q : Ideal S) [q.IsPrime] :
    List.TFAE
      [ IsSmoothAt k q
      , Module.finrank (Ideal.ResidueField q)
          ((Ideal.ResidueField q) ⊗[S] Ω[S⁄k]) ≤ ringKrullDim (Localization.AtPrime q)
      , Module.finrank (Ideal.ResidueField q)
          ((Ideal.ResidueField q) ⊗[S] Ω[S⁄k]) = ringKrullDim (Localization.AtPrime q) ] := sorry

-- Proof sketch: after base change to an algebraic closure of `k`, the smoothness hypothesis gives
-- a smooth point on the base-changed algebra lying over `q`. Lemma `10.140.2` makes the
-- corresponding localized ring regular, and Lemma `10.110.9` descends regularity along the flat
-- local map from `S_q` to that localized base change.
/-- If `S` is smooth at the prime `q` over the field `k`, formalized as `IsSmoothAt k q`,
then the local ring `S_q` is regular. -/
theorem isRegularLocalRing_of_isSmoothAt (q : Ideal S) [q.IsPrime] (hsmooth : IsSmoothAt k q) :
    IsRegularLocalRing (Localization.AtPrime q) := sorry

end

end Algebra
