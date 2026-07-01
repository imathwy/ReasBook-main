import Mathlib
import stacks_project.Chap10.Definition_10_42_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-
Domain-style sampling for Lemma 10.140.5:
- primary domain: smoothness at a prime of a finite type algebra over a field versus regularity of
  the corresponding local ring, under a separable residue-field hypothesis;
- sampled owner declarations:
  `Algebra.IsSmoothAt`,
  `Algebra.isRegularLocalRing_of_isSmoothAt`,
  `residueCotangentToKaehler_injective_of_isSeparableOver`,
  `IsRegularLocalRing.iff_finrank_cotangentSpace`;
- best owner abstraction: the canonical owner is the ideal-level predicate `IsSmoothAt k q` for a
  prime ideal `q : Ideal S`; the prime-spectrum presentation is only a bridge/view, since the
  mathematical payload is entirely carried by `q`, `q.ResidueField`, and `Localization.AtPrime q`;
- primitive data: a prime ideal `q : Ideal S` and the Stacks-project separability hypothesis
  `IsSeparableOver k q.ResidueField`;
- derived API: the regular-local condition on `Localization.AtPrime q` and the resulting
  equivalence with `IsSmoothAt k q`.

Source/core/bridge triage:
- `source-facing`: the Stacks equivalence between smoothness at `q` and regularity of `S_q` under
  separability of `κ(q) / k`;
- `core/canonical`: `IsSmoothAt k q` and `IsRegularLocalRing (Localization.AtPrime q)`;
- `bridge/view`: a `PrimeSpectrum S` wrapper, which is not retained as the main owner surface. -/

-- Proof sketch: one direction is Lemma `10.140.3`, which shows that smoothness at `q` implies the
-- regularity of `S_q`. For the converse, use Lemma `10.140.4` and the conormal exact sequence from
-- Lemma `10.131.9` to identify the dimension of the Kähler-differential fiber with the embedding
-- dimension of `S_q`; the Stacks-project separability hypothesis on `κ(q) / k` and Lemma
-- `10.116.3` then turn regularity into the equality criterion in Lemma `10.140.3`.
/-- Lemma 10.140.5: let `q` be a prime of the finite type `k`-algebra `S` and assume the residue
field `κ(q) = q.ResidueField` is separable over `k` in the Stacks Project sense. Then `S` is
smooth at `q` over `k`
if and only if the local ring `S_q`, formalized as `Localization.AtPrime q`, is a regular local
ring. -/
theorem isSmoothAt_iff_isRegularLocalRing_of_separable_residueField
    (q : Ideal S) [q.IsPrime] [IsSeparableOver k q.ResidueField] :
    IsSmoothAt k q ↔ IsRegularLocalRing (Localization.AtPrime q) := sorry

end

end Algebra
