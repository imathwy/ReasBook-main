import Mathlib
import StacksProject_2024.Chap10.Lemma_10_135_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Algebra

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/- Domain-style sampling pass.

Primary domain: local complete intersections over a field and their detection on prime and maximal
localizations of an algebra.

Sampled owner declarations:
* `IsLocalCompleteIntersection`;
* `IsCompleteIntersectionOver`;
* `completeIntersectionOver_atPrime_tfae`;
* `MaximalSpectrum`.

Best owner abstraction: `IsLocalCompleteIntersection k S` is the source-facing owner on `S`,
while `IsCompleteIntersectionOver k _` is the canonical owner on each local ring. For the
maximal-local criterion, `MaximalSpectrum S` is the canonical indexing object, so the theorem
surface should use it directly instead of a raw ideal plus a maximality proof.

Primitive vs. derived:
* primitive data: the field `k` and the `k`-algebra `S`;
* derived API: finite presentation and finite type of `S` from
  `IsLocalCompleteIntersection k S`, together with the prime-local and maximal-local comparison
  clauses.

Source/core/bridge triage:
* source-facing: the three-way `List.TFAE` below;
* core/canonical: `IsLocalCompleteIntersection k S` and
  `IsCompleteIntersectionOver k _`;
* bridge/view: the specialization from all prime localizations to maximal localizations.
-/

-- Proof sketch: once one of the three clauses holds, the relevant finite-presentation and
-- finite-type hypotheses are recovered from the owner abstractions (`IsLocalCompleteIntersection`
-- or the primewise/maximal complete-intersection conditions). Then apply Lemma `10.135.8` at each
-- prime `q` to identify the local complete-intersection condition on `S` with the
-- complete-intersection condition on `S_q`. The implication from all prime local rings to all
-- maximal localizations is immediate, and the converse follows from the locality of the complete
-- intersection property together with quasi-compactness of `Spec S`.
/-- Lemma 10.135.9: for a `k`-algebra `S`, the following are equivalent: `S` is a
local complete intersection over `k`; every local ring `S_q` for `q : PrimeSpectrum S` is a
complete intersection over `k`; and every localization `S_m` at a maximal ideal `m` of `S` is a
complete intersection over `k`. -/
theorem isLocalCompleteIntersection_tfae_completeIntersectionOver_localRings :
    List.TFAE
      [ IsLocalCompleteIntersection k S
      , ∀ q : PrimeSpectrum S, IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal)
      , ∀ m : MaximalSpectrum S, IsCompleteIntersectionOver k (Localization.AtPrime m.asIdeal)
      ] := sorry

end
