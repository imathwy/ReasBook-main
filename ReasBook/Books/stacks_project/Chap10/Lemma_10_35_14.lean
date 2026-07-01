import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R)

/- Domain triage:
* primary domain: Jacobson rings and maximal ideals under away-localization;
* source-facing layer: the textbook statements specialize to `Localization.Away f`;
* core/canonical owner: mathlib's away-localization API
  `isJacobsonRing_localization` and `IsLocalization.orderIsoOfMaximal`;
* primitive data vs. derived API: `f` and the ambient away-localization `S` are the only
  parameters, while the Jacobson-ring structure and maximal-ideal correspondence are recalled
  directly from the owner abstraction rather than repackaged in local wrapper declarations.
-/

/- Lemma 10.35.14 (1): if `R` is a Jacobson ring and `f ∈ R`, then the localization
`Localization.Away f` is again a Jacobson ring. Mathlib owns this at the more canonical
away-localization level `S` with `[IsLocalization.Away f S]`; the textbook statement is the
special case `S = Localization.Away f`. -/
recall isJacobsonRing_localization [Algebra R S] [IsLocalization.Away f S] [IsJacobsonRing R] :
    IsJacobsonRing S

/- Lemma 10.35.14 (2): maximal ideals of `Localization.Away f` correspond order-isomorphically to
maximal ideals of `R` that do not contain `f`. Mathlib owns this at the same canonical
away-localization level `S` with `[IsLocalization.Away f S]`; the textbook statement is the
special case `S = Localization.Away f`. -/
recall IsLocalization.orderIsoOfMaximal [Algebra R S] [IsLocalization.Away f S]
    [IsJacobsonRing R] :
    { p : Ideal S // p.IsMaximal } ≃o { p : Ideal R // p.IsMaximal ∧ f ∉ p }

end
