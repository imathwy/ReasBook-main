import Mathlib
import StacksProject_2024.Chap10.Definition_10_136_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Algebra

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

/- Domain-style sampling:
- primary domain: cotangent modules of explicit quotient presentations, localized away from one
  element, under the syntomic owner predicate on the localized ring map;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `Ideal.Cotangent`,
  `LocalizedModule.Away`,
  `localized_presentation_cotangent_stable_equiv`;
- best owner abstraction: the public owner here is the pair of predicates
  `Module.Finite` / `Module.Projective` on the canonical localized cotangent module
  `LocalizedModule.Away g I.Cotangent`; the relative-global-complete-intersection presentation and
  the stable cotangent comparison are bridge/view input for the proof, not extra public data;
- primitive vs. derived:
  the primitive source-facing data are the quotient ideal `I` and the syntomic hypothesis on the
  localized quotient map `R → S_g`;
  a separate finite-generation hypothesis on `I` is derived proof input at most, not owner data
  for the localized conormal statement, so it should not remain in the public interface.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma for an explicit quotient `S = R[x₁, …, xₙ] / I`;
- `core/canonical`: `RingHom.Syntomic`, `Ideal.Cotangent`, and `LocalizedModule.Away`;
- `bridge/view`: `syntomicAtPrime_tfae`, `relativeGCI_conormalModule_has_basis`, and
  `localized_presentation_cotangent_stable_equiv`.
-/

local notation "Poly" => MvPolynomial (Fin n) R

-- Proof sketch: by Lemma `10.136.15`, after refining the basic open `D(g)` we may assume the
-- localization is a relative global complete intersection over `R`. Lemma `10.136.12` then makes
-- the conormal module free for that refined presentation, and Lemma `10.134.16` transports this
-- finite projective structure back to the localization of the original conormal module.
/-- Lemma 10.136.16: let `S = R[x₁, …, xₙ] / I` with `I` finitely generated. If the localization
`S_g` is syntomic over `R`, then the localized conormal module `(I / I²)_g` is a finite
projective `S_g`-module. -/
theorem idealCotangent_localizedAway_finiteProjective_of_syntomic
    (I : Ideal Poly) (g : Poly ⧸ I)
    (hsyntomic : (algebraMap R (Localization.Away g)).Syntomic) :
    Module.Finite (Localization.Away g) (LocalizedModule.Away g I.Cotangent) ∧
      Module.Projective (Localization.Away g) (LocalizedModule.Away g I.Cotangent) := sorry

end

end Algebra
