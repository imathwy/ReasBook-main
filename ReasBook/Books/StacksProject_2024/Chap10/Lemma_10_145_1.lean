import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S' : Type v} {S : Type w}
variable [CommRing R] [CommRing S'] [CommRing S]
variable [Algebra R S'] [Algebra R S]
variable [Algebra.IsIntegral R S'] [Algebra.FiniteType R S]

/- Domain-style sampling:
* primary domain: commutative algebra of localizations and fibers of finite-type / integral
  algebra maps;
* sampled owner declarations:
  `Localization.awayMapₐ`,
  `Ideal.Fiber`,
  `Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ`;
* best owner abstraction:
  the mathlib spreading-out lemma
  `Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ`;
* layer:
  this numbered item is direct `core/canonical` owner reuse, so no extra local bridge theorem is
  needed;
* primitive data:
  the algebra map `f`, the localization element `g`, the prime `p`, and the fiberwise unit
  hypothesis;
* derived API:
  finiteness of the localization `R[1/r] → S[1/r]` away from some `r ∉ p`.
-/

/- Lemma 10.145.1: this is exactly the canonical localization-away spreading-out lemma
`Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ`. The source-facing statement adds no
extra mathematical content beyond that owner theorem, so the file records direct reuse instead of a
stronger local bijectivity wrapper. -/
recall Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ

end
