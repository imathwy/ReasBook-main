import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_162_4
import stacks_proof.stacks_project.Chap10.Proposition_10_162_16

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

variable {R : Type u} {Rₘ : Type v} [CommRing R] [CommRing Rₘ] [Algebra R Rₘ]

/- Domain-style sampling:
- primary domain: commutative algebra of Nagata rings, localizations, and essential finite type;
- sampled owner abstractions of the same kind in the project:
  - `NagataRing`, the source-facing owner from `Definition_10_162_1`;
  - `UniversallyJapaneseRing`, the chapter bridge owner obtained from `NagataRing` in
    `Proposition_10_162_16`;
  - `universallyJapaneseRing_of_essFiniteType`, the canonical permanence theorem for essentially
    finite type algebras from `Lemma_10_162_4`;
  - `IsLocalization.isNoetherianRing`, the canonical Noetherian localization owner recall from
    `Lemma_10_31_1`.

Best owner abstraction:
- `NagataRing` is the source-facing owner for this lemma;
- the Noetherian part should be derived directly from `IsLocalization.isNoetherianRing`;
- the prime-quotient `N-2` part should be derived through the existing owner bridge
  `NagataRing → UniversallyJapaneseRing` and then the essentially-finite-type permanence theorem,
  rather than by introducing a separate local quotient-localization wrapper.

Primitive data vs derived API:
- primitive data: the localization datum `R → Rₘ` and the ambient assumption `[NagataRing R]`;
- derived API: Noetherianity of `Rₘ`, essential finite type of `Rₘ` and of its prime quotients
  over `R`, and the resulting `IsN2Ring` instances for those prime quotients.

Source/core/bridge triage:
- `source-facing`: the localization permanence statement for `NagataRing`;
- `core/canonical`: `NagataRing`, `UniversallyJapaneseRing`,
  `universallyJapaneseRing_of_essFiniteType`, and `IsLocalization.isNoetherianRing`;
- `bridge/view`: the passage from a prime quotient of the localization to an essentially finite
  type domain over the base Nagata ring.
-/

/-- Lemma 10.162.6: a localization of a Nagata ring is again a Nagata ring. -/
-- Proof sketch: a localization of a Noetherian ring is Noetherian. For a prime ideal `q` of the
-- localization, the quotient `Rₘ ⧸ q` is essentially of finite type over `R`; since a Nagata ring
-- is universally Japanese, `Lemma 10.162.4` makes `Rₘ ⧸ q` universally Japanese, and because it
-- is a domain, it is `N-2`. These are exactly the two fields needed to build `NagataRing Rₘ`.
@[stacks 032U]
theorem localization_nagataRing (M : Submonoid R) [IsLocalization M Rₘ] [NagataRing R] :
    NagataRing Rₘ := by
  letI : IsNoetherianRing Rₘ := IsLocalization.isNoetherianRing M Rₘ inferInstance
  refine NagataRing.mk ?_
  intro q
  letI : Algebra.EssFiniteType R Rₘ := Algebra.EssFiniteType.of_isLocalization Rₘ M
  let hEssFiniteType : Algebra.EssFiniteType R (Rₘ ⧸ q) := inferInstance
  let hUniversallyJapanese : UniversallyJapaneseRing R := inferInstance
  letI : Algebra.EssFiniteType R (Rₘ ⧸ q) := hEssFiniteType
  letI : UniversallyJapaneseRing (Rₘ ⧸ q) :=
    @universallyJapaneseRing_of_essFiniteType R (Rₘ ⧸ q) _ _ _ hUniversallyJapanese hEssFiniteType
  exact inferInstance

end
