import Mathlib
import Mathlib.Data.List.TFAE
import stacks_project.Chap10.Definition_10_162_1
import stacks_project.Chap10.Definition_10_162_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: Noetherian local Nagata rings and analytic unramifiedness for finite domain
  extensions;
- sampled owner declarations in the same chapter/project:
  `NagataRing`,
  `IsAnalyticallyUnramified`,
  `localization_nagataRing`,
  `isAnalyticallyUnramified_of_nagataRing`,
  `isN1Ring_of_forall_maximal_isAnalyticallyUnramified`;
- best owner abstraction: the source-facing owner for clause `(1)` is `NagataRing`, while the
  analytic condition in clauses `(2)` and `(3)` should be stated directly with the canonical owner
  `IsAnalyticallyUnramified`, not via a parallel reduced-completion wrapper;
- primitive data vs. derived API: the primitive data are the Noetherian local base ring `R` and,
  for each extension `S`, the finite/domain/local algebra structure. Localization at a maximal
  ideal and analytic unramifiedness are derived owner-level views, so the TFAE should use
  `Localization.AtPrime m.asIdeal` and `IsAnalyticallyUnramified` directly rather than introducing
  any new package or wrapper.

Source/core/bridge triage:
- `source-facing`: the TFAE relating the Nagata condition to analytically unramified finite domain
  extensions;
- `core/canonical`: `NagataRing`, `IsAnalyticallyUnramified`, `Localization.AtPrime`,
  `localization_nagataRing`, and `isAnalyticallyUnramified_of_nagataRing`;
- `bridge/view`: clause `(2)` passes from a finite domain algebra to its maximal localizations,
  while clause `(3)` is the local special case used to recover the owner `NagataRing`.
-/

-- Proof sketch: `(1) → (2)` by applying Nagata stability under finite extensions
-- (`Lemma 10.162.5`), then localizing (`Lemma 10.162.6`), and finally using that a local Nagata
-- domain is analytically unramified (`Lemma 10.162.13`). `(2) → (3)` is the special case obtained
-- by localizing a finite local domain algebra at its maximal ideal. For `(3) → (1)`, to prove
-- that `R` is Nagata one tests the `N-2` condition on each prime quotient by a finite field
-- extension, builds the corresponding finite local domain algebra, applies `(3)`, and then uses
-- `Lemma 10.162.10 (4)` to deduce finiteness of the integral closure.
/-- Lemma 10.162.14: for a Noetherian local ring `R`, the Nagata condition is equivalent to saying
that every localization `S_{m'}` of a finite domain `R`-algebra is analytically unramified, and is
also equivalent to saying that every finite local domain `R`-algebra is analytically unramified. -/
theorem nagataRing_tfae_analyticallyUnramified_finite_domain_extensions :
    List.TFAE
      [ NagataRing R,
        ∀ (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] [IsDomain S],
          ∀ m : MaximalSpectrum S, IsAnalyticallyUnramified (Localization.AtPrime m.asIdeal),
        ∀ (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] [IsDomain S]
          [IsLocalRing S] [IsLocalHom (algebraMap R S)],
          IsAnalyticallyUnramified S ] := sorry

end
