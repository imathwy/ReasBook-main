import StacksProject_2024.Chap15.Definition_15_33_2
import StacksProject_2024.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingHom

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [Algebra A B] [IsNoetherianRing A] [Algebra.FiniteType A B]

/- Source/core/bridge triage:
* source-facing: the primewise completed-localization criterion for local complete intersection
  maps from Lemma 23.9.5;
* core/canonical: `RingHom.IsLocalCompleteIntersection` and the chapter owner
  `CompletedLocalizationAtPrime.map`;
* bridge/view: the theorem restates the textbook condition directly in terms of the canonical map
  on completed localizations, rather than the raw composite
  `maximalIdealCompletionMap (Localization.localRingHom ...)`.
-/

/-- Lemma 23.9.5: for a finite type ring map `f : A →+* B` with `A` Noetherian, `f` is a local
complete intersection in the sense of Definition `15.33.2` if and only if for every prime
`q ⊂ B`, writing `p = q ∩ A`, the induced map on completed localizations `(A_p)^∧ → (B_q)^∧`
is a complete intersection homomorphism. -/
@[stacks 09QE]
theorem isLocalCompleteIntersection_iff_forall_prime_completion_localRingHom :
    RingHom.IsLocalCompleteIntersection (algebraMap A B) ↔
      ∀ q : PrimeSpectrum B,
        RingHom.IsLocalCompleteIntersection
          (CompletedLocalizationAtPrime.map
            (PrimeSpectrum.comap (algebraMap A B) q) q rfl) := sorry

end

end RingHom
