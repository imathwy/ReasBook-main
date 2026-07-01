import stacks_project.Chap10.Definition_10_54_1
import stacks_project.Chap10.Lemma_10_127_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w uR uS

section

variable {R : Type uR} {S : Type uS} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

/-
Domain sampling:
* Primary domain: directed approximation systems for local homomorphisms of local rings in
  commutative algebra.
* Owner declarations inspected in this domain:
  - `DirectedLocalHomApproximation`
  - `DirectedLocalHomApproximation.targetStageBaseChange`
  - `DirectedLocalHomApproximation.stageBaseChangeMap`
  - `RingHom.EssFinitePresentation`
* Best owner abstraction: `DirectedLocalHomApproximation f` is the source-facing approximation
  object; “the transition base-change maps are localizations at prime ideals” is derived
  transition behavior of that owner, not new primitive data.
* Primitive vs. derived: the directed system, stage rings, local maps, and colimit identifications
  are primitive owner data from `Lemma_10_127_9`; prime-localization transition behavior is a
  property of those canonical base-change maps.
-/

namespace DirectedLocalHomApproximation

/-- A transition in a directed local approximation presents the later target stage as a
localization at a prime ideal of the corresponding base-change ring. -/
def TransitionIsLocalizationAtPrime {f : R →+* S} (A : DirectedLocalHomApproximation f)
    {i j : A.Λ} (h : i ≤ j) : Prop :=
  ∃ q : Ideal (A.targetStageBaseChange h),
    ∃ _ : q.IsPrime, q.primeCompl.IsLocalizationMap (A.stageBaseChangeMap h)

/-- Every transition in a directed local approximation is a localization at a prime ideal. -/
def HasPrimeLocalizationTransitions {f : R →+* S} (A : DirectedLocalHomApproximation f) : Prop :=
  ∀ {i j : A.Λ} (h : i ≤ j), A.TransitionIsLocalizationAtPrime h

/-- A directed local approximation has a transition whose canonical base-change map is not a
localization at a prime ideal. -/
def HasFailingPrimeLocalizationTransition {f : R →+* S} (A : DirectedLocalHomApproximation f) :
    Prop :=
  ∃ (i j : A.Λ) (h : i ≤ j), ¬ A.TransitionIsLocalizationAtPrime h

end DirectedLocalHomApproximation

variable (f : R →+* S) [IsLocalHom f]

-- Proof sketch: choose an essentially finitely presented local presentation of `S` over `R`,
-- write `R` as a directed colimit of local rings essentially of finite type over `ℤ`, descend the
-- finitely many generators and relations of the presentation to a sufficiently large stage, and
-- localize at the inverse images of the chosen prime.
/-- Lemma 10.127.11: if `f : R →+* S` is a local homomorphism of local rings and `S` is essentially
of finite presentation over `R`, then there is a directed system of local homomorphisms
approximating `f` whose source stages are essentially of finite type over `ℤ`, whose target
stages are essentially of finite type over the corresponding source stages, and whose transition
maps identify each stage after base change with a localization at a prime ideal. -/
theorem exists_localEssFinitePresentationApproximation
    (hf : f.EssFinitePresentation) :
    ∃ A : DirectedLocalHomApproximation f,
      DirectedLocalHomApproximation.HasPrimeLocalizationTransitions A := sorry

end
