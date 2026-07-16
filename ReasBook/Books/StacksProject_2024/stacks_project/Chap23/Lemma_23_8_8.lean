import StacksProject_2024.stacks_project.Chap10.Lemma_10_135_9
import StacksProject_2024.stacks_project.Chap23.Definition_23_8_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Algebra

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-
Source/core/bridge triage:
* source-facing: the two bridge theorems below, comparing the Chapter 10 field-algebra owners with
  the Chapter 23 local-ring owners;
* core/canonical: `Algebra.IsCompleteIntersectionOver`, `IsLocalCompleteIntersection`,
  `IsCompleteIntersectionLocalRing`, and `IsLocalCompleteIntersectionRing`;
* bridge/view: the primewise equivalence in `(1)` and the global equivalence in `(2)`, where the
  latter should reuse the existing prime-local criterion from `Lemma_10_135_9` instead of
  rebuilding a separate local-complete-intersection API.
-/

/-- Lemma 23.8.8 (1): for a finite type `k`-algebra `S` and a prime `q` of `S`, the local ring
`S_q` is a complete intersection in the sense of Algebra, Definition 10.135.5 if and only if
`S_q` is a complete intersection in the sense of Definition 23.8.5. -/
@[stacks 09Q6 "(1)"]
theorem completeIntersectionOver_atPrime_iff_completeIntersectionLocalRing
    (q : PrimeSpectrum S) :
    IsCompleteIntersectionOver.{u, v, v} k (Localization.AtPrime q.asIdeal) ↔
      IsCompleteIntersectionLocalRing (Localization.AtPrime q.asIdeal) := sorry

/-- Lemma 23.8.8 (2): for a finite type `k`-algebra `S`, the ring `S` is a local complete
intersection in the sense of Algebra, Definition 10.135.1 if and only if `S` is a local complete
intersection in the sense of Definition 23.8.5. -/
@[stacks 09Q6 "(2)"]
theorem isLocalCompleteIntersection_iff_isLocalCompleteIntersectionRing :
    IsLocalCompleteIntersection k S ↔ IsLocalCompleteIntersectionRing S := by
  have htfae :
      List.TFAE
        [ IsLocalCompleteIntersection k S
        , ∀ q : PrimeSpectrum S, IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal)
        , ∀ m : MaximalSpectrum S, IsCompleteIntersectionOver k (Localization.AtPrime m.asIdeal)
        ] :=
    isLocalCompleteIntersection_tfae_completeIntersectionOver_localRings.{u, v, v, v}
  constructor
  · intro hS
    letI : IsNoetherianRing S := FiniteType.isNoetherianRing k S
    exact IsLocalCompleteIntersectionRing.of_localizationAtPrime S
      (fun q ↦
        (completeIntersectionOver_atPrime_iff_completeIntersectionLocalRing
          q).mp
            ((htfae.out 0 1 rfl rfl).mp hS q))
  · intro hS
    exact
      (htfae.out 0 1 rfl rfl).mpr
        (fun q ↦
          (completeIntersectionOver_atPrime_iff_completeIntersectionLocalRing
            q).mpr (hS.completeIntersection_atPrime q))

end
