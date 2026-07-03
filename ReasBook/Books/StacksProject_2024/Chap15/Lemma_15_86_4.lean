import Mathlib
import StacksProject_2024.Chap10.Definition_10_134_1
import StacksProject_2024.Chap10.Lemma_10_134_3
import StacksProject_2024.Chap15.Definition_15_33_2
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_75_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open Algebra
open scoped NaiveCotangent

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [RingHom.IsLocalCompleteIntersection (algebraMap A B)]

/- Domain triage:
- primary domain: local complete intersection ring maps and the derived invariants of the
  canonical naive cotangent complex `NL_{B⁄A}`;
- sampled owner declarations:
  - `RingHom.IsLocalCompleteIntersection`, the chapter owner for the source-facing lci property;
  - `naiveCotangentObject A B`, the Chapter 10 bridge/view object of `NL_{B⁄A}` in `D(B)`;
  - `K.IsPerfect` and `HasTorAmplitudeIn`, the chapter owners for the two target
    derived properties.
- best owner abstraction: the primitive public datum is the lci owner
  `RingHom.IsLocalCompleteIntersection (algebraMap A B)`, while a chosen presentation
  `P : Generators A B (Fin n)` is bridge data supplied by Definition `15.33.2`.
- layer triage:
  - `source-facing`: the lci-facing perfectness and tor-amplitude theorems below;
  - `core/canonical`: `HasTorAmplitudeIn` and `DerivedCategory.IsPerfect` on
    `naiveCotangentObject A B`;
  - `bridge/view`: the chosen finite presentation witness from Definition `15.33.2`, used only
    internally in the proof. -/

/-- Lemma 15.86.4: if `A → B` is a local complete intersection ring map, then the naive
cotangent complex `NL_{B/A}` is perfect and has tor-amplitude in `[-1, 0]`. -/
theorem naiveCotangent_perfect_and_hasTorAmplitude_of_isLocalCompleteIntersection
    :
    (naiveCotangentObject A B).IsPerfect ∧
      HasTorAmplitudeIn (naiveCotangentObject A B) (-1) 0 := by
  sorry

/-- For a local complete intersection ring map, the naive cotangent complex `NL_{B/A}` is
perfect in `D(B)`. -/
theorem naiveCotangent_isPerfect_of_isLocalCompleteIntersection
    :
    (naiveCotangentObject A B).IsPerfect :=
  naiveCotangent_perfect_and_hasTorAmplitude_of_isLocalCompleteIntersection.1

/-- For a local complete intersection ring map, the naive cotangent complex `NL_{B/A}` has
tor-amplitude in `[-1, 0]`. -/
theorem naiveCotangent_hasTorAmplitude_of_isLocalCompleteIntersection
    :
    HasTorAmplitudeIn (naiveCotangentObject A B) (-1) 0 :=
  naiveCotangent_perfect_and_hasTorAmplitude_of_isLocalCompleteIntersection.2

end
