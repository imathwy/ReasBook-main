import StacksProject_2024.Chap15.Lemma_15_83_2
import StacksProject_2024.Chap15.Lemma_15_86_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Algebra

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [RingHom.IsPerfectRingMap (algebraMap A B)]

local notation "NL" => naiveCotangentObject A B
local notation "Tor01" => HasTorAmplitudeIn NL (-1) 0
local notation "LCI" => RingHom.IsLocalCompleteIntersection (algebraMap A B)
local notation "PerfTor01" => DerivedCategory.IsPerfect NL ∧ Tor01

/-- Lemma 23.11.4 (2): for a perfect ring map of Noetherian rings, if the naive cotangent object
`NL_{B/A}` has tor-amplitude in `[-1, 0]`, then `A → B` is a local complete intersection. This is
the source-faithful implication behind the corresponding equivalence. -/
@[stacks 0FJT "(2)"]
theorem isLocalCompleteIntersection_of_naiveCotangent_hasTorAmplitude
    (hTor : Tor01) : LCI := by
  sorry

/-- Lemma 23.11.4 (1): for a perfect ring map of Noetherian rings, if the naive cotangent object
`NL_{B/A}` has tor-amplitude in `[-1, 0]`, then it is a perfect object of `D(B)`. This is the
canonical owner behind the textbook equivalence with “perfect and has tor-amplitude in `[-1, 0]`”.
-/
@[stacks 0FJT "(1)"]
theorem naiveCotangent_isPerfect_of_hasTorAmplitude
    (hTor : Tor01) : DerivedCategory.IsPerfect NL := by
  let _ : LCI := isLocalCompleteIntersection_of_naiveCotangent_hasTorAmplitude hTor
  exact naiveCotangent_isPerfect_of_isLocalCompleteIntersection

/-- Companion API: the textbook clause “`NL_{B/A}` is perfect and has tor-amplitude in
`[-1, 0]`” already follows from tor-amplitude alone under the standing perfectness hypotheses. -/
theorem naiveCotangent_perfect_and_hasTorAmplitude_of_hasTorAmplitude
    (hTor : Tor01) : PerfTor01 :=
  ⟨naiveCotangent_isPerfect_of_hasTorAmplitude hTor, hTor⟩

/-- Companion API: repackage Lemma 23.11.4 (1) in the clause-level textbook form. -/
theorem naiveCotangent_hasTorAmplitude_iff_isPerfect_and_hasTorAmplitude :
    Tor01 ↔ PerfTor01 := by
  exact ⟨naiveCotangent_perfect_and_hasTorAmplitude_of_hasTorAmplitude, fun h ↦ h.2⟩

/-- Companion API: under the standing perfectness hypotheses, tor-amplitude in `[-1, 0]` for the
naive cotangent object is equivalent to `A → B` being a local complete intersection. -/
theorem naiveCotangent_hasTorAmplitude_iff_isLocalCompleteIntersection :
    Tor01 ↔ LCI := by
  constructor
  · exact isLocalCompleteIntersection_of_naiveCotangent_hasTorAmplitude
  · intro hLCI
    let _ : LCI := hLCI
    exact naiveCotangent_hasTorAmplitude_of_isLocalCompleteIntersection

/-- Companion API: under the standing perfectness hypotheses, the textbook clause
“`NL_{B/A}` is perfect and has tor-amplitude in `[-1, 0]`” is equivalent to `A → B` being a
local complete intersection. This is the direct clause-to-clause bridge used by the subsequent
TFAE packaging. -/
theorem naiveCotangent_perfect_and_hasTorAmplitude_iff_isLocalCompleteIntersection :
    PerfTor01 ↔ LCI := by
  rw [← naiveCotangent_hasTorAmplitude_iff_isPerfect_and_hasTorAmplitude]
  exact naiveCotangent_hasTorAmplitude_iff_isLocalCompleteIntersection

end

end Algebra
