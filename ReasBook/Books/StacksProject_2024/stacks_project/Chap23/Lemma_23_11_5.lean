import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap15.Lemma_15_33_5
import StacksProject_2024.Chap23.Lemma_23_11_4

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Algebra

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "Synt" => RingHom.Syntomic (algebraMap A B)
local notation "LCI" => RingHom.IsLocalCompleteIntersection (algebraMap A B)

/-- Companion API: syntomicity of `A → B` already implies that `A → B` is a local complete
intersection, since flatness is built into `RingHom.Syntomic`. -/
theorem isLocalCompleteIntersection_of_syntomic (hSynt : Synt) : LCI :=
  (RingHom.Syntomic.iff_flat_and_isLocalCompleteIntersection (algebraMap A B)).mp hSynt |>.2

section

variable [Module.Flat A B]

/-- Under the standing flatness hypotheses of Lemma 23.11.5, syntomicity of `A → B` is equivalent
to `A → B` being a local complete intersection. -/
theorem syntomic_iff_isLocalCompleteIntersection :
    Synt ↔ LCI := by
  have hflat : (algebraMap A B).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  simpa [hflat] using
    (RingHom.Syntomic.iff_flat_and_isLocalCompleteIntersection (algebraMap A B))

end

end

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [Module.Flat A B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [RingHom.IsPerfectRingMap (algebraMap A B)]

local notation "NL" => naiveCotangentObject A B
local notation "Tor01" => HasTorAmplitudeIn NL (-1) 0
local notation "PerfTor01" => DerivedCategory.IsPerfect NL ∧ Tor01
local notation "Synt" => RingHom.Syntomic (algebraMap A B)
local notation "LCI" => RingHom.IsLocalCompleteIntersection (algebraMap A B)

/-- Companion API: under the standing Noetherian perfectness and flatness hypotheses, the naive
cotangent object has tor-amplitude in `[-1, 0]` exactly when `A → B` is syntomic. -/
theorem naiveCotangent_hasTorAmplitude_iff_syntomic :
    Tor01 ↔ Synt := by
  rw [syntomic_iff_isLocalCompleteIntersection]
  exact naiveCotangent_hasTorAmplitude_iff_isLocalCompleteIntersection

/-- Companion API: under the standing Noetherian perfectness and flatness hypotheses, the textbook
clause “`NL_{B/A}` is perfect and has tor-amplitude in `[-1, 0]`” is equivalent to `A → B` being
syntomic. -/
theorem naiveCotangent_perfect_and_hasTorAmplitude_iff_syntomic :
    PerfTor01 ↔ Synt := by
  rw [syntomic_iff_isLocalCompleteIntersection]
  exact naiveCotangent_perfect_and_hasTorAmplitude_iff_isLocalCompleteIntersection

/-- Lemma 23.11.5: for a flat perfect map `A → B` of Noetherian rings, the following are
equivalent: `NL_{B/A}` has tor-amplitude in `[-1, 0]`; `NL_{B/A}` is a perfect object of `D(B)`
with tor-amplitude in `[-1, 0]`; `A → B` is syntomic; and `A → B` is a local complete
intersection. -/
@[stacks 0FJV]
theorem naiveCotangent_torAmplitude_syntomic_tfae :
    ([Tor01, PerfTor01, Synt, LCI] : List Prop).TFAE := by
  tfae_have 1 ↔ 2 := naiveCotangent_hasTorAmplitude_iff_isPerfect_and_hasTorAmplitude
  tfae_have 1 ↔ 3 := naiveCotangent_hasTorAmplitude_iff_syntomic
  tfae_have 3 ↔ 4 := syntomic_iff_isLocalCompleteIntersection
  tfae_finish

end

end Algebra
