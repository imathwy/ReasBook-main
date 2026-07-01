import Mathlib
import stacks_project.Chap10.Lemma_10_110_8
import stacks_project.Chap15.Definition_15_105_3
import stacks_project.Chap15.Definition_15_83_1
import stacks_project.Chap15.Lemma_15_83_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

namespace Algebra

/- Domain-style sampling for Lemma 15.83.5:
- primary domain: perfect ring maps out of regular rings of finite Krull dimension;
- sampled owner declarations:
  `RingHom.IsPerfectRingMap`,
  `Ring.KrullDimLE`,
  `RingHom.IsPseudoCoherentRingMap`,
  `IsRegularRing`,
  `IsFiniteGlobalDimensionRing`,
  `globalDimension`;
- best owner abstraction: `RingHom.IsPerfectRingMap` on `algebraMap A B` is the owner of the
  conclusion, while `IsRegularRing`, `Ring.KrullDimLE`, `IsFiniteGlobalDimensionRing`, and
  `globalDimension` are the chapter owners for the finite-dimensional regularity input and its
  finite-global-dimension consequence;
- primitive vs. derived:
  the source-facing input is `[IsRegularRing A]` together with the canonical finite-dimensional
  bridge `∃ d : ℕ, Ring.KrullDimLE d A`;
  the derived API is pseudo-coherence from Lemma `15.83.3` and finite tor dimension from
  finite global dimension via Lemma `15.67.19`;
- source/core/bridge triage:
  `source-facing`: the theorem below with the canonical finite-dimension bridge;
  `core/canonical`: `RingHom.IsPerfectRingMap`, `Ring.KrullDimLE`, `IsRegularRing`,
    `IsFiniteGlobalDimensionRing`, `globalDimension`;
  `bridge/view`: the private proof-only passage from a finite Krull-dimension bound to the exact
    dimension witness required by `finiteGlobalDimension_regularRing_localizations_tfae`.
-/
private theorem isFiniteGlobalDimensionRing_of_isRegularRing_of_exists_krullDimLE
    (A : Type u) [CommRing A] [IsRegularRing A] [Nontrivial A]
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A) :
    IsFiniteGlobalDimensionRing A := by
  obtain ⟨d, hd⟩ := hfinite
  have hneTop : ringKrullDim A ≠ ⊤ := by
    exact ne_of_lt
      (lt_of_le_of_lt (Ring.krullDimLE_iff.mp hd)
        (lt_top_iff_ne_top.mpr (by
          intro htop
          exact ENat.coe_ne_top d (WithBot.coe_eq_top.mp htop))))
  have hbot : ringKrullDim A ≠ ⊥ := by
    exact bot_lt_iff_ne_bot.mp (lt_of_lt_of_le (by simp) ringKrullDim_nonneg_of_nontrivial)
  let n : ℕ := ((ringKrullDim A).unbot hbot).toNat
  have hnneTop : (ringKrullDim A).unbot hbot ≠ ⊤ := by
    intro htop
    exact hneTop (by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop)
  have hdim' : ((ringKrullDim A).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hnneTop).symm
  have hdim : ringKrullDim A = n := by
    calc
      ringKrullDim A = (ringKrullDim A).unbot hbot := (WithBot.coe_unbot (ringKrullDim A) hbot).symm
      _ = n := hdim'
  have hregular : IsRegularRing A ∧ ringKrullDim A = n := ⟨inferInstance, hdim⟩
  rcases (((finiteGlobalDimension_regularRing_localizations_tfae n).out 1 0).mp
      hregular) with ⟨hA, _⟩
  exact hA

-- Proof sketch: by Lemma `10.110.8`, a regular ring of finite dimension has finite global
-- dimension. Hence the canonical instance chain
-- `HasGlobalDimensionLE A d ⟹ HasWeakDimensionLE A d ⟹ ModuleHasTorDimensionLE (ModuleCat.of A B) d`
-- gives finite tor dimension for `B`, while Lemma `15.83.3` gives pseudo-coherence for the
-- finite type map `A → B`.
/-- Lemma 15.83.5: a finite type ring map `A → B` with `A` regular of finite Krull dimension is a
perfect ring map. The finite-dimensional hypothesis is carried by the canonical bridge
`∃ d : ℕ, Ring.KrullDimLE d A`. -/
theorem isPerfectRingMap_of_finiteType_of_isRegularRing_of_finiteDimension
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsRegularRing A] [Algebra.FiniteType A B] (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A) :
    (algebraMap A B).IsPerfectRingMap := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl hA =>
      letI : Subsingleton A := hA
      letI : Subsingleton B := Algebra.subsingleton A B
      haveI : HasGlobalDimensionLE A 0 := {
        hasProjectiveDimensionLE M := by
          letI : Subsingleton M := Module.subsingleton A M
          have hM : Limits.IsZero M := ModuleCat.isZero_of_subsingleton M
          letI : HasProjectiveDimensionLT M 0 := hM.hasProjectiveDimensionLT_zero
          exact (projective_iff_hasProjectiveDimensionLE_zero M).mp inferInstance }
      refine
        { toIsPseudoCoherentRingMap := inferInstance
          hasFiniteTorDimension := by
            let _ : Algebra A B := (algebraMap A B).toAlgebra
            have hwd : HasWeakDimensionLE A 0 := inferInstance
            have htor : ModuleHasTorDimensionLE (ModuleCat.of A B) 0 :=
              hwd.hasTorDimensionLE (ModuleCat.of A B)
            refine ⟨0, 0, ?_⟩
            simpa [ModuleHasTorDimensionLE] using htor }
  | inr hA =>
      letI : Nontrivial A := hA
      letI : IsFiniteGlobalDimensionRing A :=
        isFiniteGlobalDimensionRing_of_isRegularRing_of_exists_krullDimLE A hfinite
      refine
        { toIsPseudoCoherentRingMap := inferInstance
          hasFiniteTorDimension := by
            let _ : Algebra A B := (algebraMap A B).toAlgebra
            have hwd : HasWeakDimensionLE A (globalDimension A) := inferInstance
            have htor : ModuleHasTorDimensionLE (ModuleCat.of A B) (globalDimension A) :=
              hwd.hasTorDimensionLE (ModuleCat.of A B)
            refine ⟨-(globalDimension A : ℤ), 0, ?_⟩
            simpa [ModuleHasTorDimensionLE] using htor }

end Algebra
