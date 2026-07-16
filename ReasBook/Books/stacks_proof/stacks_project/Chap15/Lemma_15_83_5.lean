import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_110_8
import stacks_proof.stacks_project.Chap15.Definition_15_105_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

namespace RingHom

/-- Helper for Lemma 15.83.5: the presentationwise finiteness condition used in this file as a
local witness for pseudo-coherence of a finite type ring map. -/
abbrev PresentationwiseFinite {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B) (_ : Function.Surjective α),
    let _ : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
    Module.Finite (MvPolynomial (Fin n) A) B

/-- Helper for Lemma 15.83.5: a ring map is pseudo-coherent if it is of finite type and the
target ring is presentationwise finite over every surjective polynomial presentation of the base.
This is the local source-faithful criterion used by this item. -/
class IsPseudoCoherentRingMap {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (f : A →+* B) : Prop where
  /-- A pseudo-coherent ring map is of finite type. -/
  finiteType : f.FiniteType
  /-- The target is finite over every surjective polynomial presentation of the base. -/
  isPseudoCoherentRelativeTo : PresentationwiseFinite (A := A) (B := B)

/-- Helper for Lemma 15.83.5: a ring map is perfect if it is pseudo-coherent and the target has
finite tor dimension as a module over the base. -/
class IsPerfectRingMap {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (f : A →+* B) : Prop
    extends IsPseudoCoherentRingMap f where
  /-- The target ring has finite tor dimension as a module over the base ring. -/
  hasFiniteTorDimension : ModuleHasFiniteTorDimension (ModuleCat.of A B)

attribute [instance] IsPerfectRingMap.hasFiniteTorDimension

end RingHom

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
/-- Helper for Lemma 15.83.5: a regular nontrivial ring with a finite Krull-dimension bound has
finite global dimension. -/
private theorem isFiniteGlobalDimensionRing_of_isRegularRing_of_exists_krullDimLE
    (A : Type u) [CommRing A] [IsRegularRing A] [Nontrivial A]
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A) :
    IsFiniteGlobalDimensionRing A := by
  obtain ⟨d, hd⟩ := hfinite
  -- The finite-dimensional hypothesis rules out `⊤`, so the Krull dimension is an actual natural
  -- number after removing the bottom value forced away by nontriviality.
  have hneTop : ringKrullDim A ≠ ⊤ := by
    have hdTop : ((d : ℕ∞) : WithBot ℕ∞) ≠ ⊤ := by
      intro h
      cases h
    exact ne_of_lt (lt_of_le_of_lt (Ring.krullDimLE_iff.mp hd) (lt_top_iff_ne_top.mpr hdTop))
  have hbot : ringKrullDim A ≠ ⊥ := by
    have hnonneg : (0 : WithBot ℕ∞) ≤ ringKrullDim A := by
      simpa using (ringKrullDim_nonneg_of_nontrivial (R := A))
    exact ne_of_gt <| lt_of_lt_of_le (by simp) hnonneg
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

/-- Helper for Lemma 15.83.5: a weak-dimension bound packages into finite tor dimension for any
module. -/
private theorem moduleCat_hasFiniteTorDimension_of_hasWeakDimensionLE
    {R : Type u} [CommRing R] (d : ℕ) [HasWeakDimensionLE R d] (M : ModuleCat R) :
    ModuleHasFiniteTorDimension M := by
  -- The weak-dimension owner already supplies Tor-amplitude in `[-d, 0]`, which is exactly a
  -- finite tor-dimension witness.
  let hwd : HasWeakDimensionLE R d := inferInstance
  have hM : ModuleHasTorDimensionLE M d := hwd.hasTorDimensionLE M
  exact ⟨-(d : ℤ), 0, hM⟩

/-- Helper for Lemma 15.83.5: a finite type map is presentationwise finite over every surjective
polynomial presentation. -/
private theorem presentationwiseFinite_of_finiteType
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] :
    RingHom.PresentationwiseFinite (A := A) (B := B) := by
  intro n α hα
  let P := MvPolynomial (Fin n) A
  letI : Algebra P B := α.toAlgebra
  letI : Module P B := Module.compHom B α.toRingHom
  letI : Module.Finite P B := AlgHom.Finite.of_surjective α hα
  exact inferInstance

/-- Helper for Lemma 15.83.5: a subsingleton ring has global dimension at most `0`. -/
private theorem hasGlobalDimensionLE_zero_of_subsingleton_ring
    (A : Type u) [CommRing A] [Subsingleton A] :
    HasGlobalDimensionLE A 0 where
  hasProjectiveDimensionLE M := by
    letI : Subsingleton M := Module.subsingleton A M
    have hzero : Limits.IsZero M := ModuleCat.isZero_of_subsingleton M
    -- Every module is isomorphic to the zero object, hence projective, so its projective
    -- dimension is at most `0`.
    have hprojective : Projective M := by
      exact Projective.of_iso hzero.isoZero.symm inferInstance
    exact (projective_iff_hasProjectiveDimensionLE_zero M).1 hprojective

-- Proof sketch: by Lemma `10.110.8`, a regular ring of finite dimension has finite global
-- dimension. Hence the canonical instance chain
-- `HasGlobalDimensionLE A d ⟹ HasWeakDimensionLE A d ⟹ ModuleHasTorDimensionLE (ModuleCat.of A B) d`
-- gives finite tor dimension for `B`, while Lemma `15.83.3` gives pseudo-coherence for the
-- finite type map `A → B`.
/-- Lemma 15.83.5: a finite type ring map `A → B` with `A` regular of finite Krull dimension is a
perfect ring map. The finite-dimensional hypothesis is carried by the canonical bridge
`∃ d : ℕ, Ring.KrullDimLE d A`. -/
@[stacks 067K]
theorem isPerfectRingMap_of_finiteType_of_isRegularRing_of_finiteDimension
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsRegularRing A] [Algebra.FiniteType A B] (hfinite : ∃ d : ℕ, Ring.KrullDimLE d A) :
    (algebraMap A B).IsPerfectRingMap := by
  classical
  have hPseudo : (algebraMap A B).IsPseudoCoherentRingMap := by
    refine ⟨RingHom.finiteType_algebraMap.mpr inferInstance, ?_⟩
    exact presentationwiseFinite_of_finiteType (A := A) (B := B)
  cases subsingleton_or_nontrivial A with
  | inl hA =>
      letI : Subsingleton A := hA
      letI : HasGlobalDimensionLE A 0 := hasGlobalDimensionLE_zero_of_subsingleton_ring A
      refine
        { toIsPseudoCoherentRingMap := hPseudo
          hasFiniteTorDimension := by
            exact moduleCat_hasFiniteTorDimension_of_hasWeakDimensionLE 0 (ModuleCat.of A B) }
  | inr hA =>
      letI : Nontrivial A := hA
      letI : IsFiniteGlobalDimensionRing A :=
        isFiniteGlobalDimensionRing_of_isRegularRing_of_exists_krullDimLE A hfinite
      refine
        { toIsPseudoCoherentRingMap := hPseudo
          hasFiniteTorDimension := by
            exact
              moduleCat_hasFiniteTorDimension_of_hasWeakDimensionLE
                (globalDimension A) (ModuleCat.of A B) }

end Algebra
