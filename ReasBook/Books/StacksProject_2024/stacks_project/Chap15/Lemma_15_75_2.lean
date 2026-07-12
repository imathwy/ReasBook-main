import Mathlib
import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_65_5
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_66_6

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open DerivedCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "ModR" => ModuleCat R
local notation "Cpx" => CochainComplex ModR ℤ
local notation "DMod" => DerivedCategory ModR
local notation "H" => DerivedCategory.homologyFunctor ModR
local notation "FiniteProjectiveClass" => (finiteProjectiveModuleProperty R)

/- Domain-style sampling for Lemma 15.75.2:
- primary domain: perfect objects in `D(R)` and their concrete finite-projective representatives;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `DerivedCategory.IsPseudoCoherent`,
  `HasTorAmplitudeIn`,
  `finiteProjectiveModuleProperty`,
  `CochainComplex.MinusWithTermsIn`;
- best owner abstraction: the main perfectness predicate is the source-facing owner
  `K.IsPerfect`, while explicit representative data should reuse the existing bounded-above owner
  `CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R)` rather than re-bundling
  boundedness through `CochainComplex.IsBoundedFiniteProjective` when the theorem already
  specifies the exact support interval `[a, b]`;
- primitive vs. derived:
  primitive data are the derived object `K`, the tor-amplitude interval `[a, b]`, and a
  representative complex with termwise finite-projective terms and explicit support bounds;
  the global boundedness package `CochainComplex.IsBoundedFiniteProjective` is derived from those
  explicit bounds and should not be duplicated in the representative theorem below;
- source/core/bridge triage:
  `source-facing`: perfectness characterized by pseudo-coherence and finite tor dimension;
  `core/canonical`: `K.IsPerfect`, `K.IsPseudoCoherent`, `HasFiniteTorDimension K`, and the owner
    `CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R)`;
  `bridge/view`: the representative theorem below, which presents perfectness data through a
    chosen bounded-above finite-projective model with fixed support bounds.
-/

/-- Helper for Lemma 15.75.2: pseudo-coherence is preserved by isomorphisms in `D(R)`. -/
lemma isPseudoCoherent_of_iso {K L : DMod} (e : K ≅ L)
    (hK : K.IsPseudoCoherent) :
    L.IsPseudoCoherent := by
  rcases hK with ⟨E, hEbounded, hEfree, α, hα⟩
  -- Proof comment: compose the chosen bounded-above finite-free representative with the target
  -- isomorphism.
  refine ⟨E, hEbounded, hEfree, α ≫ e.hom, ?_⟩
  simpa using (show IsIso (α ≫ e.hom) by infer_instance)

/-- Helper for Lemma 15.75.2: a bounded termwise-flat representative supported in `[a, b]`
realizes tor-amplitude in `[a, b]`. -/
private theorem hasTorAmplitudeIn_of_flat_representative
    {K : DMod} {E : Cpx} {a b : ℤ}
    (e : K ≅ DerivedCategory.Q.obj E)
    (hGE : E.IsStrictlyGE a) (hLE : E.IsStrictlyLE b) (hFlat : E.IsTermwiseFlat) :
    HasTorAmplitudeIn K a b := by
  -- TODO(Lemma 15.75.2): finish the standard tensor-comparison argument once a compileable local
  -- replacement for the broken `Lemma_15_67_2` infrastructure is available. The intended route is
  -- to compute derived tensor products on the termwise-flat bounded-above representative `E` and
  -- then read off vanishing from the support bounds `hGE` and `hLE`.
  sorry

/-- Helper for Lemma 15.75.2: a bounded finite-projective complex is pseudo-coherent. -/
private theorem isPseudoCoherent_of_isBoundedFiniteProjective
    (L : CochainComplex (ModuleCat.{u} R) ℤ) [hL : CochainComplex.IsBoundedFiniteProjective L] :
    L.IsPseudoCoherent := by
  rcases hL.bounded with ⟨_, b, _, hLLE⟩
  have hLminus : CochainComplex.minus (ModuleCat.{u} R) L := by
    -- Proof comment: the bounded finite-projective hypothesis already gives the bounded-above
    -- side needed to package `L` as an object of `MinusWithTermsIn`.
    exact (CochainComplex.minus_iff (ModuleCat.{u} R) L).2 ⟨b, hLLE⟩
  have hTerms : ∀ i : ℤ, Module.Finite R (L.X i) ∧ Projective (L.X i) := by
    intro i
    refine ⟨hL.finite i, ?_⟩
    let _ : Module.Projective R (L.X i) := hL.projective i
    infer_instance
  let P : CochainComplex.MinusWithTermsIn
      (fun M : ModuleCat.{u} R ↦ Module.Finite R M ∧ Projective M) :=
    ⟨⟨L, hLminus⟩, hTerms⟩
  have hTFAE := cochainComplex_pseudoCoherent_tfae (R := R) L
  have hIdQuasi : QuasiIso (𝟙 L) := by
    infer_instance
  -- Proof comment: apply the bounded-above finite-projective leg of Lemma `15.65.5` to the
  -- explicit witness coming from `L` itself.
  have hWitness :
      ∃ P : CochainComplex.MinusWithTermsIn
          (fun M : ModuleCat.{u} R ↦ Module.Finite R M ∧ Projective M),
        ∃ α : (P : CochainComplex (ModuleCat.{u} R) ℤ) ⟶ L, QuasiIso α := by
    exact ⟨P, 𝟙 L, hIdQuasi⟩
  exact (hTFAE.out 2 0).mp hWitness

/-- Helper for Lemma 15.75.2: pseudo-coherence plus tor-amplitude yields a finite-projective
representative supported in the same interval. -/
private theorem exists_strictlySupported_finiteProjective_complex_aux
    {K : DMod} {a b : ℤ}
    (hKpc : K.IsPseudoCoherent) (hamp : HasTorAmplitudeIn K a b) :
    ∃ E : CochainComplex.MinusWithTermsIn FiniteProjectiveClass,
      ∃ (_ : K ≅ DerivedCategory.Q.obj (E : Cpx)),
        (E : Cpx).IsStrictlyGE a ∧ (E : Cpx).IsStrictlyLE b := by
  -- TODO(Lemma 15.75.2): after choosing a bounded-above finite-free model with support `≤ b`
  -- from `exists_boundedAbove_termwiseFiniteFree_quasiIso`, smart-truncate below `a`, identify
  -- the cutoff term with `differentialCokernel`, and use the missing local replacement for the
  -- broken cutoff-flatness API from `Lemma_15_67_2` to upgrade that term to finite projective.
  sorry

-- Proof sketch: combine the bounded finite-projective representative from `IsPerfect` with the
-- flat-representative criterion of Lemma `15.67.3` to obtain pseudo-coherence and finite tor
-- dimension, and conversely use the explicit finite-projective representative built from
-- pseudo-coherence plus tor-amplitude.
/-- Lemma 15.75.2: an object `K^•` of `D(R)` is perfect if and only if it is pseudo-coherent and
has finite tor dimension. -/
theorem isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
    (K : DMod) :
    K.IsPerfect ↔ K.IsPseudoCoherent ∧ HasFiniteTorDimension K := by
  constructor
  · rintro ⟨L, e, hL⟩
    have hLpc : L.IsPseudoCoherent := by
      -- Proof comment: the only missing forward-input bridge is the standard stabilization from
      -- finite-projective terms to finite-free terms.
      exact isPseudoCoherent_of_isBoundedFiniteProjective (R := R) L
    have hpc : K.IsPseudoCoherent := by
      exact isPseudoCoherent_of_iso e.symm hLpc
    rcases hL.bounded with ⟨a, b, hGE, hLE⟩
    have hFlat : L.IsTermwiseFlat := by
      intro i
      let _ : Module.Projective R (L.X i) := hL.projective i
      infer_instance
    have hAmpK : HasTorAmplitudeIn K a b := by
      -- Proof comment: the bounded finite-projective representative is termwise flat, so the
      -- tensor homology vanishes outside `[a, b]` by direct support inspection.
      exact hasTorAmplitudeIn_of_flat_representative (R := R) e hGE hLE hFlat
    exact ⟨hpc, hAmpK.hasFiniteTorDimension⟩
  · rintro ⟨hKpc, hKtor⟩
    rcases hKtor with ⟨a, b, hAmp⟩
    obtain ⟨E, e, hEGE, hELE⟩ :=
      exists_strictlySupported_finiteProjective_complex_aux (R := R) hKpc hAmp
    refine ⟨(E : Cpx), e, ?_⟩
    refine ⟨⟨a, b, hEGE, hELE⟩, ?_, ?_⟩
    · intro i
      exact (E.term_mem i).1
    · intro i
      exact (E.term_mem i).2

-- Proof sketch: choose a bounded-above finite-free representative from pseudo-coherence, cut it
-- down to degrees `≤ b`, then smart-truncate below `a`; the remaining cutoff-flatness bridge is
-- exactly the localized substitute for Lemma `15.67.2`.
/-- For a pseudo-coherent object, tor-amplitude in `[a, b]` yields a
representative by finite projective `R`-modules concentrated in degrees `[a, b]`. -/
theorem exists_strictlySupported_finiteProjective_complex_of_isPseudoCoherent_of_hasTorAmplitudeIn
    {K : DMod} {a b : ℤ}
    (hKpc : K.IsPseudoCoherent) (hamp : HasTorAmplitudeIn K a b) :
    ∃ E : CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R),
      ∃ (_ : K ≅ DerivedCategory.Q.obj (E : Cpx)),
        (E : Cpx).IsStrictlyGE a ∧ (E : Cpx).IsStrictlyLE b := by
  -- Proof comment: this is exactly the localized truncation construction isolated above.
  exact exists_strictlySupported_finiteProjective_complex_aux (R := R) hKpc hamp

end

end CategoryTheory
