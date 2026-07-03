import Mathlib
import StacksProject_2024.Chap10.Definition_10_104_1
import StacksProject_2024.Chap10.Lemma_10_68_5
import StacksProject_2024.Chap10.Lemma_10_104_2
import StacksProject_2024.Chap10.Lemma_10_112_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory Sequence
open IsLocalRing
open scoped TensorProduct

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R]

/-
Source/core/bridge triage:
* primary domain: Cohen-Macaulay local rings under flat local base change in commutative algebra;
* sampled owner API:
  `Module.CohenMacaulay R R` from Definition `10.104.1`,
  `isRegular_iff_isRegular_tensorBaseChange_of_flat_localHom` from Lemma `10.68.5`,
  `exists_maximal_regularSequence_extension_of_ringKrullDim_quotient_add_length_eq` from
    Lemma `10.104.2`,
  `ringKrullDim_eq_of_injective_algebraMap_of_isIntegral` from Lemma `10.112.4`;
* source-facing: the four ascent/equality statements of Lemma `10.112.9`;
* core/canonical: `Module.CohenMacaulay`, `ringKrullDim`, and `RingTheory.Sequence.IsRegular`;
* bridge/view: flat local base change of regular sequences and the integral-dimension comparison.

Primitive data are only the source Cohen-Macaulay owner hypothesis on `R`, together with flatness,
finite generation where required, and the Krull-dimension comparison in parts `(3)` and `(4)`.
For part `(1)`, target-side Noetherianity is derived from the owner theorem
`IsNoetherianRing.of_finite` rather than stored as primitive public context. The dimension-equality
claims are derived API from the sampled owner lemmas above, so this file should reuse those owners
directly rather than restating a parallel local dimension wrapper.
-/

/-- Helper for Lemma 10.112.9: a Cohen--Macaulay Noetherian local ring carries a regular sequence
whose length is the Krull dimension. -/
private theorem exists_maximal_regularSequence_self_of_cohenMacaulay
    (hCM : Module.CohenMacaulay R R) :
    ∃ xs : List R, IsRegular R xs ∧ ringKrullDim R = xs.length := by
  letI : Module.CohenMacaulay R R := hCM
  have hxs : ∀ x ∈ ([] : List R), x ∈ maximalIdeal R := by
    simp
  have hquot :
      ringKrullDim (R ⧸ Ideal.ofList ([] : List R)) + ([] : List R).length = ringKrullDim R := by
    -- Rewrite the empty quotient as `R` itself.
    rw [Ideal.ofList_nil]
    simpa using
      ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R : R ⧸ (⊥ : Ideal R) ≃+* R)
  simpa using
    exists_maximal_regularSequence_extension_of_ringKrullDim_quotient_add_length_eq hxs hquot

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.112.9: flat local base change carries a regular sequence on `R` to the
corresponding regular sequence on `S`. -/
private theorem isRegular_map_self_of_flat_localHom [Module.Flat R S] {xs : List R}
    (hreg : IsRegular R xs) :
    IsRegular S (xs.map (algebraMap R S)) := by
  -- Route correction: Lemma `10.68.5` lands in `S ⊗[R] R`, so we transport across the tensor-unit
  -- equivalence to recover a regular sequence directly on `S`.
  have hregTensor : IsRegular (S ⊗[R] R) (xs.map (algebraMap R S)) :=
    (isRegular_iff_isRegular_tensorBaseChange_of_flat_localHom
      (R := R) (S := S) (M := R) (rs := xs)).mp hreg
  simpa using ((Algebra.TensorProduct.rid R S S).toLinearEquiv.isRegular_congr _).mp hregTensor

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.112.9: a finite flat local homomorphism preserves Krull dimension. -/
private theorem ringKrullDim_eq_of_finiteFlat_localHom_aux [Module.Finite R S] [Module.Flat R S] :
    ringKrullDim R = ringKrullDim S := by
  -- Faithful flatness gives injectivity of the algebra map, and finiteness gives integrality.
  letI : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hff : (algebraMap R S).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  exact ringKrullDim_eq_of_injective_algebraMap_of_isIntegral hff.injective

/-- Helper for Lemma 10.112.9: in a Noetherian local ring, a regular sequence whose length already
equals the Krull dimension forces the ring to be Cohen--Macaulay. -/
private theorem cohenMacaulay_self_of_isRegular_of_length_eq_ringKrullDim
    [IsNoetherianRing S] {xs : List S} (hreg : IsRegular S xs)
    (hlen : xs.length = ringKrullDim S) :
    Module.CohenMacaulay S S := by
  have hSdim : Module.supportDim S S = xs.length := by
    rw [Module.supportDim_self_eq_ringKrullDim, ← hlen]
  -- Extend the sequence up to module depth and show that no tail can remain.
  obtain ⟨xs', hreg', hdepth⟩ := IsRegular.exists_append_eq_moduleDepth hreg
  letI : Nontrivial S := hreg.nontrivial
  have hIneTop : Ideal.ofList (xs ++ xs') • (⊤ : Submodule S S) ≠ ⊤ := by
    simpa [ne_comm] using hreg'.top_ne_smul
  letI : Nontrivial (S ⧸ (Ideal.ofList (xs ++ xs') • (⊤ : Submodule S S))) :=
    Submodule.Quotient.nontrivial_iff.2 hIneTop
  have hquot_nonbot :
      Module.supportDim S (S ⧸ (Ideal.ofList (xs ++ xs') • (⊤ : Submodule S S))) ≠ ⊥ :=
    Module.supportDim_ne_bot_of_nontrivial S _
  have hlen_le :
      (((xs ++ xs').length : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim S S := by
    rw [← Module.supportDim_add_length_eq_supportDim_of_isRegular (M := S) (rs := xs ++ xs') hreg']
    simpa [add_comm] using WithBot.le_add_self hquot_nonbot
      ((((xs ++ xs').length : ℕ∞) : WithBot ℕ∞))
  have htail_len : xs'.length = 0 := by
    have hsum_le :
        (((xs.length + xs'.length : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
          (((xs.length : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      simpa [hSdim, List.length_append] using hlen_le
    have hsum_le_nat : xs.length + xs'.length ≤ xs.length := by
      exact_mod_cast hsum_le
    omega
  have htail : xs' = [] := List.length_eq_zero_iff.mp htail_len
  -- The support-dimension identity is then exactly the Cohen--Macaulay equality.
  refine Module.CohenMacaulay.mk ?_
  rw [hdepth, htail]
  simpa using hSdim

/-- Helper for Lemma 10.112.9: a regular sequence in a Noetherian local ring has length at most
the Krull dimension. -/
private theorem length_le_ringKrullDim_of_isRegular [IsNoetherianRing S] {xs : List S}
    (hreg : IsRegular S xs) :
    xs.length ≤ ringKrullDim S := by
  -- Compare the regular sequence with the canonical dimension formula for quotienting by it.
  have hdimSeq := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hreg
  have hIneTop : Ideal.ofList xs ≠ ⊤ := by
    simpa [ne_comm] using hreg.top_ne_smul
  letI : Nontrivial (S ⧸ Ideal.ofList xs) := Ideal.Quotient.nontrivial_iff.2 hIneTop
  rw [← hdimSeq]
  exact le_add_of_nonneg_left ringKrullDim_nonneg_of_nontrivial

-- Proof sketch: choose a regular sequence in `maximalIdeal R` of length `ringKrullDim R` using the
-- Cohen-Macaulay hypothesis on `R`. By Lemma `10.68.5`, its image in `S` is again a regular
-- sequence. In the finite flat case, Lemma `10.112.4` gives `ringKrullDim S = ringKrullDim R`,
-- so this regular sequence has maximal possible length in `S`, which yields the Cohen-Macaulay
-- property for `S`.
/-- Lemma 10.112.9 (1): if `R → S` is a local homomorphism of Noetherian local rings, `R` is
Cohen-Macaulay, and `S` is finite flat over `R`, then `S` is Cohen-Macaulay. -/
theorem cohenMacaulayRing_of_finiteFlat_localHom
    (hCM : Module.CohenMacaulay R R) [Module.Finite R S] [Module.Flat R S] :
    Module.CohenMacaulay S S := by
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  -- Follow the source proof: transport a full-length regular sequence from `R` to `S`.
  obtain ⟨xs, hregR, hlenR⟩ := exists_maximal_regularSequence_self_of_cohenMacaulay hCM
  have hregS : IsRegular S (xs.map (algebraMap R S)) :=
    isRegular_map_self_of_flat_localHom hregR
  have hlenS : (xs.map (algebraMap R S)).length = ringKrullDim S := by
    calc
      (xs.map (algebraMap R S)).length = ringKrullDim R := by
        simpa using hlenR.symm
      _ = ringKrullDim S := ringKrullDim_eq_of_finiteFlat_localHom_aux
  exact cohenMacaulay_self_of_isRegular_of_length_eq_ringKrullDim hregS hlenS

-- Proof sketch: finite `R`-algebras are integral over `R`, and a flat local homomorphism is
-- faithfully flat. Thus Lemma `10.112.4` applies directly to give equality of Krull dimensions,
-- without any extra Cohen-Macaulay input.
omit [IsNoetherianRing R] in
/-- Lemma 10.112.9 (2): a finite flat local homomorphism of local rings preserves Krull
dimension. This is the dimension-equality input used in part `(1)`. -/
theorem ringKrullDim_eq_of_finiteFlat_localHom [Module.Finite R S] [Module.Flat R S] :
    ringKrullDim R = ringKrullDim S := by
  -- Reuse the file-local dimension comparison established above.
  exact ringKrullDim_eq_of_finiteFlat_localHom_aux

variable [IsNoetherianRing S]

-- Proof sketch: let `d = ringKrullDim R` and choose a regular sequence in `maximalIdeal R` of
-- length `d` using the Cohen-Macaulay hypothesis on `R`. Lemma `10.68.5` carries this sequence to
-- a regular sequence in `S`. The assumed bound `ringKrullDim S ≤ ringKrullDim R = d` forces this
-- regular sequence to have maximal possible length in `S`, so `S` is Cohen-Macaulay.
/-- Lemma 10.112.9 (3): if `R → S` is a local homomorphism of Noetherian local rings, `R` is
Cohen-Macaulay, `S` is flat over `R`, and `dim(S) ≤ dim(R)`, then `S` is Cohen-Macaulay. -/
theorem cohenMacaulayRing_of_flat_localHom_of_ringKrullDim_le
    (hCM : Module.CohenMacaulay R R) [Module.Flat R S] (hdim : ringKrullDim S ≤ ringKrullDim R) :
    Module.CohenMacaulay S S := by
  -- Transport a maximal regular sequence from `R` and show it already has maximal length in `S`.
  obtain ⟨xs, hregR, hlenR⟩ := exists_maximal_regularSequence_self_of_cohenMacaulay hCM
  have hregS : IsRegular S (xs.map (algebraMap R S)) :=
    isRegular_map_self_of_flat_localHom hregR
  have hlenS : (xs.map (algebraMap R S)).length = ringKrullDim S := by
    apply le_antisymm
    · exact length_le_ringKrullDim_of_isRegular hregS
    · calc
        ringKrullDim S ≤ ringKrullDim R := hdim
        _ = (xs.map (algebraMap R S)).length := by
          simpa using hlenR
  exact cohenMacaulay_self_of_isRegular_of_length_eq_ringKrullDim hregS hlenS

-- Proof sketch: the same regular-sequence transfer as in part (3) gives a regular sequence in `S`
-- of length `ringKrullDim R`, hence `ringKrullDim R ≤ ringKrullDim S` because the length of a
-- regular sequence is bounded above by the Krull dimension. Combine this with the assumed
-- inequality `ringKrullDim S ≤ ringKrullDim R`.
/-- Lemma 10.112.9 (4): if `R → S` is a local homomorphism of Noetherian local rings, `R` is
Cohen-Macaulay, `S` is flat over `R`, and `dim(S) ≤ dim(R)`, then `dim(R) = dim(S)`. -/
theorem ringKrullDim_eq_of_flat_localHom_of_ringKrullDim_le_of_cohenMacaulayRing
    (hCM : Module.CohenMacaulay R R) [Module.Flat R S] (hdim : ringKrullDim S ≤ ringKrullDim R) :
    ringKrullDim R = ringKrullDim S := by
  -- The transported regular sequence has length `ringKrullDim R`, so its length bounds
  -- `ringKrullDim R` from above by `ringKrullDim S`.
  obtain ⟨xs, hregR, hlenR⟩ := exists_maximal_regularSequence_self_of_cohenMacaulay hCM
  have hregS : IsRegular S (xs.map (algebraMap R S)) :=
    isRegular_map_self_of_flat_localHom hregR
  have hle : ringKrullDim R ≤ ringKrullDim S := by
    calc
      ringKrullDim R = (xs.map (algebraMap R S)).length := by
        simpa using hlenR
      _ ≤ ringKrullDim S := length_le_ringKrullDim_of_isRegular hregS
  exact le_antisymm hle hdim

end
