import Mathlib
import stacks_project.Chap10.Definition_10_104_1
import stacks_project.Chap10.Lemma_10_68_5
import stacks_project.Chap10.Lemma_10_104_2
import stacks_project.Chap10.Lemma_10_112_4

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

-- Proof sketch: choose a regular sequence in `maximalIdeal R` of length `ringKrullDim R` using the
-- Cohen-Macaulay hypothesis on `R`. By Lemma `10.68.5`, its image in `S` is again a regular
-- sequence. In the finite flat case, Lemma `10.112.4` gives `ringKrullDim S = ringKrullDim R`,
-- so this regular sequence has maximal possible length in `S`, which yields the Cohen-Macaulay
-- property for `S`.
/-- Lemma 10.112.9 (1): if `R → S` is a local homomorphism of Noetherian local rings, `R` is
Cohen-Macaulay, and `S` is finite flat over `R`, then `S` is Cohen-Macaulay. -/
theorem cohenMacaulayRing_of_finiteFlat_localHom
    (hCM : Module.CohenMacaulay R R) [Module.Finite R S] [Module.Flat R S] :
    Module.CohenMacaulay S S := sorry

-- Proof sketch: finite `R`-algebras are integral over `R`, and a flat local homomorphism is
-- faithfully flat. Thus Lemma `10.112.4` applies directly to give equality of Krull dimensions,
-- without any extra Cohen-Macaulay input.
omit [IsNoetherianRing R] in
/-- Lemma 10.112.9 (2): a finite flat local homomorphism of local rings preserves Krull
dimension. This is the dimension-equality input used in part `(1)`. -/
theorem ringKrullDim_eq_of_finiteFlat_localHom [Module.Finite R S] [Module.Flat R S] :
    ringKrullDim R = ringKrullDim S := by
  letI : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hff : (algebraMap R S).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  exact ringKrullDim_eq_of_injective_algebraMap_of_isIntegral hff.injective

variable [IsNoetherianRing S]

-- Proof sketch: let `d = ringKrullDim R` and choose a regular sequence in `maximalIdeal R` of
-- length `d` using the Cohen-Macaulay hypothesis on `R`. Lemma `10.68.5` carries this sequence to
-- a regular sequence in `S`. The assumed bound `ringKrullDim S ≤ ringKrullDim R = d` forces this
-- regular sequence to have maximal possible length in `S`, so `S` is Cohen-Macaulay.
/-- Lemma 10.112.9 (3): if `R → S` is a local homomorphism of Noetherian local rings, `R` is
Cohen-Macaulay, `S` is flat over `R`, and `dim(S) ≤ dim(R)`, then `S` is Cohen-Macaulay. -/
theorem cohenMacaulayRing_of_flat_localHom_of_ringKrullDim_le
    (hCM : Module.CohenMacaulay R R) [Module.Flat R S] (hdim : ringKrullDim S ≤ ringKrullDim R) :
    Module.CohenMacaulay S S := sorry

-- Proof sketch: the same regular-sequence transfer as in part (3) gives a regular sequence in `S`
-- of length `ringKrullDim R`, hence `ringKrullDim R ≤ ringKrullDim S` because the length of a
-- regular sequence is bounded above by the Krull dimension. Combine this with the assumed
-- inequality `ringKrullDim S ≤ ringKrullDim R`.
/-- Lemma 10.112.9 (4): if `R → S` is a local homomorphism of Noetherian local rings, `R` is
Cohen-Macaulay, `S` is flat over `R`, and `dim(S) ≤ dim(R)`, then `dim(R) = dim(S)`. -/
theorem ringKrullDim_eq_of_flat_localHom_of_ringKrullDim_le_of_cohenMacaulayRing
    (hCM : Module.CohenMacaulay R R) [Module.Flat R S] (hdim : ringKrullDim S ≤ ringKrullDim R) :
    ringKrullDim R = ringKrullDim S := by
  letI : Module.CohenMacaulay R R := hCM
  have hnil : Ideal.ofList ([] : List R) = (⊥ : Ideal R) := Ideal.ofList_nil
  have hxs : ∀ x ∈ ([] : List R), x ∈ maximalIdeal R := by
    simp
  have hexists :=
    exists_maximal_regularSequence_extension_of_ringKrullDim_quotient_add_length_eq hxs
      (by
        rw [hnil]
        simpa using
          ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R : R ⧸ (⊥ : Ideal R) ≃+* R))
  rcases hexists with ⟨xs, hregR, _, hlen⟩
  have hregTensor : IsRegular (S ⊗[R] R) (xs.map (algebraMap R S)) :=
    isRegular_iff_isRegular_tensorBaseChange_of_flat_localHom.mp hregR
  have hregS : IsRegular S (xs.map (algebraMap R S)) := by
    simpa using ((Algebra.TensorProduct.rid R S S).toLinearEquiv.isRegular_congr _).mp hregTensor
  have hle : ringKrullDim R ≤ ringKrullDim S := by
    rw [hlen]
    have hdimSeq := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hregS
    have hlenS : (xs.map (algebraMap R S)).length ≤ ringKrullDim S := by
      rw [← hdimSeq]
      have hIneTop : Ideal.ofList (xs.map (algebraMap R S)) ≠ ⊤ := by
        simpa [ne_comm] using hregS.top_ne_smul
      letI : Nontrivial (S ⧸ Ideal.ofList (xs.map (algebraMap R S))) :=
        Ideal.Quotient.nontrivial_iff.2 hIneTop
      exact le_add_of_nonneg_left ringKrullDim_nonneg_of_nontrivial
    simpa using hlenS
  exact le_antisymm hle hdim

end
