import StacksProject_2024.stacks_project.Chap10.Lemma_10_102_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_72_9

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

open IsLocalRing Module.associatedPrimes

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
variable {e : ℕ}

/- Domain triage:
* primary domain: bounded finite free complexes over a local ring, together with the chapter depth
  owner `moduleDepth` and the associated-prime bridge detecting depth `0`;
* sampled owner declarations of the same kind:
  `FiniteFreeComplex`,
  `IsDirectSumOfTrivialComplexes`,
  `finiteFreeComplex_isDirectSumOfTrivialComplexes_of_exact_of_depthZero`,
  `moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes`;
* best owner abstraction: the chapter owner theorem
  `finiteFreeComplex_isDirectSumOfTrivialComplexes_of_exact_of_depthZero`, with the Artinian-local
  hypothesis used only to derive the canonical bridge statement `moduleDepth R R = 0`;
* layer: `source-facing` specialization of that owner theorem, not a second decomposition owner.
-/

-- Proof sketch: apply
-- `finiteFreeComplex_isDirectSumOfTrivialComplexes_of_exact_of_depthZero`. An Artinian local ring
-- has depth `0`; equivalently, its maximal ideal is an associated prime of `R`, which is the
-- bridge criterion used in the proof of Lemma `10.102.3`.
/-- Lemma 10.102.4: in Situation 10.102.1, if `R` is an Artinian local ring and the bounded finite
free complex `0 → R^{n_e} → R^{n_{e-1}} → ⋯ → R^{n_0}` is exact in degrees `e, …, 1`, then the
complex is isomorphic to a direct sum of trivial complexes. -/
theorem finiteFreeComplex_isDirectSumOfTrivialComplexes_of_exact_of_artinianLocal
    (C : FiniteFreeComplex R e)
    (hexact : ∀ j : ℕ, 1 ≤ j → j ≤ e → C.toChainComplex.ExactAt j) :
    IsDirectSumOfTrivialComplexes C.toChainComplex := by
  refine finiteFreeComplex_isDirectSumOfTrivialComplexes_of_exact_of_depthZero C hexact ?_
  haveI : Ring.KrullDimLE 0 R := (isArtinianRing_iff_krullDimLE_zero).mp inferInstance
  have hann : Module.annihilator R R = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hassoc : maximalIdeal R ∈ associatedPrimes R R := by
    have hmin' : maximalIdeal R ∈ (⊥ : Ideal R).minimalPrimes := by
      rw [Ring.KrullDimLE.mem_minimalPrimes_iff_le_of_isPrime]
      exact bot_le
    have hmin : maximalIdeal R ∈ (Module.annihilator R R).minimalPrimes := by
      simpa [hann] using hmin'
    exact minimalPrimes_annihilator_subset_associatedPrimes R R hmin
  have hle : WithBot.some (moduleDepth R R : ℕ∞) ≤ ringKrullDim (R ⧸ maximalIdeal R) :=
    moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (maximalIdeal R) hassoc
  have hdim : ringKrullDim (R ⧸ maximalIdeal R) = 0 := by
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
    exact ringKrullDim_eq_zero_of_field (R ⧸ maximalIdeal R)
  rw [hdim] at hle
  have hdepth_le : moduleDepth R R ≤ 0 := by
    simpa [WithBot.some_eq_coe] using hle
  exact le_antisymm hdepth_le bot_le

end
