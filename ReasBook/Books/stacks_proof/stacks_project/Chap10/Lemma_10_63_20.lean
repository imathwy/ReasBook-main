import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_61_3
import stacks_proof.stacks_project.Chap10.Lemma_10_63_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable [Algebra.FiniteType k S]

include k

/-- Lemma 10.63.20: if `S` is a finite type `k`-algebra of positive Krull dimension, then `S`
contains an element that is a nonzerodivisor and not a unit.

Canonical Lean form: for an element of a ring, "is a nonzerodivisor" is expressed by membership
in the canonical submonoid `nonZeroDivisors S`, rather than by the module-specialized predicate
`IsSMulRegular S`. -/
-- Proof sketch: `S` is Noetherian, so `associatedPrimes S S` is finite by Lemma `10.63.5`.
-- Positive Krull dimension rules out the zero-dimensional case from Lemma `10.61.3`, so `S` has
-- infinitely many maximal ideals and one can choose a maximal ideal not among the associated
-- primes. Lemma `10.63.18` then yields an element of that maximal ideal that is regular on `S`,
-- hence a nonzerodivisor. Membership in a proper maximal ideal shows it is not a unit.
@[stacks 0GEC]
theorem exists_nonzerodivisor_nonunit_of_finiteType_over_field_of_pos_ringKrullDim
    (hdim : 0 < ringKrullDim S) :
    ∃ f : S, f ∈ nonZeroDivisors S ∧ ¬ IsUnit f := by
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  haveI : Nontrivial S := by
    by_contra hS
    haveI : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS
    simp [ringKrullDim_eq_bot_of_subsingleton] at hdim
  have htfae :
      List.TFAE
        [ Ring.KrullDimLE 0 S
        , Finite (PrimeSpectrum S)
        , Finite (MaximalSpectrum S)
        , T2Space (PrimeSpectrum S)
        , FiniteDimensional k S
        , IsArtinianRing S
        , DiscreteTopology (PrimeSpectrum S)
        ] :=
    finiteTypeAlgebra_over_field_zeroDimensional_tfae
  have hnot_finite : ¬ Finite (MaximalSpectrum S) := by
    intro hfinite
    have hle0 : Ring.KrullDimLE 0 S := (htfae.out 0 2 rfl rfl).mpr hfinite
    have hzero : ringKrullDim S = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hle0
    exact not_lt_of_ge hzero.le hdim
  haveI : Infinite (MaximalSpectrum S) := by
    by_contra hfinite
    exact hnot_finite (not_infinite_iff_finite.mp hfinite)
  classical
  have hassoc_finite : (associatedPrimes S S).Finite := associatedPrimes.finite S S
  have hmax_assoc_finite :
      { m : MaximalSpectrum S | m.asIdeal ∈ associatedPrimes S S }.Finite := by
    let e : MaximalSpectrum S ↪ Ideal S :=
      ⟨MaximalSpectrum.asIdeal, fun m n h ↦ by
        cases m
        cases n
        cases h
        rfl⟩
    simpa [e] using Set.Finite.preimage_embedding e hassoc_finite
  obtain ⟨m, hm_assoc⟩ : ∃ m : MaximalSpectrum S, m.asIdeal ∉ associatedPrimes S S := by
    simpa using hmax_assoc_finite.infinite_compl.nonempty
  have hm_not_le_assoc : ∀ q ∈ associatedPrimes S S, ¬ m.asIdeal ≤ q := by
    intro q hq_assoc hle
    have hmq : m.asIdeal = q :=
      m.isMaximal.eq_of_le (IsAssociatedPrime.isPrime <| AssociatedPrimes.mem_iff.mp hq_assoc).ne_top
        hle
    exact hm_assoc (hmq ▸ hq_assoc)
  obtain ⟨f, hfm, hf_reg⟩ :
      ∃ f ∈ m.asIdeal, IsSMulRegular S f :=
    (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes m.asIdeal).2 hm_not_le_assoc
  have hf_mem : f ∈ nonZeroDivisors S := by
    simpa [nonZeroDivisorsLeft_eq_nonZeroDivisors] using
      hf_reg.isLeftRegular.mem_nonZeroDivisorsLeft
  refine ⟨f, hf_mem, ?_⟩
  intro hf_unit
  exact m.isMaximal.ne_top <| m.asIdeal.eq_top_of_isUnit_mem hfm hf_unit

end
