import Mathlib.RingTheory.Noetherian.OfPrime
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open TopologicalSpace

variable {R : Type u} [CommRing R]

namespace Ideal

/-- An ideal has finitely generated radical if its radical is the radical of a finitely generated
ideal. -/
def HasFinitelyGeneratedRadical (I : Ideal R) : Prop :=
  ∃ J : Ideal R, J.FG ∧ I.radical = J.radical

/-- For a prime ideal, having finitely generated radical means being the radical of a finitely
generated ideal. -/
theorem hasFinitelyGeneratedRadical_iff_eq_radical {P : Ideal R} (hP : P.IsPrime) :
    P.HasFinitelyGeneratedRadical ↔ ∃ J : Ideal R, J.FG ∧ P = J.radical := by
  simp [HasFinitelyGeneratedRadical, hP.radical]

/-- Helper for Example 10.28.14: the textbook identity
`√I = √((I + (a)) * (I : a))` in mathlib's ideal notation. -/
theorem radical_mul_sup_span_singleton_colon (I : Ideal R) (a : R) :
    (((I ⊔ Ideal.span ({a} : Set R)) * I.colon (Ideal.span ({a} : Set R))).radical) = I.radical := by
  apply le_antisymm
  · -- The product already lies in `I`, so its radical does as well.
    refine Ideal.radical_mono ?_
    rw [Ideal.sup_mul]
    refine sup_le ?_ ?_
    · exact Ideal.mul_le_right
    · rw [Ideal.span_singleton_mul_le_iff]
      intro z hz
      simpa [mul_comm] using Ideal.mem_colon_span_singleton.mp hz
  · -- Every element of `I` contributes a square to the product, giving the reverse radical
    -- inclusion.
    refine (Ideal.radical_le_radical_iff).2 ?_
    intro x hx
    have hx_sup : x ∈ I ⊔ Ideal.span ({a} : Set R) := Ideal.mem_sup_left hx
    have hxa : x * a ∈ I := by
      simpa [mul_comm] using I.mul_mem_left a hx
    have hx_colon : x ∈ I.colon (Ideal.span ({a} : Set R)) :=
      Ideal.mem_colon_span_singleton.mpr hxa
    refine ⟨2, ?_⟩
    simpa [pow_two] using Ideal.mul_mem_mul hx_sup hx_colon

/-- Helper for Example 10.28.14: if a chain of ideals has supremum with finitely generated
radical, then some member of the chain already has finitely generated radical. -/
theorem exists_mem_chain_hasFinitelyGeneratedRadical_of_sSup
    {C : Set (Ideal R)} (hC : IsChain (· ≤ ·) C) {I0 : Ideal R} (hI0 : I0 ∈ C)
    (hsSup : (sSup C).HasFinitelyGeneratedRadical) :
    ∃ J ∈ C, J.HasFinitelyGeneratedRadical := by
  classical
  rcases hsSup with ⟨K, hKfg, hKrad⟩
  -- Move from the finitely generated witness `K` to a positive power contained in the chain
  -- supremum.
  have hKle : K ≤ (sSup C).radical := by
    rw [hKrad]
    exact Ideal.le_radical
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hKle hKfg
  have hpow_le_sSup : K ^ (n + 1) ≤ sSup C := by
    exact (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn
  have hpow_fg : (K ^ (n + 1)).FG := hKfg.pow
  obtain ⟨G, hG⟩ := hpow_fg
  obtain ⟨J, hJ, hGJ⟩ :
      ∃ J ∈ C, (G : Set R) ⊆ (J : Set R) := by
    refine hC.directedOn.exists_mem_subset_of_finset_subset_biUnion ⟨I0, hI0⟩ ?_
    intro x hx
    have hxpow : x ∈ K ^ (n + 1) := by
      rw [← hG]
      exact Ideal.subset_span hx
    have hxsSup : x ∈ sSup C := hpow_le_sSup hxpow
    simpa only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] using
      (Submodule.mem_sSup_of_directed ⟨I0, hI0⟩ hC.directedOn).1 hxsSup
  have hpow_le_J : K ^ (n + 1) ≤ J := by
    rw [← hG]
    exact Ideal.span_le.2 hGJ
  refine ⟨J, hJ, K ^ (n + 1), hKfg.pow, ?_⟩
  apply le_antisymm
  · -- A chain member sits below the supremum, so its radical sits below the witness radical.
    calc
      J.radical ≤ (sSup C).radical := Ideal.radical_mono (le_sSup hJ)
      _ = K.radical := hKrad
      _ = (K ^ (n + 1)).radical := by
        symm
        exact Ideal.radical_pow (I := K) (Nat.succ_ne_zero n)
  · -- The chosen power is contained in `J`, so its radical lies in `J.radical`.
    exact Ideal.radical_mono hpow_le_J

/-- The ideals whose radicals are radicals of finitely generated ideals form an Oka family. -/
-- Proof sketch: the unit ideal is trivially in the family. For the Oka step, combine finite
-- generation data for `I ⊔ Ideal.span {a}` and `I.colon (Ideal.span {a})` with the identity
-- `I.radical = ((I ⊔ Ideal.span ({a} : Set R)) * I.colon (Ideal.span ({a} : Set R))).radical`.
theorem isOka_hasFinitelyGeneratedRadical :
    IsOka (fun I : Ideal R ↦ I.HasFinitelyGeneratedRadical) where
  top := by
    -- The unit ideal is already finitely generated, so it is its own radical witness.
    refine ⟨⊤, fg_top R, ?_⟩
    simp
  oka {I} {a} hsup hcolon := by
    rcases hsup with ⟨J, hJfg, hJrad⟩
    rcases hcolon with ⟨K, hKfg, hKrad⟩
    -- Multiply the finitely generated witnesses and rewrite with the textbook radical identity.
    refine ⟨J * K, hJfg.mul hKfg, ?_⟩
    calc
      I.radical = (((I ⊔ Ideal.span ({a} : Set R)) * I.colon (Ideal.span ({a} : Set R))).radical) := by
        symm
        exact radical_mul_sup_span_singleton_colon I a
      _ = (I ⊔ Ideal.span ({a} : Set R)).radical ⊓
            (I.colon (Ideal.span ({a} : Set R))).radical := by
        rw [Ideal.radical_mul]
      _ = J.radical ⊓ K.radical := by
        rw [hJrad, hKrad]
      _ = (J * K).radical := by
        rw [Ideal.radical_mul]

end Ideal

/-- Helper for Example 10.28.14: in a Noetherian spectrum, every ideal has finitely generated
radical. -/
theorem hasFinitelyGeneratedRadical_of_noetherianSpace
    (hX : NoetherianSpace (PrimeSpectrum R)) (I : Ideal R) :
    I.HasFinitelyGeneratedRadical := by
  -- The complement of `V(I)` is compact open, hence it comes from a finitely generated ideal.
  have hcompact : IsCompact ((PrimeSpectrum.zeroLocus (I : Set R))ᶜ) :=
    (TopologicalSpace.noetherianSpace_iff_isCompact (α := PrimeSpectrum R)).mp hX
      ((PrimeSpectrum.zeroLocus (I : Set R))ᶜ)
  obtain ⟨J, hJfg, hJopen⟩ :=
    (PrimeSpectrum.isCompact_isOpen_iff_ideal :
      IsCompact ((PrimeSpectrum.zeroLocus (I : Set R))ᶜ) ∧
        IsOpen ((PrimeSpectrum.zeroLocus (I : Set R))ᶜ) ↔
          ∃ J : Ideal R, J.FG ∧
            (PrimeSpectrum.zeroLocus (J : Set R))ᶜ =
              (PrimeSpectrum.zeroLocus (I : Set R))ᶜ).mp
      ⟨hcompact, (PrimeSpectrum.isClosed_zeroLocus (I : Set R)).isOpen_compl⟩
  refine ⟨J, hJfg, ?_⟩
  -- Equal complements of zero loci give equal radicals.
  have hzero : PrimeSpectrum.zeroLocus (J : Set R) = PrimeSpectrum.zeroLocus (I : Set R) := by
    simpa using congrArg (fun s : Set (PrimeSpectrum R) ↦ sᶜ) hJopen
  exact (PrimeSpectrum.zeroLocus_eq_iff.mp hzero).symm

/-- Helper for Example 10.28.14: if every ideal has finitely generated radical, then `Spec(R)` is
Noetherian. -/
theorem noetherianSpace_of_forall_hasFinitelyGeneratedRadical
    (hI : ∀ I : Ideal R, I.HasFinitelyGeneratedRadical) :
    NoetherianSpace (PrimeSpectrum R) := by
  refine (TopologicalSpace.noetherianSpace_iff_opens (α := PrimeSpectrum R)).2 ?_
  intro U
  -- Rewrite the closed complement of `U` as a zero locus and replace it by a finitely generated
  -- radical witness.
  obtain ⟨I, hIeq⟩ :=
    (PrimeSpectrum.isClosed_iff_zeroLocus_ideal ((U : Set (PrimeSpectrum R))ᶜ)).mp U.isOpen.isClosed_compl
  rcases hI I with ⟨J, hJfg, hJrad⟩
  have hzero : PrimeSpectrum.zeroLocus (J : Set R) = PrimeSpectrum.zeroLocus (I : Set R) := by
    exact PrimeSpectrum.zeroLocus_eq_iff.mpr hJrad.symm
  have hU0 : (PrimeSpectrum.zeroLocus (I : Set R))ᶜ = (U : Set (PrimeSpectrum R)) := by
    simpa using (congrArg (fun s : Set (PrimeSpectrum R) ↦ sᶜ) hIeq).symm
  have hU : (PrimeSpectrum.zeroLocus (J : Set R))ᶜ = (U : Set (PrimeSpectrum R)) := by
    rw [hzero]
    exact hU0
  exact
    (PrimeSpectrum.isCompact_isOpen_iff_ideal :
      IsCompact (U : Set (PrimeSpectrum R)) ∧ IsOpen (U : Set (PrimeSpectrum R)) ↔
        ∃ I : Ideal R, I.FG ∧
          (PrimeSpectrum.zeroLocus (I : Set R))ᶜ = (U : Set (PrimeSpectrum R))).mpr
      ⟨J, hJfg, hU⟩ |>.1

/-- Example 10.28.14: the prime spectrum `Spec(R)` is Noetherian if and only if every prime ideal
of `R` is the radical of a finitely generated ideal. -/
-- Proof sketch: apply the Oka-family maximal-ideal argument to the predicate
-- `Ideal.HasFinitelyGeneratedRadical`. For a prime ideal, this predicate is exactly the statement
-- that the prime is the radical of a finitely generated ideal.
@[stacks 0G2Z]
theorem primeSpectrum_noetherianSpace_iff_every_prime_hasFinitelyGeneratedRadical :
    NoetherianSpace (PrimeSpectrum R) ↔
      ∀ P : Ideal R, P.IsPrime → ∃ J : Ideal R, J.FG ∧ P = J.radical := by
  constructor
  · intro hX P hP
    -- The topological hypothesis gives finite generation up to radical for every ideal, hence in
    -- particular for primes.
    exact (Ideal.hasFinitelyGeneratedRadical_iff_eq_radical hP).mp
      (hasFinitelyGeneratedRadical_of_noetherianSpace hX P)
  · intro hprime
    -- Route correction: the reverse implication only needs the Oka-family argument on radicals,
    -- not the stronger noetherian-ring criterion from `IsNoetherianRing.of_prime`.
    have hall : ∀ I : Ideal R, I.HasFinitelyGeneratedRadical :=
      Ideal.isOka_hasFinitelyGeneratedRadical.forall_of_forall_prime'
        (fun C _ hC I hI hSup ↦
          Ideal.exists_mem_chain_hasFinitelyGeneratedRadical_of_sSup hC hI hSup)
        (fun P hP ↦ (Ideal.hasFinitelyGeneratedRadical_iff_eq_radical hP).mpr (hprime P hP))
    exact noetherianSpace_of_forall_hasFinitelyGeneratedRadical hall

/-- Bridge reformulation of Example 10.28.14: `Spec(R)` is Noetherian if and only if every ideal of
`R` has radical equal to the radical of a finitely generated ideal. Since this predicate depends
only on the radical, it is equivalent to the radical-ideal wording in the source text. -/
-- Proof sketch: combine the prime-ideal criterion with the Oka-family theorem
-- `Ideal.isOka_hasFinitelyGeneratedRadical`, and use
-- `Ideal.hasFinitelyGeneratedRadical_iff_eq_radical` on prime ideals.
theorem primeSpectrum_noetherianSpace_iff_every_ideal_hasFinitelyGeneratedRadical :
    NoetherianSpace (PrimeSpectrum R) ↔ ∀ I : Ideal R, I.HasFinitelyGeneratedRadical := by
  constructor
  · intro hX I
    -- This is the closed-set/compact-open bridge from the source argument.
    exact hasFinitelyGeneratedRadical_of_noetherianSpace hX I
  · intro hI
    -- If every closed subset is represented by a finitely generated radical, every open is
    -- compact, so the spectrum is Noetherian.
    exact noetherianSpace_of_forall_hasFinitelyGeneratedRadical hI

end
