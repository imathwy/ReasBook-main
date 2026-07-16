import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_162_10
import stacks_proof.stacks_project.Chap10.Lemma_10_162_13
import stacks_proof.stacks_project.Chap10.Proposition_10_162_16
import stacks_proof.stacks_project.Chap10.Remark_10_119_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

/-
Domain triage:
- primary domain: Noetherian local rings, maximal-ideal completions, and analytic unramifiedness;
- sampled owner declarations: `IsAnalyticallyUnramified`,
  `isReduced_of_isAnalyticallyUnramified`,
  and `isAnalyticallyUnramified_of_isReduced_of_minimalPrimes`;
- core/canonical owner: `IsAnalyticallyUnramified` for the completion-reducedness owner and its
  reducedness consequences;
- source-facing bridge: reducedness of `AdicCompletion (maximalIdeal A) A` is the completion view
  of `IsAnalyticallyUnramified A`, while the Chapter 15 statements themselves remain phrased in the
  source completion language.

Primitive vs derived:
- the owner-level datum for completion-reducedness is `IsAnalyticallyUnramified`;
- reducedness of `A` and of minimal-prime quotients are derived owner API, so this file should
  reuse those chapter owners instead of rebuilding a parallel completion-descent argument.
-/

section

variable {A : Type u} [CommRing A] [IsLocalRing A]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

section

variable [IsNoetherianRing A]

-- Proof sketch: reducedness of the maximal-ideal completion is exactly the owner hypothesis
-- `IsAnalyticallyUnramified A`, so the result is the Chapter `10.162.10 (1)` theorem reused in the
-- source completion language.
/-- Lemma 15.43.6 (1): if the maximal-ideal adic completion of a Noetherian local ring `A` is
reduced, then `A` is reduced. -/
@[stacks 07NZ]
theorem isReduced_of_maximalIdealAdicCompletion_isReduced
    [IsReduced ACompletion] : IsReduced A := by
  letI : IsAnalyticallyUnramified A := (isAnalyticallyUnramified_iff A).2 inferInstance
  exact isReduced_of_isAnalyticallyUnramified A

end

-- Proof sketch: Example `10.119.5` constructs a one-dimensional Noetherian local domain whose
-- maximal-ideal adic completion is not reduced. Taking that explicit example yields a reduced
-- Noetherian local ring for which the converse of part `(1)` fails.
/-- Lemma 15.43.6 (2): in general, there exists a reduced Noetherian local ring whose
maximal-ideal adic completion is not reduced. -/
@[stacks 07NZ]
theorem exists_reduced_noetherian_local_ring_with_nonreduced_completion :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A) (_ : IsLocalRing A),
      IsReduced A ∧ ¬ IsReduced (AdicCompletion (maximalIdeal A) A) := by
  obtain ⟨A, _, _, _, _, _, _, hA, _⟩ :=
    exists_charZero_nonstabilizing_finite_semilocal_domain_overring_sequence
  refine ⟨A, inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨inferInstance, ?_⟩
  simpa [isAnalyticallyUnramified_iff A] using hA

section

variable [NagataRing A]

local instance (p : minimalPrimes A) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

local instance (p : minimalPrimes A) : IsLocalRing (A ⧸ p.1) :=
  primeSpectrum_quotient_isLocalRing ⟨p.1, inferInstance⟩

local instance (p : minimalPrimes A) : NagataRing (A ⧸ p.1) :=
  nagataRing_of_finiteType A

/-- Lemma 15.43.6 (3): for a Nagata local ring `A`, reducedness is equivalent to reducedness of
its maximal-ideal adic completion. -/
@[stacks 07NZ]
theorem nagataRing_isReduced_iff_maximalIdealAdicCompletion_isReduced :
    IsReduced A ↔ IsReduced ACompletion := by
  constructor
  · intro hA
    letI : IsReduced A := hA
    letI : IsAnalyticallyUnramified A :=
      isAnalyticallyUnramified_of_isReduced_of_minimalPrimes A (fun _ ↦ inferInstance)
    exact inferInstance
  · intro hCompletion
    letI : IsReduced ACompletion := hCompletion
    exact isReduced_of_maximalIdealAdicCompletion_isReduced

end

end
