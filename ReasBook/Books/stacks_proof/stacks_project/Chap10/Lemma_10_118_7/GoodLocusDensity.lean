import StacksProject_2024.Chap10.Lemma_10_118_3
import StacksProject_2024.Chap10.Lemma_10_118_4
import StacksProject_2024.Chap10.Lemma_10_118_5
import StacksProject_2024.Chap10.Lemma_10_118_6
import StacksProject_2024.Chap10.Lemma_10_30_2
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/- Domain triage:
* primary domain: the generic-flatness good locus on `Spec(R)`;
* source-facing owner: `goodLocus R S M` from `10_118_3_2`;
* core/canonical topological owners: `IsOpen` and `Dense` for subsets of `Spec(R)`;
* bridge/view target of this file: openness comes directly from the owner description
  `goodLocus_eq_iUnion`, while density under `[IsReduced R]` is the source-facing consequence
  obtained by combining the domain case `Lemma_10_118_3` with the dense-standard-open bridge
  `dense_goodLocus_of_dense_standardOpen_cover` from `Lemma_10_118_6`. -/

/-- The generic-flatness good locus `U(R → S, M)` is open in `Spec(R)`. -/
-- Proof sketch: `goodLocus R S M` is defined as a union of basic opens `D(f)`, and each basic
-- open is open in `Spec(R)`.
theorem isOpen_goodLocus :
    IsOpen (goodLocus R S M) := by
  -- Reuse the canonical owner statement proved in the dense-cover file.
  simpa using GenericFlatness.isOpen_goodLocus_aux (R := R) (S := S) (M := M)

/-- Helper for Lemma 10.118.7: over a domain, the generic-flatness good locus contains a dense
basic open coming from the nonzero witness of Lemma `10.118.3`. -/
theorem dense_goodLocus_of_isDomain
    [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] :
    Dense (goodLocus R S M) := by
  obtain ⟨f, hf, hcond⟩ :
      ∃ f : R, f ≠ 0 ∧ LocalizationCondition R S M f :=
    exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType
  have hsubset : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ goodLocus R S M := by
    -- The witness `f` contributes its basic open directly to the defining union of the good locus.
    intro p hp
    rw [goodLocus_eq_iUnion]
    exact Set.mem_iUnion.mpr ⟨⟨f, hcond⟩, hp⟩
  -- A nonzero basic open is dense over a domain, so the larger good locus is dense as well.
  exact Dense.mono hsubset (basicOpen_dense_of_nonzero_of_isDomain f hf)

/-- Helper for Lemma 10.118.7: density of the good locus propagates across a short exact sequence
from the two endpoint modules to the middle module. -/
theorem dense_goodLocus_middle_of_shortExact
    {T : CategoryTheory.ShortComplex (ModuleCat.{max u v} S)} (hT : T.ShortExact)
    (h₁ : Dense (goodLocus R S T.X₁)) (h₃ : Dense (goodLocus R S T.X₃)) :
    Dense (goodLocus R S T.X₂) := by
  have hinter :
      Dense (goodLocus R S T.X₁ ∩ goodLocus R S T.X₃) := by
    -- The endpoint good loci are open, so their intersection is dense.
    exact h₁.inter_of_isOpen_right h₃ (isOpen_goodLocus (R := R) (S := S) (M := T.X₃))
  -- Lemma `10.118.4` identifies this dense intersection as a subset of the middle good locus.
  exact Dense.mono
    (CategoryTheory.ShortComplex.ShortExact.goodLocus_inter_subset_of_shortExact
      (R := R) (S := S) (T := T) hT)
    hinter

/-- Helper for Lemma 10.118.7: an `S`-linear equivalence transports the localized
generic-flatness condition at a fixed element of `R`. -/
theorem localizationCondition_of_linearEquiv
    {N : Type*} [AddCommGroup N] [Module S N]
    (f : R) (e : M ≃ₗ[S] N) [h : LocalizationCondition R S M f] :
    LocalizationCondition R S N f := by
  -- Localize the linear equivalence and transport the finite-presentation and freeness fields.
  let e' : LocalizedModule.Away (algebraMap R S f) M ≃ₗ[Localization.Away (algebraMap R S f)]
      LocalizedModule.Away (algebraMap R S f) N := by
    refine LinearEquiv.ofBijective
      (LocalizedModule.map (.powers (algebraMap R S f)) e.toLinearMap) ?_
    constructor
    · simpa using
        LocalizedModule.map_injective (.powers (algebraMap R S f)) e.toLinearMap e.injective
    · simpa using
        LocalizedModule.map_surjective (.powers (algebraMap R S f)) e.toLinearMap e.surjective
  let e'' : LocalizedModule.Away (algebraMap R S f) M ≃ₗ[Localization.Away f]
      LocalizedModule.Away (algebraMap R S f) N :=
    { toFun := e'
      invFun := e'.symm
      left_inv := e'.left_inv
      right_inv := e'.right_inv
      map_add' := e'.map_add
      map_smul' := fun r x ↦ by
        -- Rewrite the base-scalar action through the canonical map into the localized target ring,
        -- then apply linearity of the localized equivalence.
        change e' ((algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)) r) • x) =
          (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)) r) • e' x
        simpa using
          e'.map_smulₛₗ (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)) r) x }
  letI : Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) N) := Module.FinitePresentation.of_equiv e'
  letI : Module.Free (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) N) :=
    Module.Free.of_equiv' h.free_module e''
  exact
    { finitePresentation_algebra := h.finitePresentation_algebra
      finitePresentation_module := inferInstance
      free_algebra := h.free_algebra
      free_module := inferInstance }

/-- Helper for Lemma 10.118.7: the good locus is unchanged by `S`-linear equivalence of the
module argument. -/
theorem goodLocus_eq_of_linearEquiv
    {N : Type*} [AddCommGroup N] [Module S N] (e : M ≃ₗ[S] N) :
    goodLocus R S M = goodLocus R S N := by
  ext p
  -- Rewrite membership as the existence of one localization witness and transport that witness
  -- across the localized linear equivalence.
  rw [mem_goodLocus_iff, mem_goodLocus_iff]
  constructor
  · rintro ⟨f, hf, hfp⟩
    exact
      ⟨f,
        localizationCondition_of_linearEquiv (R := R) (S := S) (M := M) (N := N) f e,
        hfp⟩
  · rintro ⟨f, hf, hfp⟩
    exact
      ⟨f,
        localizationCondition_of_linearEquiv (R := R) (S := S) (M := N) (N := M) f e.symm,
        hfp⟩

end GenericFlatness

end
