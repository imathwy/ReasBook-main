import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_136_1_Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Algebra

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

/- Domain-style sampling:
- primary domain: cotangent modules of explicit quotient presentations, localized away from one
  element, under the syntomic owner predicate on the localized ring map;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `Ideal.Cotangent`,
  `LocalizedModule.Away`,
  `localized_presentation_cotangent_stable_equiv`;
- best owner abstraction: the public owner here is the pair of predicates
  `Module.Finite` / `Module.Projective` on the canonical localized cotangent module
  `LocalizedModule.Away g I.Cotangent`; the relative-global-complete-intersection presentation and
  the stable cotangent comparison are bridge/view input for the proof, not extra public data;
- primitive vs. derived:
  the primitive source-facing data are the quotient ideal `I` and the syntomic hypothesis on the
  localized quotient map `R → S_g`;
  a separate finite-generation hypothesis on `I` is derived proof input at most, not owner data
  for the localized conormal statement, so it should not remain in the public interface.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma for an explicit quotient `S = R[x₁, …, xₙ] / I`;
- `core/canonical`: `RingHom.Syntomic`, `Ideal.Cotangent`, and `LocalizedModule.Away`;
- `bridge/view`: `syntomicAtPrime_tfae`, `relativeGCI_conormalModule_has_basis`, and
  `localized_presentation_cotangent_stable_equiv`.
-/

local notation "Poly" => MvPolynomial (Fin n) R

/-- Helper for Chap10 Lemma 10 136 16: finite projectivity transfers across a linear
equivalence to the source module. -/
private lemma finiteProjective_of_linearEquiv
    {A : Type u} [CommRing A]
    {M N : Type u}
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Projective A N]
    (e : M ≃ₗ[A] N) :
    Module.Finite A M ∧ Module.Projective A M := by
  -- Pull the finite/projective structure back along the given equivalence.
  refine ⟨?_, ?_⟩
  · exact Module.Finite.equiv e.symm
  · exact Module.Projective.of_equiv e.symm

/-- Helper for Chap10 Lemma 10 136 16: the left factor of a product stably equivalent to a finite
projective product is finite projective. -/
private lemma finiteProjective_left_of_prod_linearEquiv
    {A : Type u} [CommRing A]
    {M N P Q : Type u}
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P]
    [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [Module.Projective A Q]
    (e : (M × N) ≃ₗ[A] (P × Q)) :
    Module.Finite A M ∧ Module.Projective A M := by
  -- Transfer finite projectivity across the stable product equivalence.
  have hfinProdMN : Module.Finite A (M × N) := Module.Finite.equiv e.symm
  have hprojProdMN : Module.Projective A (M × N) := Module.Projective.of_equiv e.symm
  -- Projecting onto the first factor makes `M` a finite quotient of the finite product.
  have hfst_surj : Function.Surjective (LinearMap.fst A M N) := by
    intro x
    exact ⟨(x, 0), rfl⟩
  have hfinM : Module.Finite A M :=
    Module.Finite.of_surjective (LinearMap.fst A M N) hfst_surj
  -- The standard inclusion/projection splitting makes `M` a projective direct summand.
  have hsplit : (LinearMap.fst A M N).comp (LinearMap.inl A M N) = LinearMap.id := by
    ext x
    rfl
  have hprojM : Module.Projective A M :=
    Module.Projective.of_split (LinearMap.inl A M N) (LinearMap.fst A M N) hsplit
  exact ⟨hfinM, hprojM⟩

/-- Helper for Chap10 Lemma 10 136 16: the left factor of a product stably equivalent to a
finite product is finite. -/
private lemma finite_of_prod_linearEquiv
    {A : Type u} [CommRing A]
    {M N P Q : Type u}
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] [Module.Finite A P]
    [AddCommGroup Q] [Module A Q] [Module.Finite A Q]
    (e : (M × N) ≃ₗ[A] (P × Q)) :
    Module.Finite A M := by
  -- Transfer finiteness across the stable product equivalence, then project onto the left factor.
  have hfinProdMN : Module.Finite A (M × N) := Module.Finite.equiv e.symm
  have hfst_surj : Function.Surjective (LinearMap.fst A M N) := by
    intro x
    exact ⟨(x, 0), rfl⟩
  exact Module.Finite.of_surjective (LinearMap.fst A M N) hfst_surj

/-- Helper for Chap10 Lemma 10 136 16: prime-wise basic-open witnesses force the chosen elements
to generate the unit ideal. -/
private lemma span_top_of_forall_prime_exists_not_mem
    {A : Type u} [CommRing A] (t : Set A)
    (h : ∀ q : PrimeSpectrum A, ∃ a ∈ t, a ∉ q.asIdeal) :
    Ideal.span t = ⊤ := by
  classical
  -- If the span were proper, a maximal ideal above it would define a prime contradicting `h`.
  by_contra htop
  obtain ⟨m, hmmax, hmle⟩ := Ideal.exists_le_maximal (Ideal.span t) htop
  let q : PrimeSpectrum A := ⟨m, hmmax.isPrime⟩
  obtain ⟨a, hat, ham⟩ := h q
  exact ham (hmle (Ideal.subset_span hat))

/-- Helper for Chap10 Lemma 10 136 16: a syntomic algebra map supplies algebraic finite
presentation for the target algebra. -/
private lemma finitePresentation_of_syntomic_algebraMap
    {A : Type u} [CommRing A] [Algebra R A]
    (hsyntomic : (algebraMap R A).Syntomic) :
    Algebra.FinitePresentation R A := by
  -- Project the finite-presentation field of `Syntomic` and translate from ring maps to algebras.
  exact RingHom.finitePresentation_algebraMap.mp
    (RingHom.Syntomic.finitePresentation hsyntomic)

/-- Helper for Chap10 Lemma 10 136 16: a syntomic algebra map supplies flatness of the target
algebra as a module over the source. -/
private lemma moduleFlat_of_syntomic_algebraMap
    {A : Type u} [CommRing A] [Algebra R A]
    (hsyntomic : (algebraMap R A).Syntomic) :
    Module.Flat R A := by
  -- Project the flatness field of `Syntomic` and translate from ring maps to algebras.
  exact RingHom.flat_algebraMap_iff.mp (RingHom.Syntomic.flat hsyntomic)

/-- Helper for Chap10 Lemma 10 136 16: the trivial principal chart of a syntomic algebra is
finitely presented over the base. -/
private lemma finitePresentation_localizationAway_one_of_syntomic_algebraMap
    {A : Type u} [CommRing A] [Algebra R A]
    (hsyntomic : (algebraMap R A).Syntomic) :
    Algebra.FinitePresentation R (Localization.Away (1 : A)) := by
  -- Compose finite presentation of `R -> A` with the finite presentation of `A -> A[1⁻¹]`.
  have hloc :
      (algebraMap A (Localization.Away (1 : A))).FinitePresentation :=
    (RingHom.finitePresentation_algebraMap).mpr
      (IsLocalization.Away.finitePresentation (S := Localization.Away (1 : A)) (1 : A))
  let f : A →+* Localization.Away (1 : A) := algebraMap A (Localization.Away (1 : A))
  have hcomp : (f.comp (algebraMap R A)).FinitePresentation :=
    RingHom.FinitePresentation.comp hloc (RingHom.Syntomic.finitePresentation hsyntomic)
  have hEq : f.comp (algebraMap R A) = algebraMap R (Localization.Away (1 : A)) := by
    ext r
    rfl
  exact (RingHom.finitePresentation_algebraMap).mp (hEq ▸ hcomp)

/-- Helper for Chap10 Lemma 10 136 16: syntomic flatness localizes to the canonical local map at
any target prime. -/
private lemma localRingHom_flat_of_syntomic_algebraMap
    {A : Type u} [CommRing A] [Algebra R A]
    (hsyntomic : (algebraMap R A).Syntomic) (q : PrimeSpectrum A) :
    (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl).Flat := by
  -- Localize the flat ring map at the contracted source prime and the chosen target prime.
  exact RingHom.Flat.localRingHom (RingHom.Syntomic.flat hsyntomic)
    q.asIdeal (q.asIdeal.under R) rfl

/-- Helper for Chap10 Lemma 10 136 16: a syntomic algebra supplies the finite-presentation,
localized-flatness, and fiber-LCI side conditions on the trivial chart at every target prime. -/
private lemma syntomic_trivialChart_sideConditions
    {A : Type u} [CommRing A] [Algebra R A]
    (hsyntomic : (algebraMap R A).Syntomic) (q : PrimeSpectrum A) :
    ∃ a : A, a ∉ q.asIdeal ∧
      Algebra.FinitePresentation R (Localization.Away a) ∧
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl).Flat ∧
      (algebraMap R A).HasLocalCompleteIntersectionFibers := by
  -- Use the basic open `D(1)`: it contains every prime and keeps the syntomic data visible.
  refine ⟨1, ?_, ?_, ?_, ?_⟩
  · simpa [Ideal.eq_top_iff_one] using q.2.ne_top
  · exact finitePresentation_localizationAway_one_of_syntomic_algebraMap hsyntomic
  · exact localRingHom_flat_of_syntomic_algebraMap hsyntomic q
  · exact RingHom.Syntomic.hasLocalCompleteIntersectionFibers hsyntomic

/-- Helper for Chap10 Lemma 10 136 16: the finite-presentation charts visible from a syntomic
algebra map generate the unit ideal. -/
private lemma finitePresentationCharts_span_top_of_syntomic_algebraMap
    {A : Type u} [CommRing A] [Algebra R A]
    (hsyntomic : (algebraMap R A).Syntomic) :
    Ideal.span {a : A | Algebra.FinitePresentation R (Localization.Away a)} = ⊤ := by
  -- The trivial chart `D(1)` is finitely presented, so this chart set already contains `1`.
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span (finitePresentation_localizationAway_one_of_syntomic_algebraMap hsyntomic)

/-- Helper for Chap10 Lemma 10 136 16: the syntomic finite-presentation chart cover can be
chosen finite, in the explicit unit-chart form needed by localization patching. -/
private lemma finitePresentationCharts_finset_span_top_of_syntomic_algebraMap
    {A : Type u} [CommRing A] [Algebra R A]
    (hsyntomic : (algebraMap R A).Syntomic) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ a ∈ s, Algebra.FinitePresentation R (Localization.Away a) := by
  -- The unit chart is a finite principal cover, and syntomicity gives finite presentation there.
  use ({1} : Finset A)
  constructor
  · rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span (by simp)
  · intro a ha
    rw [Finset.mem_singleton] at ha
    subst a
    exact finitePresentation_localizationAway_one_of_syntomic_algebraMap hsyntomic

/-- Helper for Chap10 Lemma 10 136 16: the trivial principal chart of a syntomic algebra gives a
finite unit cover carrying the finite-presentation, flatness, and fiber-LCI side conditions used
by the relative-GCI spreading step. -/
private lemma syntomicSideConditionCharts_finset_span_top_of_syntomic_algebraMap
    {A : Type u} [CommRing A] [Algebra R A]
    (hsyntomic : (algebraMap R A).Syntomic) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ a ∈ s,
        Algebra.FinitePresentation R (Localization.Away a) ∧
          ∀ q : PrimeSpectrum A,
            a ∉ q.asIdeal ∧
              (Localization.localRingHom (q.asIdeal.under R) q.asIdeal
                (algebraMap R A) rfl).Flat ∧
              (algebraMap R A).HasLocalCompleteIntersectionFibers := by
  -- Use the finite cover by `D(1)` and record all syntomic fields on that chart.
  use ({1} : Finset A)
  constructor
  · rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span (by simp)
  · intro a ha
    rw [Finset.mem_singleton] at ha
    subst a
    constructor
    · exact finitePresentation_localizationAway_one_of_syntomic_algebraMap hsyntomic
    · intro q
      refine ⟨?_, ?_, ?_⟩
      · simpa [Ideal.eq_top_iff_one] using q.2.ne_top
      · exact localRingHom_flat_of_syntomic_algebraMap hsyntomic q
      · exact RingHom.Syntomic.hasLocalCompleteIntersectionFibers hsyntomic

/-- Helper for Chap10 Lemma 10 136 16: the unit principal chart is a finite cover whose single
member gives the primewise finite-presentation, flatness, and fiber-LCI side conditions. -/
private lemma syntomicSideConditionPrimeCover_finset_span_top_of_syntomic_algebraMap
    {A : Type u} [CommRing A] [Algebra R A]
    (hsyntomic : (algebraMap R A).Syntomic) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ q : PrimeSpectrum A, ∃ a ∈ s,
        a ∉ q.asIdeal ∧
          Algebra.FinitePresentation R (Localization.Away a) ∧
          (Localization.localRingHom (q.asIdeal.under R) q.asIdeal
            (algebraMap R A) rfl).Flat ∧
          (algebraMap R A).HasLocalCompleteIntersectionFibers := by
  -- Record the same unit basic open as a primewise witness, which is the cover shape needed
  -- before the missing relative-GCI spreading theorem can be applied.
  use ({1} : Finset A)
  constructor
  · rw [Ideal.eq_top_iff_one]
    have hmem : (1 : A) ∈ (({1} : Finset A) : Set A) := by
      simp
    exact Ideal.subset_span hmem
  · intro q
    have hmem : (1 : A) ∈ ({1} : Finset A) := by
      simp
    refine ⟨1, hmem, ?_, ?_, ?_, ?_⟩
    · simpa [Ideal.eq_top_iff_one] using q.2.ne_top
    · exact finitePresentation_localizationAway_one_of_syntomic_algebraMap hsyntomic
    · exact localRingHom_flat_of_syntomic_algebraMap hsyntomic q
    · exact RingHom.Syntomic.hasLocalCompleteIntersectionFibers hsyntomic

-- Proof sketch: by Lemma `10.136.15`, after refining the basic open `D(g)` we may assume the
-- localization is a relative global complete intersection over `R`. Lemma `10.136.12` then makes
-- the conormal module free for that refined presentation, and Lemma `10.134.16` transports this
-- finite projective structure back to the localization of the original conormal module.
/-- Lemma 10.136.16: let `S = R[x₁, …, xₙ] / I` with `I` finitely generated. If the localization
`S_g` is syntomic over `R`, then the localized conormal module `(I / I²)_g` is a finite
projective `S_g`-module. -/
@[stacks 07BT]
theorem idealCotangent_localizedAway_finiteProjective_of_syntomic
    (I : Ideal Poly) (g : Poly ⧸ I)
    (hsyntomic : (algebraMap R (Localization.Away g)).Syntomic) :
    Module.Finite (Localization.Away g) (LocalizedModule.Away g I.Cotangent) ∧
      Module.Projective (Localization.Away g) (LocalizedModule.Away g I.Cotangent) := by
  -- Route correction: the unfinished chart route imported too much API and hit stale prefix
  -- objects.  The current skeleton first extracts the raw syntomic fields available from the
  -- basic owner API, then the remaining proof should build the localized conormal bridge.
  have hfinitePresentation :
      Algebra.FinitePresentation R (Localization.Away g) :=
    finitePresentation_of_syntomic_algebraMap hsyntomic
  have hflatRingHom : (algebraMap R (Localization.Away g)).Flat :=
    RingHom.Syntomic.flat hsyntomic
  have hlocalCompleteIntersectionFibers :
      (algebraMap R (Localization.Away g)).HasLocalCompleteIntersectionFibers :=
    RingHom.Syntomic.hasLocalCompleteIntersectionFibers hsyntomic
  obtain
    ⟨sideConditionPrimeCharts, hsideConditionPrimeCover, hsideConditionPrimeCharts⟩ :=
      syntomicSideConditionPrimeCover_finset_span_top_of_syntomic_algebraMap hsyntomic
  have hprimeSideConditions :
      ∀ q : PrimeSpectrum (Localization.Away g),
        ∃ a : Localization.Away g, a ∉ q.asIdeal ∧
          Algebra.FinitePresentation R (Localization.Away a) ∧
          (Localization.localRingHom (q.asIdeal.under R) q.asIdeal
            (algebraMap R (Localization.Away g)) rfl).Flat ∧
          (algebraMap R (Localization.Away g)).HasLocalCompleteIntersectionFibers :=
    fun q ↦ by
      -- Forget the finite indexing set and keep the prime-local witness needed by the
      -- at-prime relative-GCI bridge.
      obtain ⟨a, _ha_mem, ha_not_mem, ha_finitePresentation, ha_flat, ha_lci⟩ :=
        hsideConditionPrimeCharts q
      exact ⟨a, ha_not_mem, ha_finitePresentation, ha_flat, ha_lci⟩
  -- Package the already available finite-presentation chart as a finite cover, matching the
  -- finite-cover shape used by the eventual local-to-global patching theorem, and keep the
  -- flat/LCI fields attached for the later relative-GCI spreading bridge.
  -- TODO: strengthen the verified primewise side-condition cover `hsideConditionPrimeCover` to
  -- the relative-GCI principal-open cover supplied by Lemma `10.136.15`, then prove local
  -- finite projectivity of `LocalizedModule.Away g I.Cotangent` on each chart and patch over
  -- the unit-ideal cover.  The still-missing step is the chart conormal transport from
  -- `relativeGCI_conormalModule_has_basis` and `localized_presentation_cotangent_stable_equiv`.
  sorry

end

end Algebra
