import Mathlib
import StacksProject_2024.Chap10.Definition_10_104_6
import StacksProject_2024.Chap10.Definition_10_135_1
import StacksProject_2024.Chap10.Lemma_10_17_6
import StacksProject_2024.Chap10.Lemma_10_104_2
import StacksProject_2024.Chap10.Lemma_10_104_7
import StacksProject_2024.Chap10.Lemma_10_106_3
import StacksProject_2024.Chap10.Lemma_10_129_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-- Helper for Chap10 Lemma 10 135 3: the self-module of a ring has full support. -/
private lemma selfModule_support_eq_univ (R : Type*) [CommRing R] :
    Module.support R R = Set.univ := by
  -- The self-module support is the zero locus of the identity algebra map, hence all primes.
  have hker : RingHom.ker (RingHom.id R) = (⊥ : Ideal R) := by
    ext x
    simp
  simpa [hker, PrimeSpectrum.zeroLocus_bot] using
    (show Module.support R R = PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R R)) from
      Module.support_of_algebra)

/-- Helper for Chap10 Lemma 10 135 3: every field is Cohen-Macaulay as a ring. -/
private theorem field_cohenMacaulayRing (K : Type*) [Field K] : CohenMacaulayRing K := by
  -- A field is a regular local ring, so the self-module is Cohen-Macaulay; full support upgrades
  -- that local statement to the global ring owner.
  letI : Module.CohenMacaulay K K := regularLocalRing_selfModule_cohenMacaulay
  letI : Module.LocallyCohenMacaulay K K :=
    Module.locallyCohenMacaulay_of_cohenMacaulay K K (selfModule_support_eq_univ K)
  exact CohenMacaulayRing.mk

/-- Helper for Chap10 Lemma 10 135 3: the zero-ring convention gives a vacuous
Cohen-Macaulay ring. -/
private theorem cohenMacaulayRing_of_subsingleton (R : Type*) [CommRing R] [Subsingleton R] :
    CohenMacaulayRing R := by
  -- There are no prime ideals in a subsingleton ring, so the local Cohen-Macaulay condition is
  -- vacuous; Noetherianity and self-finiteness are inferable.
  refine
    { toIsNoetherian := inferInstance
      toLocallyCohenMacaulay := ?_ }
  refine
    { toFinite := inferInstance
      localizedModule_cohenMacaulay := ?_ }
  intro p
  exact False.elim (p.2.ne_top (Subsingleton.elim _ _))

/-- Helper for Chap10 Lemma 10 135 3: Cohen-Macaulayness is preserved by a linear equivalence
over a fixed Noetherian local ring. -/
private theorem cohenMacaulay_of_linearEquiv
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) [hM : Module.CohenMacaulay A M] :
    Module.CohenMacaulay A N := by
  -- Transport the defining equality through the support-dimension and depth invariance lemmas.
  let _ : Module.Finite A N := Module.Finite.equiv e
  exact ⟨by
    rw [← Module.supportDim_eq_of_equiv e, ← moduleDepth_eq_of_equiv e,
      hM.supportDim_eq_moduleDepth]⟩

/-- Helper for Chap10 Lemma 10 135 3: a ring equivalence transports the Cohen-Macaulay
self-module condition between Noetherian local rings. -/
private theorem cohenMacaulaySelf_of_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsNoetherianRing A] [IsLocalRing B] [IsNoetherianRing B]
    (e : A ≃+* B) (hA : Module.CohenMacaulay A A) :
    Module.CohenMacaulay B B := by
  -- Regard the equivalence as a surjective algebra map, first transporting the source
  -- self-module across the induced linear equivalence over `A`.
  letI : Algebra A B := e.toRingHom.toAlgebra
  have hsurj : Function.Surjective (algebraMap A B) := by
    simpa using e.surjective
  have hinj : Function.Injective (Algebra.linearMap A B) := by
    simpa using e.injective
  let eA : A ≃ₗ[A] B := LinearEquiv.ofBijective (Algebra.linearMap A B) ⟨hinj, hsurj⟩
  have hAB : Module.CohenMacaulay A B := by
    letI : Module.CohenMacaulay A A := hA
    exact cohenMacaulay_of_linearEquiv eA
  -- The surjective scalar-restriction criterion turns the transported `A`-module statement into
  -- the desired self-module statement over `B`.
  exact
    (Module.cohenMacaulay_iff_restrictScalars_of_surjective
      (R := A) (S := B) (N := B) hsurj).mpr hAB

/-- Helper for Chap10 Lemma 10 135 3: quotienting a local ring by the ideal of a regular list
again gives a local ring. -/
private theorem quotient_isLocalRing_of_regularList
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {xs : List R}
    (hreg : RingTheory.Sequence.IsRegular R xs) :
    IsLocalRing (R ⧸ Ideal.ofList xs) := by
  -- Regular lists in a local ring generate a proper ideal contained in the maximal ideal.
  have hI : Ideal.ofList xs ≤ IsLocalRing.maximalIdeal R :=
    IsRegular.ofList_le_maximalIdeal hreg
  have hne : Ideal.ofList xs ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hI
  have : Nontrivial (R ⧸ Ideal.ofList xs) := by
    rw [Ideal.Quotient.nontrivial_iff]
    exact hne
  -- The quotient map is surjective, and quotients of nontrivial local rings by proper ideals are
  -- local.
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- Helper for Chap10 Lemma 10 135 3: quotienting a Cohen-Macaulay local ring by a regular
sequence gives a Cohen-Macaulay local self-module, and this property transports across a ring
equivalence. -/
private theorem cohenMacaulaySelf_of_quotient_regularList_of_ringEquiv
    {R T : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Module.CohenMacaulay R R] [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    {xs : List R} (hreg : RingTheory.Sequence.IsRegular R xs)
    (e : (R ⧸ Ideal.ofList xs) ≃+* T) :
    Module.CohenMacaulay T T := by
  -- First apply the regular-sequence quotient theorem to the full prefix `xs.take xs.length`.
  letI : IsLocalRing (R ⧸ Ideal.ofList xs) := quotient_isLocalRing_of_regularList hreg
  letI : IsLocalRing (R ⧸ Ideal.ofList (xs.take xs.length)) :=
    quotient_isLocalRing_of_regularList (by simpa [List.take_length] using hreg)
  have hquot :
      Module.CohenMacaulay
        (R ⧸ Ideal.ofList (xs.take xs.length))
        (R ⧸ Ideal.ofList (xs.take xs.length)) :=
    selfModule_cohenMacaulay_quotient_take_of_isRegular (R := R) hreg (i := xs.length)
  let etake : (R ⧸ Ideal.ofList (xs.take xs.length)) ≃+* T :=
    (Ideal.quotEquivOfEq (by rw [List.take_length])).trans e
  -- Then transport the quotient self-module condition along the supplied ring equivalence.
  exact cohenMacaulaySelf_of_ringEquiv etake hquot

/-- Helper for Chap10 Lemma 10 135 3: a zero-dimensional Noetherian local ring is
Cohen-Macaulay as a self-module. -/
private theorem cohenMacaulaySelf_of_ringKrullDim_eq_zero
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 0) :
    Module.CohenMacaulay R R := by
  -- The self-module support dimension is the ring Krull dimension, so zero ring dimension forces
  -- zero support dimension and then the standard depth bound forces depth zero.
  refine Module.CohenMacaulay.mk ?_
  have hsupport : Module.supportDim R R = 0 := by
    simpa [Module.supportDim_self_eq_ringKrullDim] using hdim
  have hdepth_le : WithBot.some (moduleDepth R R : ℕ∞) ≤ 0 := by
    rw [← hsupport]
    exact depth_le_supportDim
  have hdepth : moduleDepth R R = 0 := by
    simpa using hdepth_le
  simpa [hsupport, hdepth]

/-- Helper for Chap10 Lemma 10 135 3: if a Noetherian ring has dimension zero, then every prime
localization is Cohen-Macaulay as a self-module. -/
private theorem cohenMacaulaySelf_atPrime_of_ringKrullDim_eq_zero
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 0) (q : PrimeSpectrum A) :
    Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal) := by
  -- Compare the dimension of the local ring to the height of the prime, then bound that height
  -- by the global zero dimension.
  have hheight_le : ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) ≤ 0 := by
    simpa [hdim] using
      (Ideal.height_le_ringKrullDim_of_ne_top
        (I := q.asIdeal) (Ideal.IsPrime.ne_top inferInstance))
  have hheight : ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) = 0 :=
    le_antisymm hheight_le (WithBot.coe_le_coe.mpr (zero_le q.asIdeal.height))
  have hlocdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0 := by
    calc
      ringKrullDim (Localization.AtPrime q.asIdeal) =
          ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) := by
            simpa using
              IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
                (Localization.AtPrime q.asIdeal)
      _ = 0 := hheight
  -- The localized ring is Noetherian and local, so the zero-dimensional local helper applies.
  exact cohenMacaulaySelf_of_ringKrullDim_eq_zero
    (Localization.AtPrime q.asIdeal) hlocdim

/-- Helper for Chap10 Lemma 10 135 3: a finite relation list and the range of the indexed
family generate the same ideal. -/
private theorem ideal_ofList_ofFn_eq_span_range {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) :
    Ideal.ofList (List.ofFn x) = Ideal.span (Set.range x) := by
  -- Both sides are generated by exactly the same finite family, just encoded as a list or a range.
  rw [Ideal.ofList]
  congr
  ext r
  constructor
  · intro hr
    rcases List.mem_ofFn.mp hr with ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- Helper for Chap10 Lemma 10 135 3: the list of presentation relations generates the
presentation kernel. -/
private theorem ofList_relations_eq_presentationKernel
    {A : Type*} [CommRing A] [Algebra k A] {n c : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c)) :
    Ideal.ofList (List.ofFn P.relation) = P.ker := by
  -- Normalize the finite list of relations to the presentation owner's range-spanning kernel.
  calc
    Ideal.ofList (List.ofFn P.relation) = Ideal.span (Set.range P.relation) :=
      ideal_ofList_ofFn_eq_span_range P.relation
    _ = P.ker := P.span_range_relation_eq_ker

/-- Helper for Chap10 Lemma 10 135 3: the quotient by the chosen relation list is the presented
algebra. -/
private noncomputable def presentationRelationQuotientEquiv
    {A : Type*} [CommRing A] [Algebra k A] {n c : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c)) :
    (P.Ring ⧸ Ideal.ofList (List.ofFn P.relation)) ≃+* A :=
  (Ideal.quotientEquivAlgOfEq k (ofList_relations_eq_presentationKernel P)).toRingEquiv.trans
    P.quotientEquiv.toRingEquiv

/-- Helper for Chap10 Lemma 10 135 3: the relation quotient of an expected-dimension
presentation satisfies the codimension inequality needed for the Cohen-Macaulay regularity
criterion. -/
private theorem presentationQuotient_dimension_add_relations_le
    {A : Type*} [CommRing A] [Algebra k A] {n c : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c))
    (hP : ringKrullDim A = P.dimension) (hcn : c ≤ n) :
    ringKrullDim (P.Ring ⧸ Ideal.ofList (List.ofFn P.relation)) +
        (List.ofFn P.relation).length ≤
      ringKrullDim P.Ring := by
  -- Transport the quotient dimension to `A`, then reduce the remaining comparison to
  -- `(n - c) + c = n`.
  have hquot :
      ringKrullDim (P.Ring ⧸ Ideal.ofList (List.ofFn P.relation)) =
        ringKrullDim A :=
    ringKrullDim_eq_of_ringEquiv (presentationRelationQuotientEquiv P)
  have hAdim : ringKrullDim A = ((n - c : ℕ) : WithBot ℕ∞) :=
    hP.trans (congrArg (fun m : ℕ => (m : WithBot ℕ∞))
      (presentation_dimension_eq_fin_sub P))
  have hpoly : ringKrullDim P.Ring = (n : WithBot ℕ∞) := by
    simpa using MvPolynomial.ringKrullDim_of_isNoetherianRing (R := k) (ι := Fin n)
  have hnat : (n - c) + c = n := Nat.sub_add_cancel hcn
  have hadd :
      ((n - c : ℕ) : WithBot ℕ∞) + c = (n : WithBot ℕ∞) := by
    simpa [← WithBot.coe_add] using
      congrArg (fun m : ℕ => (m : WithBot ℕ∞)) hnat
  exact le_of_eq <| by
    calc
      ringKrullDim (P.Ring ⧸ Ideal.ofList (List.ofFn P.relation)) +
          (List.ofFn P.relation).length =
          ((n - c : ℕ) : WithBot ℕ∞) + c := by
            rw [hquot, hAdim, List.length_ofFn]
      _ = (n : WithBot ℕ∞) := hadd
      _ = ringKrullDim P.Ring := hpoly.symm

/-- Helper for Chap10 Lemma 10 135 3: the presentation map carries the contracted prime
complement onto the target prime complement. -/
private theorem presentationPrimeCompl_map_eq
    {A : Type*} [CommRing A] [Algebra k A] {n c : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c)) (q : PrimeSpectrum A) :
    Submonoid.map (algebraMap P.Ring A)
        (PrimeSpectrum.comap (algebraMap P.Ring A) q).asIdeal.primeCompl =
      q.asIdeal.primeCompl := by
  -- Surjectivity of the presentation map lifts target denominators back to the polynomial ring.
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    rcases P.algebraMap_surjective y with ⟨x, rfl⟩
    exact ⟨x, hy, rfl⟩

/-- Helper for Chap10 Lemma 10 135 3: the induced map on prime localizations is surjective. -/
private theorem localizedPresentationMap_surjective
    {A : Type*} [CommRing A] [Algebra k A] {n c : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c)) (q : PrimeSpectrum A) :
    Function.Surjective
      (Localization.localRingHom
        (PrimeSpectrum.comap (algebraMap P.Ring A) q).asIdeal q.asIdeal
        (algebraMap P.Ring A) rfl) := by
  -- Rebuild the fraction-level proof directly so universe levels and the localized submonoids do
  -- not have to be inferred through an auxiliary `IsLocalization` instance.
  intro x
  rcases IsLocalization.exists_mk'_eq q.asIdeal.primeCompl x with ⟨b, s, rfl⟩
  obtain ⟨a, rfl⟩ := P.algebraMap_surjective b
  obtain ⟨t, ht⟩ := P.algebraMap_surjective s.1
  refine ⟨IsLocalization.mk'
      (M := (PrimeSpectrum.comap (algebraMap P.Ring A) q).asIdeal.primeCompl)
      (Localization.AtPrime
        (PrimeSpectrum.comap (algebraMap P.Ring A) q).asIdeal) a ⟨t, ?_⟩, ?_⟩
  · change algebraMap P.Ring A t ∈ q.asIdeal.primeCompl
    simpa [ht] using s.2
  · rw [Localization.localRingHom_mk']
    simp [ht]

/-- Helper for Chap10 Lemma 10 135 3: the kernel of the localized presentation map is generated
by the localized relation list. -/
private theorem localizedPresentationMap_ker_eq_relationIdeal
    {A : Type*} [CommRing A] [Algebra k A] {n c : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c)) (q : PrimeSpectrum A) :
    RingHom.ker
        (Localization.localRingHom
          (PrimeSpectrum.comap (algebraMap P.Ring A) q).asIdeal q.asIdeal
          (algebraMap P.Ring A) rfl) =
      Ideal.ofList
        (List.ofFn fun i : Fin c =>
          algebraMap P.Ring
            (Localization.AtPrime
              (PrimeSpectrum.comap (algebraMap P.Ring A) q).asIdeal)
            (P.relation i)) := by
  -- Compute the localization kernel by `IsLocalization.ker_map`, then rewrite the presentation
  -- kernel as the ideal generated by the chosen relation list.
  let qPoly : PrimeSpectrum P.Ring :=
    PrimeSpectrum.comap (algebraMap P.Ring A) q
  calc
    RingHom.ker
        (Localization.localRingHom qPoly.asIdeal q.asIdeal
          (algebraMap P.Ring A) rfl) =
        Ideal.map (algebraMap P.Ring (Localization.AtPrime qPoly.asIdeal)) P.ker := by
          simpa [qPoly, Localization.localRingHom] using
            (IsLocalization.ker_map
              (S := Localization.AtPrime qPoly.asIdeal)
              (Q := Localization.AtPrime q.asIdeal)
              (g := algebraMap P.Ring A)
              (presentationPrimeCompl_map_eq P q))
    _ = Ideal.map (algebraMap P.Ring (Localization.AtPrime qPoly.asIdeal))
        (Ideal.ofList (List.ofFn P.relation)) := by
          rw [ofList_relations_eq_presentationKernel P]
    _ = Ideal.ofList
        (List.ofFn fun i : Fin c =>
          algebraMap P.Ring (Localization.AtPrime qPoly.asIdeal) (P.relation i)) := by
          rw [Ideal.map_ofList]
          rw [← List.ofFn_comp']

/-- Helper for Chap10 Lemma 10 135 3: the presentation relations form a regular sequence after
localizing at the prime over `q` in the expected-codimension branch. -/
private theorem presentationRelations_regular_atPrime_of_expectedDimension
    {A : Type*} [CommRing A] [Algebra k A] {n c : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c))
    (hP : ringKrullDim A = P.dimension) (q : PrimeSpectrum A) (hcn : c ≤ n) :
    RingTheory.Sequence.IsRegular
      (Localization.AtPrime (PrimeSpectrum.comap (algebraMap P.Ring A) q).asIdeal)
      (List.ofFn fun i : Fin c =>
        algebraMap P.Ring
          (Localization.AtPrime (PrimeSpectrum.comap (algebraMap P.Ring A) q).asIdeal)
          (P.relation i)) := by
  -- Apply the Cohen-Macaulay/equidimensional regularity criterion to the polynomial presentation
  -- ring, after proving the expected quotient-dimension inequality.
  let qPoly : PrimeSpectrum P.Ring :=
    PrimeSpectrum.comap (algebraMap P.Ring A) q
  letI : CohenMacaulayRing P.Ring :=
    cohenMacaulayRing_mvPolynomial (field_cohenMacaulayRing k) n
  have hle :
      ringKrullDim (P.Ring ⧸ Ideal.ofList (List.ofFn P.relation)) +
          (List.ofFn P.relation).length ≤
        ringKrullDim P.Ring :=
    presentationQuotient_dimension_add_relations_le P hP hcn
  have hcontains : Ideal.ofList (List.ofFn P.relation) ≤ qPoly.asIdeal := by
    -- Elements of the presentation kernel map to zero in `A`, hence lie in every contracted
    -- prime over `A`.
    rw [ofList_relations_eq_presentationKernel P]
    intro x hx
    have hx0 : algebraMap P.Ring A x = 0 := by
      rw [P.algebraMap_apply]
      exact P.aeval_val_eq_zero hx
    change algebraMap P.Ring A x ∈ q.asIdeal
    simpa [hx0]
  have hregular :=
    (ringKrullDim_quotient_add_length_eq_and_isRegular_atPrime_of_cohenMacaulay_equidimensional
      (S := P.Ring) (fs := List.ofFn P.relation) hle).2 qPoly hcontains
  -- The imported criterion returns `List.map`; rewrite it to the fixed `List.ofFn` spelling used
  -- by the quotient comparison.
  simpa [qPoly, List.map_ofFn] using hregular

/-- Helper for Chap10 Lemma 10 135 3: the localized quotient of the polynomial presentation is
the target local ring. -/
private noncomputable def localizedPresentationQuotientEquiv
    {A : Type*} [CommRing A] [Algebra k A] {n c : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c)) (q : PrimeSpectrum A) :
    ((Localization.AtPrime
        (PrimeSpectrum.comap (algebraMap P.Ring A) q).asIdeal) ⧸
      Ideal.ofList
        (List.ofFn fun i : Fin c =>
          algebraMap P.Ring
            (Localization.AtPrime
              (PrimeSpectrum.comap (algebraMap P.Ring A) q).asIdeal)
            (P.relation i))) ≃+* Localization.AtPrime q.asIdeal :=
  (Ideal.quotientEquivAlgOfEq ℤ
    (localizedPresentationMap_ker_eq_relationIdeal P q).symm).toRingEquiv.trans
      (RingHom.quotientKerEquivOfSurjective
        (localizedPresentationMap_surjective P q))

/-- Helper for Chap10 Lemma 10 135 3: the localized presentation at a prime is
Cohen-Macaulay when the presentation has the expected dimension. -/
private theorem presentationAtPrime_cohenMacaulay_of_expectedDimension
    {A : Type*} [CommRing A] [Algebra k A] {n c : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c))
    (hP : ringKrullDim A = P.dimension) (q : PrimeSpectrum A) :
    Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal) := by
  -- Split off the overdetermined case first: then the expected presentation dimension is zero,
  -- so every prime localization is Cohen-Macaulay by the zero-dimensional helper.
  by_cases hcn : c ≤ n
  · let qPoly : PrimeSpectrum P.Ring :=
      PrimeSpectrum.comap (algebraMap P.Ring A) q
    letI : Algebra.FinitePresentation k A := P.finitePresentation_of_isFinite
    letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
    letI : CohenMacaulayRing P.Ring :=
      cohenMacaulayRing_mvPolynomial (field_cohenMacaulayRing k) n
    have hpolyLocalCM :
        Module.CohenMacaulay (Localization.AtPrime qPoly.asIdeal)
          (Localization.AtPrime qPoly.asIdeal) :=
      localizedRing_cohenMacaulay P.Ring qPoly
    letI : Module.CohenMacaulay (Localization.AtPrime qPoly.asIdeal)
        (Localization.AtPrime qPoly.asIdeal) := hpolyLocalCM
    have hreg :
        RingTheory.Sequence.IsRegular
          (Localization.AtPrime qPoly.asIdeal)
          (List.ofFn fun i : Fin c =>
            algebraMap P.Ring (Localization.AtPrime qPoly.asIdeal) (P.relation i)) := by
      -- The imported regularity criterion supplies the regular sequence at the contracted prime.
      simpa [qPoly] using
        presentationRelations_regular_atPrime_of_expectedDimension P hP q hcn
    -- The localized quotient by that regular relation list is `A_q`, so transport the
    -- Cohen-Macaulay quotient self-module statement across the quotient equivalence.
    exact cohenMacaulaySelf_of_quotient_regularList_of_ringEquiv hreg
      (localizedPresentationQuotientEquiv P q)
  · letI : Algebra.FinitePresentation k A := P.finitePresentation_of_isFinite
    letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
    have hdim : ringKrullDim A = 0 := by
      have hsub : n - c = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hcn)
      simpa [hsub] using
        hP.trans (congrArg (fun m : ℕ => (m : WithBot ℕ∞))
          (presentation_dimension_eq_fin_sub P))
    exact cohenMacaulaySelf_atPrime_of_ringKrullDim_eq_zero hdim q

/-- Helper for Chap10 Lemma 10 135 3: if `g` avoids a prime `p`, then Cohen-Macaulayness at the
corresponding prime of `A_g` transports back to the localization `A_p`. -/
private theorem cohenMacaulaySelf_atPrime_of_localizationAway
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (p : PrimeSpectrum A) (g : A) (hg : g ∉ p.asIdeal)
    [CohenMacaulayRing (Localization.Away g)] :
    Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal) := by
  let B := Localization.Away g
  let q : PrimeSpectrum B :=
    (primeSpectrum_localizationAway_homeomorph_D g).symm ⟨p, (mem_D g p).2 hg⟩
  have hq :
      PrimeSpectrum.comap (algebraMap A B) q = p := by
    -- The selected chart prime is the inverse image of `p` under the localization-away
    -- homeomorphism, so its contraction is exactly `p`.
    have hqD : (primeSpectrum_localizationAway_homeomorph_D g q).1 = p :=
      congrArg Subtype.val
      ((primeSpectrum_localizationAway_homeomorph_D g).apply_symm_apply ⟨p, (mem_D g p).2 hg⟩)
    simpa [B, primeSpectrum_localizationAway_homeomorph_D_apply] using hqD
  let e : Localization.AtPrime p.asIdeal ≃ₐ[A] Localization.AtPrime q.asIdeal := by
    -- Iterated localization of `A_g` at `q` is the same as localizing `A` at the contracted
    -- prime; `hq` identifies that contracted prime with `p`.
    let e0 :
        Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q).asIdeal ≃ₐ[A]
          Localization.AtPrime q.asIdeal :=
      IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (Submonoid.powers g) q.asIdeal
    rw [hq] at e0
    exact e0
  have hchartLocalCM :
      Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal) :=
    localizedRing_cohenMacaulay B q
  -- Transport the chart-local statement along the inverse comparison equivalence.
  exact cohenMacaulaySelf_of_ringEquiv e.symm.toRingEquiv hchartLocalCM

/-- Helper for Chap10 Lemma 10 135 3: a global complete intersection over a field is
Cohen-Macaulay. -/
private theorem cohenMacaulayRing_of_isGlobalCompleteIntersection
    {A : Type*} [CommRing A] [Algebra k A]
    (hG : IsGlobalCompleteIntersection k A) : CohenMacaulayRing A := by
  -- Split the owner data into the zero-ring convention and the finite-presentation branch.
  rcases hG.presentation_or_subsingleton with hsub | hpres
  · letI : Subsingleton A := hsub
    exact cohenMacaulayRing_of_subsingleton A
  · rcases hpres with ⟨n, c, P, hP⟩
    letI : IsGlobalCompleteIntersection k A := hG
    letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
    have hpolyCM : CohenMacaulayRing (MvPolynomial (Fin n) k) :=
      cohenMacaulayRing_mvPolynomial (field_cohenMacaulayRing k) n
    letI : CohenMacaulayRing (MvPolynomial (Fin n) k) := hpolyCM
    refine
      { toIsNoetherian := inferInstance
        toLocallyCohenMacaulay := ?_ }
    refine
      { toFinite := inferInstance
        localizedModule_cohenMacaulay := ?_ }
    intro q
    let qPoly : PrimeSpectrum P.Ring :=
      PrimeSpectrum.comap (algebraMap P.Ring A) q
    have hpolyLocalCM :
        Module.CohenMacaulay (Localization.AtPrime qPoly.asIdeal)
          (Localization.AtPrime qPoly.asIdeal) :=
      localizedRing_cohenMacaulay (MvPolynomial (Fin n) k) qPoly
    -- The remaining presentation-local commutative algebra is isolated in the preceding helper;
    -- the global-CI proof now only has to apply it at the chosen prime.
    exact presentationAtPrime_cohenMacaulay_of_expectedDimension P hP q

/-- Helper for Chap10 Lemma 10 135 3: local Cohen-Macaulayness descends from a finite
principal-open cover. -/
private theorem locallyCohenMacaulay_self_of_basicOpen_cover
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (s : Finset A) (hs : Ideal.span (s : Set A) = ⊤)
    (hCM : ∀ g ∈ s, CohenMacaulayRing (Localization.Away g)) :
    Module.LocallyCohenMacaulay A A := by
  -- It remains to check the Cohen-Macaulay condition after localizing at an arbitrary prime.
  refine
    { toFinite := inferInstance
      localizedModule_cohenMacaulay := ?_ }
  intro p
  have hchart : ∃ g ∈ s, g ∉ p.asIdeal := by
    -- A prime meeting every chart element would contain the unit ideal generated by the cover.
    by_contra hnone
    have hle : Ideal.span (s : Set A) ≤ p.asIdeal := by
      rw [Ideal.span_le]
      intro x hx
      by_contra hxnot
      exact hnone ⟨x, hx, hxnot⟩
    have htop_le : (⊤ : Ideal A) ≤ p.asIdeal := by
      simpa [hs] using hle
    exact p.2.ne_top (top_le_iff.mp htop_le)
  rcases hchart with ⟨g, hgs, hgp⟩
  letI : CohenMacaulayRing (Localization.Away g) := hCM g hgs
  -- The chosen chart prime contracts to `p`, so the iterated-localization comparison transports
  -- the chart-local Cohen-Macaulay self-module condition back to `A_p`.
  exact cohenMacaulaySelf_atPrime_of_localizationAway p g hgp

/-
Domain-style sampling in the local-complete-intersection / Cohen-Macaulay interface:
- primary domain: commutative algebra of local complete intersections over a field and the
  resulting global Cohen-Macaulay ring property;
- sampled owner declarations:
  `IsLocalCompleteIntersection`,
  `IsGlobalCompleteIntersection`,
  `Module.LocallyCohenMacaulay`,
  `CohenMacaulayRing`;
- best owner abstraction: this file is a `bridge/view` from the source-facing field-algebra owner
  `IsLocalCompleteIntersection k S` to the chapter-global ring owner `CohenMacaulayRing S`;
- primitive data: only the owner hypothesis `hCI : IsLocalCompleteIntersection k S`;
- derived API: finite presentation and hence finite type of `S`, together with the primewise
  Cohen-Macaulay self-module statements packaged by `CohenMacaulayRing`.

Source/core/bridge triage:
* source-facing: Lemma `10.135.3`, asserting that a local complete intersection over a field is a
  Cohen-Macaulay ring;
* core/canonical: `IsLocalCompleteIntersection k S`, `Module.LocallyCohenMacaulay S S`, and
  `CohenMacaulayRing S`;
* bridge/view: passage to each localization `Localization.AtPrime q.asIdeal`, where the local
  complete-intersection hypothesis becomes a complete-intersection local ring and hence a
  Cohen-Macaulay self-module.

The public theorem should therefore take the source-level hypothesis explicitly and return the
global owner `CohenMacaulayRing S` directly, rather than hide the main input in an instance
argument.
-/
-- Proof sketch: for each prime `p` of `S`, localize at `p`. A local complete intersection over a
-- field stays a local complete intersection after localization, so `Sₚ` admits a presentation by
-- quotienting a regular local ring by a regular sequence. Regular local rings are
-- Cohen-Macaulay, and quotienting a Cohen-Macaulay local ring by a regular sequence remains
-- Cohen-Macaulay. Hence every prime localization of `S` is Cohen-Macaulay, which is exactly the
-- global `CohenMacaulayRing` condition. The theorem header does not repeat a separate finite-type
-- or Noetherian hypothesis, since that data is derived from `hCI`.
/-- Chap10 Lemma 10 135 3: a finite type `k`-algebra that is a local complete intersection over
`k` is a Cohen-Macaulay ring. -/
@[stacks 00SB]
theorem cohenMacaulayRing_of_isLocalCompleteIntersection
    (hCI : IsLocalCompleteIntersection k S) : CohenMacaulayRing S := by
  -- Use the finite basic-open cover in the LCI owner, prove each chart Cohen-Macaulay from the
  -- global-CI helper, and descend the local condition back to `S`.
  letI : IsLocalCompleteIntersection k S := hCI
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  rcases hCI.exists_basicOpen_cover with ⟨s, hs, hglobal⟩
  refine
    { toIsNoetherian := inferInstance
      toLocallyCohenMacaulay := ?_ }
  exact locallyCohenMacaulay_self_of_basicOpen_cover s hs fun g hg =>
    cohenMacaulayRing_of_isGlobalCompleteIntersection (hglobal g hg)

end
