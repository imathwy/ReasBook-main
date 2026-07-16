import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_144_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Etale R S]

/- The global proof starts by replacing the pointwise standard-étale neighborhoods supplied by
`IsEtaleAt.exists_isStandardEtale` with a finite principal-open cover of `Spec S`. -/
/-- Helper for Chap10 Lemma 10 144 6: the elements whose away-localizations are standard étale
span the unit ideal. -/
private theorem standardEtaleAwayLocus_span_eq_top :
    Ideal.span ({f : S | IsStandardEtale R (Localization.Away f)}) = ⊤ := by
  -- Each prime lies in a principal open on which the étale algebra is standard étale.
  have hcover :
      (⨆ f ∈ ({f : S | IsStandardEtale R (Localization.Away f)}),
          PrimeSpectrum.basicOpen f) = ⊤ := by
    apply SetLike.ext'
    change (↑(⨆ f ∈ ({f : S | IsStandardEtale R (Localization.Away f)}),
          PrimeSpectrum.basicOpen f) : Set (PrimeSpectrum S)) = Set.univ
    rw [Set.eq_univ_iff_forall]
    intro q
    have hEtaleAt : IsEtaleAt R q.asIdeal := by
      have hall : etaleLocus R S = Set.univ :=
        (etaleLocus_eq_univ_iff_etale (R := R) (A := S)).2 inferInstance
      have hqmem : q ∈ etaleLocus R S := by
        rw [hall]
        exact Set.mem_univ q
      simpa using hqmem
    obtain ⟨f, hfq, hfstd⟩ :=
      IsEtaleAt.exists_isStandardEtale (R := R) (S := S) (Q := q.asIdeal)
    have hbasic : q ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum S)) := by
      simpa [PrimeSpectrum.mem_basicOpen] using hfq
    exact
      (show (PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) ≤
          ⨆ g ∈ ({g : S | IsStandardEtale R (Localization.Away g)}),
            PrimeSpectrum.basicOpen g from
        le_iSup_of_le f <| le_iSup_of_le hfstd le_rfl) hbasic
  -- The affine-spectrum basic-open criterion converts this cover into a unit-ideal statement.
  exact PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hcover

/-- Helper for Chap10 Lemma 10 144 6: an étale algebra has a finite standard-étale away cover
whose elements span the unit ideal. -/
private theorem existsFiniteStandardEtaleAwayCover :
    ∃ t : Finset S, (∀ f ∈ t, IsStandardEtale R (Localization.Away f)) ∧
      Ideal.span ((t : Finset S) : Set S) = ⊤ := by
  -- The unit-ideal cover above has a finite subcover because membership in an ideal span is
  -- already witnessed by finitely many generators.
  obtain ⟨t, ht_subset, ht_span⟩ :=
    (Ideal.span_eq_top_iff_finite ({f : S | IsStandardEtale R (Localization.Away f)})).mp
      (standardEtaleAwayLocus_span_eq_top (R := R) (S := S))
  exact ⟨t, fun f hf ↦ ht_subset hf, ht_span⟩

/-- Helper for Chap10 Lemma 10 144 6: if a finite set spans the unit ideal, then every prime
misses at least one element of that finite set. -/
private lemma exists_mem_finset_not_mem_prime_of_span_eq_top
    {A : Type*} [CommRing A] (t : Finset A) (q : PrimeSpectrum A)
    (hspan : Ideal.span ((t : Finset A) : Set A) = ⊤) :
    ∃ f ∈ t, f ∉ q.asIdeal := by
  -- If every generator lay in the prime, the ideal they span would be contained in the prime.
  by_contra h
  have hsubset : ((t : Finset A) : Set A) ⊆ q.asIdeal := by
    intro f hf
    by_contra hfq
    exact h ⟨f, hf, hfq⟩
  have hle : Ideal.span ((t : Finset A) : Set A) ≤ q.asIdeal :=
    Ideal.span_le.mpr hsubset
  -- The span is the top ideal, contradicting properness of the prime ideal.
  have htop : (⊤ : Ideal A) ≤ q.asIdeal := by
    simpa [hspan] using hle
  have hqtop : q.asIdeal = ⊤ := top_unique htop
  exact (PrimeSpectrum.isPrime q).ne_top hqtop

/-- Helper for Chap10 Lemma 10 144 6: a prime avoiding `f` lifts to the localization away
from `f`. -/
private lemma existsPrimeOver_away_of_not_mem
    {A : Type*} [CommRing A] (q : PrimeSpectrum A) {f : A} (hf : f ∉ q.asIdeal) :
    ∃ qf : PrimeSpectrum (Localization.Away f),
      PrimeSpectrum.comap (algebraMap A (Localization.Away f)) qf = q := by
  -- The range of the localization map on spectra is exactly the principal open `D(f)`.
  have hmem : q ∈ (Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f)))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact (PrimeSpectrum.mem_basicOpen f q).2 hf
  -- Unpack membership in the range to obtain the desired localized prime.
  rcases hmem with ⟨qf, hqf⟩
  exact ⟨qf, hqf⟩

omit [Etale R S] in
/-- Helper for Chap10 Lemma 10 144 6: a finite principal-open cover of `Spec S` and
surjectivity over `Spec R` give a localized chart prime over every base prime. -/
private lemma existsLocalizedCoverPrimeOver
    (t : Finset S) (hspan : Ideal.span ((t : Finset S) : Set S) = ⊤)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)))
    (p : PrimeSpectrum R) :
    ∃ f ∈ t, ∃ qf : PrimeSpectrum (Localization.Away f),
      PrimeSpectrum.comap (algebraMap R (Localization.Away f)) qf = p := by
  -- Lift `p` to a prime of `S`, then choose a chart generator missed by that prime.
  obtain ⟨q, hq⟩ := hsurj p
  obtain ⟨f, hft, hfq⟩ := exists_mem_finset_not_mem_prime_of_span_eq_top t q hspan
  -- The missed generator localizes the prime, and functoriality of `comap` returns to `p`.
  obtain ⟨qf, hqf⟩ := existsPrimeOver_away_of_not_mem q hfq
  refine ⟨f, hft, qf, ?_⟩
  rw [← hq, ← hqf]
  rfl

omit [Etale R S] in
/-- Helper for Chap10 Lemma 10 144 6: faithful flatness of an algebra map supplies the flat
owner and the surjectivity-on-spectra field required by the final extension package. -/
private theorem faithfullyFlat_algebraMap_flat_and_spectrum_surjective
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (hff : (algebraMap A B).FaithfullyFlat) :
    Module.Flat A B ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) := by
  -- The ring-hom criterion gives ring-hom flatness together with spectral surjectivity.
  rcases RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hff with ⟨hflat, hsurj⟩
  -- Convert the flatness component to the module owner used in this theorem's statement.
  exact ⟨RingHom.flat_algebraMap_iff.mp hflat, hsurj⟩

omit [CommRing S] [Algebra R S] [Etale R S] in
/-- Helper for Chap10 Lemma 10 144 6: a local factorization through an away localization of a
component algebra pushes forward along an `R`-algebra map to an away localization of the target
algebra. -/
private lemma localFactorization_pushAway
    {A : Type*} {B : Type*} {T : Type*}
    [CommRing A] [CommRing B] [CommRing T] [Algebra R A] [Algebra R B] [Algebra R T]
    (ι : A →ₐ[R] B) (qB : PrimeSpectrum B) {g : A}
    (hg : g ∉ (PrimeSpectrum.comap ι.toRingHom qB).asIdeal)
    (hφ : Nonempty (T →ₐ[R] Localization.Away g)) :
    ∃ gB : B, gB ∉ qB.asIdeal ∧ Nonempty (T →ₐ[R] Localization.Away gB) := by
  -- Push the chosen denominator through the component map; the comap hypothesis is exactly
  -- the statement that this image is outside the target prime.
  refine ⟨ι g, ?_, ?_⟩
  · simpa [PrimeSpectrum.comap, Ideal.mem_comap] using hg
  · -- Compose the given factorization with the canonical map of away localizations.
    rcases hφ with ⟨φ⟩
    exact ⟨(Localization.awayMapₐ ι g).comp φ⟩

omit [CommRing S] [Algebra R S] [Etale R S] in
/-- Helper for Chap10 Lemma 10 144 6: the binary tensor product of two finite, finitely
presented, faithfully flat `R`-algebras has the same owner data. -/
private theorem tensorProductTwoExtensionData
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Finite R A] [Module.Finite R B]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B]
    (hA : (algebraMap R A).FaithfullyFlat) (hB : (algebraMap R B).FaithfullyFlat) :
    Module.Finite R (TensorProduct R A B) ∧
      Algebra.FinitePresentation R (TensorProduct R A B) ∧
        (algebraMap R (TensorProduct R A B)).FaithfullyFlat := by
  -- Finiteness is already an instance for tensor products of finite modules.
  refine ⟨inferInstance, ?_, ?_⟩
  · -- View the tensor product as an `A`-algebra by the left inclusion and compose finite
    -- presentation over `R` with finite presentation after base change.
    letI : Algebra A (TensorProduct R A B) := Algebra.TensorProduct.leftAlgebra
    letI : IsScalarTower R A (TensorProduct R A B) := inferInstance
    exact Algebra.FinitePresentation.trans R A (TensorProduct R A B)
  · -- Faithful flatness is stable under the same base-change-and-compose pattern.
    letI : Module.FaithfullyFlat R A := RingHom.faithfullyFlat_algebraMap_iff.mp hA
    letI : Module.FaithfullyFlat R B := RingHom.faithfullyFlat_algebraMap_iff.mp hB
    letI : Algebra A (TensorProduct R A B) := Algebra.TensorProduct.leftAlgebra
    letI : IsScalarTower R A (TensorProduct R A B) := inferInstance
    letI : Module.FaithfullyFlat A (TensorProduct R A B) := inferInstance
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr
      (Module.FaithfullyFlat.trans R A (TensorProduct R A B))

omit [CommRing S] [Algebra R S] [Etale R S] in
/-- Helper for Chap10 Lemma 10 144 6: a spectrum comap equality packages the target prime as
an element of the canonical `primesOver` fiber. -/
private lemma primeIdeal_mem_primesOver_of_comap_eq
    {A : Type*} [CommRing A] [Algebra R A]
    (p : PrimeSpectrum R) (q : PrimeSpectrum A)
    (h : PrimeSpectrum.comap (algebraMap R A) q = p) :
    q.asIdeal ∈ p.asIdeal.primesOver A := by
  -- Transport the built-in lying-over instance along the given equality of base primes.
  haveI : q.asIdeal.LiesOver p.asIdeal := by
    rw [← h]
    infer_instance
  exact ⟨PrimeSpectrum.isPrime q, inferInstance⟩

omit [CommRing S] [Algebra R S] [Etale R S] in
/-- Helper for Chap10 Lemma 10 144 6: pulling a final prime back to a component preserves its
image in the base spectrum. -/
private lemma componentPrime_comap_eq_base
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (ι : A →ₐ[R] B) (qB : PrimeSpectrum B) :
    PrimeSpectrum.comap (algebraMap R A) (PrimeSpectrum.comap ι.toRingHom qB) =
      PrimeSpectrum.comap (algebraMap R B) qB := by
  -- This is just functoriality of `Spec` plus the algebra-map compatibility of `ι`.
  rw [← PrimeSpectrum.comap_comp_apply]
  congr 1
  ext r
  exact ι.commutes r

omit [CommRing S] [Algebra R S] [Etale R S] in
/-- Helper for Chap10 Lemma 10 144 6: a universe-lifted copy of the base ring has the owner data
used as the empty tensor product. -/
private theorem uliftBaseExtensionData :
    Module.Finite R (ULift.{v} R) ∧
      Algebra.FinitePresentation R (ULift.{v} R) ∧
        (algebraMap R (ULift.{v} R)).FaithfullyFlat := by
  -- Finiteness is inherited by `ULift`, finite presentation is transported across the algebra
  -- equivalence, and faithful flatness follows because the algebra map is bijective.
  refine ⟨inferInstance, ?_, ?_⟩
  · exact Algebra.FinitePresentation.equiv (ULift.algEquiv (R := R) (A := R)).symm
  · exact RingHom.FaithfullyFlat.of_bijective
      ⟨fun a b h ↦ by simpa using congrArg ULift.down h,
        fun x ↦ ⟨x.down, by cases x; rfl⟩⟩

omit [CommRing S] [Algebra R S] [Etale R S] in
/-- Helper for Chap10 Lemma 10 144 6: finitely many finite, finitely presented, faithfully flat
`R`-algebras have an iterated tensor product with component maps from every inserted factor. -/
private theorem finiteTensorExtensionData
    {ι : Type*} (s : Finset ι)
    (A : ι → Type (max u v)) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Finite R (A i)] [∀ i, Algebra.FinitePresentation R (A i)]
    (hff : ∀ i, (algebraMap R (A i)).FaithfullyFlat) :
    ∃ (T : Type (max u v)) (_ : CommRing T) (_ : Algebra R T)
      (_ : Module.Finite R T) (_ : Algebra.FinitePresentation R T)
      (_ : (algebraMap R T).FaithfullyFlat),
        ∃ (component : (i : {i // i ∈ s}) → A i.1 →ₐ[R] T), component = component := by
  classical
  -- Inductively insert one tensor factor at a time, retaining component maps for old factors via
  -- the right tensor inclusion and using the left inclusion for the newly inserted factor.
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨ULift.{v} R, inferInstance, inferInstance, ?_, ?_, ?_, ?_, rfl⟩
      · exact (uliftBaseExtensionData (R := R)).1
      · exact (uliftBaseExtensionData (R := R)).2.1
      · exact (uliftBaseExtensionData (R := R)).2.2
      · intro i
        rcases i with ⟨i, hi⟩
        simp at hi
  | insert a s has ih =>
      obtain ⟨T, hTcomm, hTalg, hTfin, hTfp, hTff, component, _⟩ := ih
      letI : CommRing T := hTcomm
      letI : Algebra R T := hTalg
      let U : Type (max u v) := TensorProduct R (A a) T
      letI : CommRing U := inferInstance
      letI : Algebra R U := inferInstance
      have hUdata :
          Module.Finite R U ∧ Algebra.FinitePresentation R U ∧
            (algebraMap R U).FaithfullyFlat := by
        exact tensorProductTwoExtensionData (R := R) (A := A a) (B := T) (hff a) hTff
      refine ⟨U, inferInstance, inferInstance, hUdata.1, hUdata.2.1, hUdata.2.2, ?_, rfl⟩
      intro i
      rcases i with ⟨i, hi⟩
      by_cases hia : i = a
      · subst hia
        exact Algebra.TensorProduct.includeLeft
      · have his : i ∈ s := by
          rw [Finset.mem_insert] at hi
          exact hi.resolve_left hia
        exact (Algebra.TensorProduct.includeRight : T →ₐ[R] U).comp (component ⟨i, his⟩)

/- Domain-style sampling:
* primary domain: étale morphisms of commutative rings, localized standard étale neighborhoods,
  and finite flat covers with surjective spectrum map;
* sampled declarations:
  `Etale`,
  `IsEtaleAt.exists_isStandardEtale`,
  `exists_finitePresentation_flat_surjective_extension_lifting_primes`,
  `Module.Finite`,
  `Algebra.FinitePresentation`,
  `Module.Flat`;
* best owner abstraction:
  the source map is already controlled by the canonical owner `Etale R S`, and the target
  extension data should stay in the existing owner predicates `Module.Finite`, `Algebra.FinitePresentation`,
  `Module.Flat`, and the canonical spectrum-surjectivity predicate, rather than being repackaged
  into a new local class;
* source/core/bridge triage:
  this lemma is `source-facing`; the local factorization clause is the genuinely new source
  content, while the finiteness / flatness conditions are derived owner data on the chosen
  extension `S'`;
* primitive-vs-derived split:
  primitive existential data are only the extension ring `S'` and its `R`-algebra structure;
  the algebraic properties of `S'` and the spectrum-surjectivity statement belong in separate
  canonical predicates in the theorem output.
-/

-- Proof sketch: use Proposition `10.144.4` and quasi-compactness of `Spec(S)` to cover `Spec(S)`
-- by finitely many basic opens on which `R → S` becomes standard étale. Apply Lemma `10.144.5` to
-- each standard étale localization, then tensor the resulting finite flat covers over `R`. For a
-- prime of the tensor product, pick one factor lying over its image in `Spec(R)` and use the
-- corresponding localized factorization through that standard étale piece.
/-- Chap10 Lemma 10 144 6: if `R → S` is étale and `Spec(S) → Spec(R)` is surjective, then there exists a
finite, finitely presented, flat `R`-algebra `S'` whose spectrum still surjects onto `Spec(R)`
and such that for every prime `q' ⊂ S'` there is an element `g' ∉ q'` for which the localized map
`R → S'[1 / g']` factors as `R → S → S'[1 / g']`. -/
@[stacks 00UG]
theorem exists_finitePresentation_flat_surjective_localFactorization_extension
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : Module.Flat R S')
      (_ : Function.Surjective (PrimeSpectrum.comap (algebraMap R S'))),
        ∀ q' : PrimeSpectrum S',
          ∃ (g' : S') (_ : g' ∉ q'.asIdeal), Nonempty (S →ₐ[R] Localization.Away g') := by
  classical
  -- Route correction: the chart theorem from Lemma 10.144.5 is now imported, so the proof follows
  -- the source route: finite standard-étale cover, chartwise extensions, then finite tensoring.
  -- Start with the finite standard-étale away cover dictated by the source proof. The remaining
  -- construction should apply the standard-étale lifting theorem chartwise and combine the
  -- resulting finite faithfully flat algebras by a finite tensor product over `R`.
  obtain ⟨t, htstd, htspan⟩ := existsFiniteStandardEtaleAwayCover (R := R) (S := S)
  -- The finite cover already supplies, for every base prime, a concrete localized chart prime;
  -- the unresolved step is to attach compatible finite flat chart extensions to these choices.
  have hlocalizedCover :
      ∀ p : PrimeSpectrum R, ∃ f ∈ t, ∃ qf : PrimeSpectrum (Localization.Away f),
        PrimeSpectrum.comap (algebraMap R (Localization.Away f)) qf = p :=
    existsLocalizedCoverPrimeOver (R := R) (S := S) t htspan hsurj
  let ι := {f : S // f ∈ t}
  have chartExtension :
      ∀ i : ι,
        ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A)
          (_ : Module.Finite R A) (_ : Algebra.FinitePresentation R A)
          (_ : (algebraMap R A).FaithfullyFlat),
            ∀ (p : PrimeSpectrum R) (q : p.asIdeal.primesOver (Localization.Away i.1))
              (q' : p.asIdeal.primesOver A),
              ∃ (g' : A) (_ : g' ∉ q'.1) (φ : Localization.Away i.1 →ₐ[R]
                Localization.Away g'),
                Ideal.comap φ.toRingHom
                    (Ideal.map (algebraMap A (Localization.Away g')) q'.1) = q.1 := by
    intro i
    -- Each selected principal open is standard étale, so Lemma 10.144.5 supplies its finite
    -- faithfully flat splitting extension with the required primewise lifting property.
    letI : IsStandardEtale R (Localization.Away i.1) := htstd i.1 i.2
    exact exists_finitePresentation_flat_surjective_extension_lifting_primes
      (R := R) (S := Localization.Away i.1)
  choose A hAcomm hAalg hAfinite hAfp hAff hAlift using chartExtension
  letI (i : ι) : CommRing (A i) := hAcomm i
  letI (i : ι) : Algebra R (A i) := hAalg i
  letI (i : ι) : Module.Finite R (A i) := hAfinite i
  letI (i : ι) : Algebra.FinitePresentation R (A i) := hAfp i
  -- Tensor together all chart extensions; component maps remember every chart inside the final
  -- finite faithfully flat algebra.
  obtain ⟨T, hTcomm, hTalg, hTfinite, hTfp, hTff, component, _⟩ :=
    finiteTensorExtensionData (R := R) (s := (Finset.univ : Finset ι)) (A := A) hAff
  letI : CommRing T := hTcomm
  letI : Algebra R T := hTalg
  obtain ⟨hTflat, hTsurj⟩ :=
    faithfullyFlat_algebraMap_flat_and_spectrum_surjective (A := R) (B := T) hTff
  refine ⟨T, hTcomm, hTalg, hTfinite, hTfp, hTflat, hTsurj, ?_⟩
  intro qT
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R T) qT
  -- Choose a chart meeting the image of `qT` in `Spec R`, then pull `qT` back to that chart's
  -- tensor component and apply the chartwise prime-lifting theorem.
  obtain ⟨f, hft, qf, hqf⟩ := hlocalizedCover p
  let i : ι := ⟨f, hft⟩
  have hiuniv : i ∈ (Finset.univ : Finset ι) := by
    simp
  let comp_i : A i →ₐ[R] T := component ⟨i, hiuniv⟩
  let qA : PrimeSpectrum (A i) := PrimeSpectrum.comap comp_i.toRingHom qT
  have hqA_base :
      PrimeSpectrum.comap (algebraMap R (A i)) qA = p := by
    exact componentPrime_comap_eq_base (R := R) comp_i qT
  let qChart : p.asIdeal.primesOver (Localization.Away i.1) :=
    ⟨qf.asIdeal, primeIdeal_mem_primesOver_of_comap_eq (R := R) p qf hqf⟩
  let qComponent : p.asIdeal.primesOver (A i) :=
    ⟨qA.asIdeal, primeIdeal_mem_primesOver_of_comap_eq (R := R) p qA hqA_base⟩
  obtain ⟨g, hg, φ, _hφ_comap⟩ := hAlift i p qChart qComponent
  have hS_to_chartAway : Nonempty (S →ₐ[R] Localization.Away g) := by
    -- Compose the chart factorization with the canonical localization map out of `S`.
    exact ⟨φ.comp (IsScalarTower.toAlgHom R S (Localization.Away i.1))⟩
  -- Finally push the chart denominator through the component map into the tensor algebra.
  obtain ⟨gT, hgT, hnonempty⟩ :=
    localFactorization_pushAway (R := R) (A := A i) (B := T) (T := S)
      comp_i qT (g := g) hg hS_to_chartAway
  exact ⟨gT, hgT, hnonempty⟩

end

end Algebra
