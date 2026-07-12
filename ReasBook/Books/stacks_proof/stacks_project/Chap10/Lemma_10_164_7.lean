import Mathlib
import StacksProject_2024.Chap10.Lemma_10_140_3
import StacksProject_2024.Chap10.Lemma_10_162_2
import StacksProject_2024.Chap10.Lemma_10_163_6
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap10.Lemma_10_164_1
import StacksProject_2024.Chap10.Proposition_10_162_15_Nagata

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Helper for Chap10 Lemma 10 164 7: a smooth algebra map which is surjective on spectra is
faithfully flat. -/
private theorem faithfullyFlat_algebraMap_of_smooth_specComap_surjective [Algebra.Smooth R S]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) :
    (algebraMap R S).FaithfullyFlat := by
  -- Smoothness gives flatness, and the spectrum-surjectivity hypothesis supplies the second
  -- component in the standard faithfully-flat characterization.
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  constructor
  · exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · exact hsurj

/-- Helper for Chap10 Lemma 10 164 7: a finite extension of the fraction field is essentially
finite type over the source domain. -/
private theorem fractionFieldFiniteExtension_essFiniteType
    {A : Type u} {L : Type w} [CommRing A] [IsDomain A] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] :
    Algebra.EssFiniteType A L := by
  -- The extension factors through the localization `A → FractionRing A`, then through a finite
  -- field extension, and essential finite type is transitive.
  letI : Algebra.EssFiniteType A (FractionRing A) :=
    Algebra.EssFiniteType.of_isLocalization (S := FractionRing A) (nonZeroDivisors A)
  letI : Module.Finite (FractionRing A) L := inferInstance
  letI : Algebra.FiniteType (FractionRing A) L := Module.Finite.finiteType L
  letI : Algebra.EssFiniteType (FractionRing A) L :=
    Algebra.EssFiniteType.of_finiteType (FractionRing A) L
  exact Algebra.EssFiniteType.comp A (FractionRing A) L

/-- Helper for Chap10 Lemma 10 164 7: maximal localizations of a smooth algebra over a field are
smooth points. -/
private theorem isSmoothAt_of_smooth_at_prime
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]
    (m : Ideal A) [m.IsPrime] :
    Algebra.IsSmoothAt k m := by
  -- Global smoothness identifies the smooth locus with all of `Spec A`, so this prime is smooth.
  have hmem : (⟨m, inferInstance⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus k A := by
    rw [Algebra.smoothLocus_eq_univ (R := k) (A := A)]
    simp
  simpa [Algebra.smoothLocus] using hmem

/-- Helper for Chap10 Lemma 10 164 7: a domain structure on a prime localization gives
reducedness of that localization. -/
private theorem isReduced_localizationAtPrime_of_isDomain
    {A : Type v} [CommRing A] (p : Ideal A) [p.IsPrime]
    [IsDomain (Localization.AtPrime p)] :
    IsReduced (Localization.AtPrime p) := by
  -- Domains have no zero divisors, so the standard reducedness instance applies directly.
  exact isReduced_of_noZeroDivisors

/-- Helper for Chap10 Lemma 10 164 7: an étale algebra over a reduced Noetherian ring is
reduced. -/
private theorem isReduced_of_etale_over_reduced_noetherian
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsReduced A] [Algebra.Etale A B] :
    IsReduced B := by
  -- Étale algebras are flat and finitely presented, so reducedness ascends from the base once all
  -- residue-field fibers are reduced.
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  exact isReduced_of_flat_of_fiber (R := A) (S := B) fun p ↦ by
    -- The fiber of an étale map is formally unramified and essentially finite type over a field,
    -- hence reduced by the field-level unramified theorem.
    exact Algebra.FormallyUnramified.isReduced_of_field p.asIdeal.ResidueField (p.asIdeal.Fiber B)

/-- Helper for Chap10 Lemma 10 164 7: a standard-smooth algebra over a field is reduced. -/
private theorem isReduced_of_standardSmooth_over_field
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmooth k A] :
    IsReduced A := by
  -- A standard-smooth algebra factors as an étale algebra over a polynomial ring; the polynomial
  -- ring over a field is reduced and Noetherian.
  have hstd : (algebraMap k A).IsStandardSmooth :=
    (RingHom.isStandardSmooth_algebraMap).2 inferInstance
  obtain ⟨n, g, -, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hstd
  letI : Algebra (MvPolynomial (Fin n) k) A := g.toAlgebra
  letI : Algebra.Etale (MvPolynomial (Fin n) k) A := RingHom.Etale.toAlgebra hg
  exact isReduced_of_etale_over_reduced_noetherian (A := MvPolynomial (Fin n) k) (B := A)

/-- Helper for Chap10 Lemma 10 164 7: if a principal localization is reduced, then every prime
localization whose prime avoids that element is reduced. -/
private theorem isReduced_atPrime_of_isReduced_away_notMem
    {A : Type v} [CommRing A] {t : A} (m : Ideal A) [m.IsPrime]
    (ht : t ∉ m) [IsReduced (Localization.Away t)] :
    IsReduced (Localization.AtPrime m) := by
  -- Map the prime to `A[1/t]`; disjointness of the powers of `t` identifies the resulting
  -- localization with `A_m`.
  let q : Ideal (Localization.Away t) := Ideal.map (algebraMap A (Localization.Away t)) m
  have hprime : m.IsPrime := inferInstance
  have hdisj : Disjoint (Submonoid.powers t : Set A) (m : Set A) := by
    exact (Ideal.disjoint_powers_iff_notMem (I := m) t (Ideal.IsPrime.isRadical hprime)).2 ht
  have hqPrime : q.IsPrime := by
    exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) (Localization.Away t)
      m hprime hdisj
  letI : q.IsPrime := hqPrime
  have hcomap : Ideal.comap (algebraMap A (Localization.Away t)) q = m := by
    exact IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers t) (Localization.Away t)
      hprime hdisj
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) m := by
    simpa [hcomap] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := Submonoid.powers t) (T := Localization.AtPrime q) q)
  let e : Localization.AtPrime m ≃ₐ[A] Localization.AtPrime q :=
    IsLocalization.algEquiv m.primeCompl (Localization.AtPrime m) (Localization.AtPrime q)
  exact isReduced_of_injective e.toRingHom e.injective

/-- Helper for Chap10 Lemma 10 164 7: maximal localizations of a smooth algebra over a field are
reduced. -/
private theorem isReduced_localizationAtMaximal_of_smooth_over_field
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]
    (m : Ideal A) [m.IsMaximal] :
    IsReduced (Localization.AtPrime m) := by
  -- Route correction: avoid the unavailable regular-local-domain import by using the standard
  -- smooth cover supplied by smoothness and localizing a reduced principal-open chart at `m`.
  obtain ⟨s, hs_top, hs_std⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth k A
  by_contra hnotReduced
  have hall : ∀ x ∈ s, x ∈ m := by
    intro x hx
    by_contra hxnot
    have hred_m : IsReduced (Localization.AtPrime m) := by
      letI : Algebra.IsStandardSmooth k (Localization.Away x) := hs_std x hx
      letI : IsReduced (Localization.Away x) :=
        isReduced_of_standardSmooth_over_field (k := k) (A := Localization.Away x)
      exact isReduced_atPrime_of_isReduced_away_notMem (A := A) (t := x) m hxnot
    exact hnotReduced hred_m
  have hle : Ideal.span s ≤ m := Ideal.span_le.mpr hall
  have htop_le : (⊤ : Ideal A) ≤ m := by
    simpa [hs_top] using hle
  exact (Ideal.IsMaximal.ne_top (show m.IsMaximal from inferInstance)) (eq_top_iff.2 htop_le)

/-- Helper for Chap10 Lemma 10 164 7: a smooth algebra over a field is reduced. -/
private theorem isReduced_of_smooth_over_field
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] :
    IsReduced A := by
  -- Reducedness is local at maximal ideals, where the previous helper supplies reduced
  -- localizations from smoothness over the field.
  refine isReduced_ofLocalizationMaximal A fun m _ ↦ ?_
  simpa using isReduced_localizationAtMaximal_of_smooth_over_field (k := k) (A := A) m

/-- Helper for Chap10 Lemma 10 164 7: smooth base change to a field is reduced. -/
private theorem tensorProduct_finiteFractionExtension_isReduced_of_smooth
    {A : Type u} {B : Type v} {L : Type w} [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    [Field L] [Algebra A L] :
    IsReduced (B ⊗[A] L) := by
  -- Commute the tensor factors so the algebra is visibly smooth over the field `L`, then
  -- transfer reducedness back across the tensor commutor.
  letI : Algebra.Smooth L (L ⊗[A] B) := inferInstance
  have hred : IsReduced (L ⊗[A] B) :=
    isReduced_of_smooth_over_field (k := L) (A := L ⊗[A] B)
  letI : IsReduced (L ⊗[A] B) := hred
  let e : B ⊗[A] L ≃ₐ[A] L ⊗[A] B := Algebra.TensorProduct.comm A B L
  exact isReduced_of_injective e.toRingHom e.injective

/-- Helper for Chap10 Lemma 10 164 7: after base change to the target algebra, a finite
fraction-field extension remains essentially finite type. -/
private theorem tensorProduct_finiteFractionExtension_essFiniteType
    {A : Type u} {B : Type v} {L : Type w} [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] :
    Algebra.EssFiniteType B (B ⊗[A] L) := by
  -- First view `L` as essentially finite type over `A`, then apply the canonical base-change API.
  letI : Algebra.EssFiniteType A L :=
    fractionFieldFiniteExtension_essFiniteType (A := A) (L := L)
  exact Algebra.EssFiniteType.baseChange A L B

/-- Helper for Chap10 Lemma 10 164 7: the smooth integral-closure comparison transports
finiteness from the target normalization back to the tensor product of the source normalization. -/
private theorem moduleFinite_tensorProduct_integralClosure_of_moduleFinite_target
    {A : Type u} {B : Type v} {L : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] [CommRing L] [Algebra A L]
    (hfiniteTarget : Module.Finite B (integralClosure B (B ⊗[A] L))) :
    Module.Finite B (B ⊗[A] integralClosure A L) := by
  -- The smooth comparison map is bijective, so it upgrades to an algebra equivalence.
  let e : B ⊗[A] integralClosure A L ≃ₐ[B] integralClosure B (B ⊗[A] L) :=
    AlgEquiv.ofBijective (TensorProduct.toIntegralClosure A B L)
      (TensorProduct.toIntegralClosure_bijective_of_smooth (R := A) (S := B) (B := L))
  letI : Module.Finite B (integralClosure B (B ⊗[A] L)) := hfiniteTarget
  -- Transport finite generation across the inverse linear equivalence.
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- Helper for Chap10 Lemma 10 164 7: after smooth base change to a Nagata target, the tensor
product with the source integral closure is finite over the target. -/
private theorem moduleFinite_tensorProduct_integralClosure_of_smooth_nagata
    {A : Type u} {B : Type v} {L : Type w} [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Algebra.Smooth A B] [NagataRing B]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L] :
    Module.Finite B (B ⊗[A] integralClosure A L) := by
  -- The tensor algebra has the two side conditions needed for the canonical finite-normalization
  -- theorem: essential finite type over the Nagata target and reducedness from smoothness.
  letI : Algebra.EssFiniteType B (B ⊗[A] L) :=
    tensorProduct_finiteFractionExtension_essFiniteType (A := A) (B := B) (L := L)
  letI : IsReduced (B ⊗[A] L) :=
    tensorProduct_finiteFractionExtension_isReduced_of_smooth (A := A) (B := B) (L := L)
  have hfiniteTarget : Module.Finite B (integralClosure B (B ⊗[A] L)) := by
    -- Apply the canonical Nagata finite-normalization theorem to the reduced essentially
    -- finite-type `B`-algebra `B ⊗[A] L`.
    exact integralClosure_finite_of_nagataRing_of_essFiniteType_of_isReduced
      (R := B) (S := B ⊗[A] L)
  -- Transport the finite target normalization through the smooth integral-closure comparison.
  exact moduleFinite_tensorProduct_integralClosure_of_moduleFinite_target hfiniteTarget

/-- Helper for Chap10 Lemma 10 164 7: the `N-2` property descends from a Nagata target along a
smooth faithfully flat map whose source is a domain. -/
private theorem isN2Ring_of_smooth_faithfullyFlat_nagata
    {A : Type u} {B : Type w} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (hff : (algebraMap A B).FaithfullyFlat) [NagataRing B] :
    IsN2Ring A := by
  -- Route correction: the faithfully-flat-only descent statement lost the smooth comparison map;
  -- keeping smoothness lets us prove finite normalization after base change and then descend it.
  letI : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  refine ⟨?_⟩
  intro L _ _ _ _ _
  -- First prove finiteness after tensoring with the faithfully flat target.
  letI : Module.Finite B (B ⊗[A] integralClosure A L) :=
    moduleFinite_tensorProduct_integralClosure_of_smooth_nagata (B := B)
  -- Then descend finite generation of the integral closure from the tensor product.
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

/-- Helper for Chap10 Lemma 10 164 7: the universally Japanese condition descends along a
smooth faithfully flat algebra map from a Nagata target. -/
private theorem universallyJapaneseRing_of_smooth_faithfullyFlat_of_nagata [Algebra.Smooth R S]
    (hff : (algebraMap R S).FaithfullyFlat) [NagataRing S] :
    UniversallyJapaneseRing.{u, u} R := by
  -- Test the universally Japanese condition on a finite type domain `A` over `R`.
  letI : Module.FaithfullyFlat R S := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  refine ⟨fun {A} [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [IsDomain A] ↦ ?_⟩
  -- Base change the faithfully-flat and smooth map to `A`; the tensor target is finite type over
  -- the Nagata ring `S`, hence Nagata by the chapter TFAE.
  have hffA : (algebraMap A (TensorProduct R A S)).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  have hNagataCommT : NagataRing (TensorProduct R A S) := by
    letI : Algebra S (TensorProduct R A S) := Algebra.TensorProduct.rightAlgebra
    have hfinite : Algebra.FiniteType S (TensorProduct R A S) :=
      Algebra.FiniteType.equiv
        (show Algebra.FiniteType S (TensorProduct R S A) from inferInstance)
        (Algebra.TensorProduct.commRight R S A)
    letI : Algebra.FiniteType S (TensorProduct R A S) := hfinite
    have htfae :
        List.TFAE
          [ NagataRing S,
            ∀ (B : Type (max u v)) [CommRing B] [Algebra S B] [Algebra.FiniteType S B],
              NagataRing B,
            UniversallyJapaneseRing.{v, max u v} S ∧ IsNoetherianRing S ] :=
      nagataRing_tfae_finiteType_algebra_nagata_universallyJapanese_noetherian
    have hstable :
        ∀ (B : Type (max u v)) [CommRing B] [Algebra S B] [Algebra.FiniteType S B],
          NagataRing B :=
      (htfae.out 0 1).1 (show NagataRing S from inferInstance)
    exact hstable (TensorProduct R A S)
  letI : NagataRing (TensorProduct R A S) := hNagataCommT
  exact isN2Ring_of_smooth_faithfullyFlat_nagata hffA

/-- Helper for Chap10 Lemma 10 164 7: a Nagata target descends the Nagata condition along a
smooth faithfully flat algebra map. -/
private theorem nagataRing_of_smooth_faithfullyFlat_of_nagata [Algebra.Smooth R S]
    (hff : (algebraMap R S).FaithfullyFlat) [NagataRing S] :
    NagataRing R := by
  -- The chapter bridge reduces Nagata descent to the universally Japanese part and Noetherian
  -- descent; the latter is Lemma 10.164.1.
  have hUJ : UniversallyJapaneseRing.{u, u} R :=
    universallyJapaneseRing_of_smooth_faithfullyFlat_of_nagata hff
  have hNoetherian : IsNoetherianRing R :=
    isNoetherianRing_of_faithfullyFlat (algebraMap R S) hff
  rw [nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing]
  constructor
  · exact hUJ
  · exact hNoetherian

/-
Domain-style sampling:
* primary domain: smooth descent of the source-facing owner `NagataRing` in commutative algebra;
* sampled owner declarations:
  `NagataRing`,
  `UniversallyJapaneseRing`,
  `nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing`,
  `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`;
* best owner abstraction: the public conclusion should stay on the source-facing owner
  `NagataRing`, while the map-side hypothesis is canonically organized through
  `RingHom.FaithfullyFlat`, derived here from smoothness plus surjectivity on spectra;
* primitive data vs. derived API: the primitive inputs are `[Algebra.Smooth R S]`, the spectrum
  surjectivity hypothesis, and `[NagataRing S]`; faithful flatness of `algebraMap R S`,
  Noetherianity descent, and the companion owner view `UniversallyJapaneseRing` are derived API.

Source/core/bridge triage:
* `source-facing`: the smooth-descent theorem for `NagataRing`;
* `core/canonical`: `NagataRing`, `UniversallyJapaneseRing`, and `RingHom.FaithfullyFlat`;
* `bridge/view`: `nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing` together with
  `isNoetherianRing_of_faithfullyFlat`.
-/
-- Proof sketch: smooth algebras are flat, so the surjectivity hypothesis on
-- `PrimeSpectrum.comap (algebraMap R S)` upgrades `R → S` to a faithfully flat morphism via
-- `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`. Lemma `10.164.1` then descends
-- Noetherianity from `S` to `R`, while the chapter bridge
-- `nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing` reduces the remaining work to the
-- universally Japanese part. Since `NagataRing S` already supplies `UniversallyJapaneseRing S`,
-- the source-facing theorem can be assembled through that canonical owner decomposition rather
-- than by rebuilding the `NagataRing` fields directly.
/-- Chap10 Lemma 10 164 7: if `R → S` is smooth and surjective on spectra, and `S` is a
Nagata ring, then `R` is a Nagata ring. -/
@[stacks 0354]
theorem nagataRing_of_smooth_of_specComap_surjective [Algebra.Smooth R S]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) [NagataRing S] :
    NagataRing R := by
  -- The smooth/spectrum hypotheses first produce faithful flatness; the descent package then
  -- transfers the Nagata owner from `S` to `R`.
  have hff : (algebraMap R S).FaithfullyFlat :=
    faithfullyFlat_algebraMap_of_smooth_specComap_surjective hsurj
  exact nagataRing_of_smooth_faithfullyFlat_of_nagata hff

end
