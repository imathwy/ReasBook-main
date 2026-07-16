import stacks_proof.stacks_project.Chap10.Definition_10_54_1
import stacks_proof.stacks_project.Chap10.Definition_10_135_1
import stacks_proof.stacks_project.Chap10.Definition_10_135_5
import stacks_proof.stacks_project.Chap10.Lemma_10_126_7
import stacks_proof.stacks_project.Chap10.Lemma_10_135_2
import stacks_proof.stacks_project.Chap10.Lemma_10_135_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open AlgebraicGeometry
open Algebra

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-- Helper for Chap10 Lemma 10 135 9: some principal open around `q` is a global complete
intersection over `k`. -/
private abbrev isGlobalCompleteIntersectionNearPrime
    (K : Type u) [Field K] {A : Type v} [CommRing A] [Algebra K A] (q : PrimeSpectrum A) : Prop :=
  ∃ g : A, g ∉ q.asIdeal ∧ IsGlobalCompleteIntersection K (Localization.Away g)

/-- Helper for Chap10 Lemma 10 135 9: some principal open around `q` is a local complete
intersection over `k`. -/
private abbrev isLocalCompleteIntersectionNearPrime
    (K : Type u) [Field K] {A : Type v} [CommRing A] [Algebra K A] (q : PrimeSpectrum A) : Prop :=
  ∃ g : A, g ∉ q.asIdeal ∧ IsLocalCompleteIntersection K (Localization.Away g)

/-- Helper for Chap10 Lemma 10 135 9: a three-term implication cycle yields a `TFAE`. -/
private theorem tfae_three_of_cycle {A B C : Prop}
    (hAB : A → B) (hBC : B → C) (hCA : C → A) :
    List.TFAE [A, B, C] := by
  -- Proof comment: after unfolding `TFAE`, every pair among the three clauses is connected by
  -- the directed cycle `A -> B -> C -> A`.
  rw [List.TFAE]
  intro x hx y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  tauto

/-- Helper for Chap10 Lemma 10 135 9: local complete intersections are invariant under
`k`-algebra equivalence. -/
private theorem isLocalCompleteIntersection_of_algEquiv
    {A : Type v} {B : Type v} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (hA : IsLocalCompleteIntersection k A) (e : A ≃ₐ[k] B) :
    IsLocalCompleteIntersection k B := by
  classical
  rcases hA.exists_basicOpen_cover with ⟨s, hs, hglobal⟩
  refine ⟨s.image e, ?_, ?_⟩
  · -- Proof comment: transport the unit-ideal condition along the algebra equivalence.
    calc
      Ideal.span ((s.image e : Finset B) : Set B)
          = Ideal.map (e : A →+* B) (Ideal.span (s : Set A)) := by
              simp [Finset.coe_image, Ideal.map_span]
      _ = Ideal.map (e : A →+* B) ⊤ := by rw [hs]
      _ = ⊤ := Ideal.map_top _
  · intro b hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    -- Proof comment: the corresponding localized charts are equivalent via the induced
    -- equivalence of away localizations.
    exact IsGlobalCompleteIntersection.of_algEquiv (hglobal a ha) <|
      IsLocalization.algEquivOfAlgEquiv
        (Localization.Away a)
        (Localization.Away (e a))
        e
        (Submonoid.map_powers e a)

/-- Helper for Chap10 Lemma 10 135 9: localizing an away-localization at a prime lying over `q`
recovers the original stalk at `q`. -/
private noncomputable def localizationAtPrime_away_comapAlgEquiv
    {A : Type v} [CommRing A] [Algebra k A]
    (q : PrimeSpectrum A) {g : A} (_hg : g ∉ q.asIdeal)
    (qg : PrimeSpectrum (Localization.Away g))
    (hqg : PrimeSpectrum.comap (algebraMap A (Localization.Away g)) qg = q) :
    Localization.AtPrime q.asIdeal ≃ₐ[k] Localization.AtPrime qg.asIdeal := by
  have hqgIdeal :
      Ideal.comap (algebraMap A (Localization.Away g)) qg.asIdeal = q.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqg
  letI : IsLocalization.AtPrime (Localization.AtPrime qg.asIdeal) q.asIdeal := by
    simpa [hqgIdeal] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Submonoid.powers g)
        (Localization.AtPrime qg.asIdeal)
        qg.asIdeal)
  exact
    (IsLocalization.algEquiv
      q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime qg.asIdeal)).restrictScalars k

/-- Helper for Chap10 Lemma 10 135 9: a maximal complete-intersection stalk spreads to a
principal-open global complete-intersection neighborhood by transporting the global model from
`isCompleteIntersectionOver_tfae` across an away-equivalence. -/
private lemma exists_globalCompleteIntersectionModel_of_completeIntersectionOver
    (m : MaximalSpectrum S)
    (hm : IsCompleteIntersectionOver k (Localization.AtPrime m.asIdeal)) :
    ∃ (A : Type v) (_ : CommRing A) (_ : Algebra k A) (a : PrimeSpectrum A)
        (_ : Localization.AtPrime m.asIdeal ≃ₐ[k] Localization.AtPrime a.asIdeal),
        IsGlobalCompleteIntersection k A := by
  letI : IsLocalRing (Localization.AtPrime m.asIdeal) := inferInstance
  letI : Algebra.EssFiniteType k (Localization.AtPrime m.asIdeal) := inferInstance
  have hTFAE :=
    @isCompleteIntersectionOver_tfae k _ (Localization.AtPrime m.asIdeal) _ _ _ _
  -- Proof comment: on the local ring `S_m`, Lemma `10.135.7` already packages the desired
  -- global complete-intersection model as one clause of its `TFAE`.
  exact (hTFAE.out 0 3 rfl rfl).mp hm

/-- Helper for Chap10 Lemma 10 135 9: a prime avoiding an away parameter lifts to the
corresponding away localization. -/
private lemma exists_primeSpectrum_away_comap_eq_of_notMem
    (q : PrimeSpectrum S) {g : S} (hg : g ∉ q.asIdeal) :
    ∃ qg : PrimeSpectrum (Localization.Away g),
      PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg = q := by
  -- Proof comment: the image of `Spec(S_g)` is exactly the basic open `D(g)`, so `q` lifts
  -- precisely because `g` avoids the chosen prime.
  have hq_range : q ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    simpa [PrimeSpectrum.mem_basicOpen] using hg
  exact Set.mem_range.mp hq_range

/-- Helper for Chap10 Lemma 10 135 9: a finite set spanning the unit ideal contains an element
outside any chosen prime ideal. -/
private lemma exists_notMem_of_span_eq_top_of_prime
    {A : Type*} [CommRing A] (s : Finset A) {p : Ideal A} [p.IsPrime]
    (hs : Ideal.span (s : Set A) = ⊤) :
    ∃ a ∈ s, a ∉ p := by
  -- Proof comment: if every generator lay in the prime, the generated ideal would also lie in
  -- the prime, forcing the prime ideal to be all of `A`.
  by_contra h
  push Not at h
  have hspan_le : Ideal.span (s : Set A) ≤ p := Ideal.span_le.mpr fun x hx ↦ h x hx
  have htop_le : (⊤ : Ideal A) ≤ p := by
    rw [← hs]
    exact hspan_le
  have hone : (1 : A) ∈ p := htop_le trivial
  have htop : p = ⊤ := (Ideal.eq_top_iff_one p).mpr hone
  exact (Ideal.IsPrime.ne_top (show p.IsPrime from inferInstance)) htop

/-- Helper for Chap10 Lemma 10 135 9: an iterated away localization of `S_g` is a single away
localization of `S`. -/
private lemma single_original_awayAlgEquiv
    (g : S) (u : Localization.Away g) :
    let h : S := g * (IsLocalization.Away.sec g u).1
    Nonempty (Localization.Away u ≃ₐ[k] Localization.Away h) := by
  -- Proof comment: replace the iterated denominator by the numerator of a chosen section and then
  -- use the standard product formula for consecutive away localizations.
  let a : S := (IsLocalization.Away.sec g u).1
  let h : S := g * a
  let hassoc :
      Associated (algebraMap S (Localization.Away g) a) u :=
    IsLocalization.Away.associated_sec_fst g u
  letI :
      IsLocalization.Away u (Localization.Away (algebraMap S (Localization.Away g) a)) :=
    IsLocalization.Away.of_associated hassoc
  let eIter :
      Localization.Away u ≃ₐ[k] Localization.Away (algebraMap S (Localization.Away g) a) :=
    (Localization.algEquiv
      (Submonoid.powers u)
      (Localization.Away (algebraMap S (Localization.Away g) a))).restrictScalars k
  letI :
      IsLocalization.Away h (Localization.Away (algebraMap S (Localization.Away g) a)) := by
    simpa [h] using
      (inferInstance :
        IsLocalization.Away h (Localization.Away (algebraMap S (Localization.Away g) a)))
  let eSingle :
      Localization.Away (algebraMap S (Localization.Away g) a) ≃ₐ[k] Localization.Away h :=
    (Localization.algEquiv
      (Submonoid.powers h)
      (Localization.Away (algebraMap S (Localization.Away g) a))).symm.restrictScalars k
  exact ⟨eIter.trans eSingle⟩

/-- Helper for Chap10 Lemma 10 135 9: if an element of an away localization avoids a lifted
prime, then the cleared original denominator still avoids the original prime. -/
private lemma notMem_original_away_of_iterated_away
    (q : PrimeSpectrum S) {g : S} (hg : g ∉ q.asIdeal)
    {u : Localization.Away g} (qg : PrimeSpectrum (Localization.Away g))
    (hqg : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg = q)
    (hu : u ∉ qg.asIdeal) :
    g * (IsLocalization.Away.sec g u).1 ∉ q.asIdeal := by
  -- Proof comment: if the cleared numerator lay in the original prime, then its image would lie
  -- in the lifted prime and the associatedness relation would force `u` into that prime as well.
  have hsec_not_mem_away :
      algebraMap S (Localization.Away g) (IsLocalization.Away.sec g u).1 ∉ qg.asIdeal := by
    intro hsec_mem
    have hu_mem : u ∈ qg.asIdeal := by
      exact (Ideal.mem_iff_of_associated
        (IsLocalization.Away.associated_sec_fst g u)).mp hsec_mem
    exact hu hu_mem
  have hsec_not_mem :
      (IsLocalization.Away.sec g u).1 ∉ q.asIdeal := by
    intro hsec_mem
    have hqgIdeal :
        Ideal.comap (algebraMap S (Localization.Away g)) qg.asIdeal = q.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqg
    have hmap_mem :
        algebraMap S (Localization.Away g) (IsLocalization.Away.sec g u).1 ∈ qg.asIdeal := by
      have :
          (IsLocalization.Away.sec g u).1 ∈
            Ideal.comap (algebraMap S (Localization.Away g)) qg.asIdeal := by
        rw [hqgIdeal]
        exact hsec_mem
      simpa [Ideal.mem_comap] using this
    exact hsec_not_mem_away hmap_mem
  -- Proof comment: both factors avoid the original prime, so their product does as well.
  exact q.2.mul_notMem hg hsec_not_mem

/-- Helper for Chap10 Lemma 10 135 9: the unit localization `Localization.Away (1 : S)` inherits
finite type over `k` from `S`. -/
private lemma finiteTypeAwayOne_of_finiteType
    [Algebra.FiniteType k S] :
    Algebra.FiniteType k (Localization.Away (1 : S)) := by
  let eOne : S ≃ₐ[k] Localization.Away (1 : S) :=
    (IsLocalization.atOne S (Localization.Away (1 : S))).restrictScalars k
  -- Proof comment: localizing away from `1` does not change the underlying `k`-algebra, so the
  -- ambient finite-type structure transports across the canonical equivalence.
  exact Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType k S) eOne

/-- Helper for Chap10 Lemma 10 135 9: finite presentation of the maximal stalk spreads to one
principal-open neighborhood of the maximal ideal after first extracting a finite-type chart. -/
private lemma exists_finiteTypeAway_of_finitePresentation_atMaximal
    [Algebra.FiniteType k S]
    (m : MaximalSpectrum S)
    (hm : Algebra.FinitePresentation k (Localization.AtPrime m.asIdeal)) :
    ∃ g : S, g ∉ m.asIdeal ∧ Algebra.FiniteType k (Localization.Away g) := by
  let _ := hm
  -- Route correction: this helper only asks for a finite-type principal-open chart of `S`, so the
  -- unit basic open `D(1)` already works under the ambient finite-type hypothesis.
  refine ⟨1, ?_, ?_⟩
  · -- Proof comment: a maximal ideal is proper, so it cannot contain the unit.
    simpa [Ideal.eq_top_iff_one] using m.2.ne_top
  · -- Proof comment: the witness `g = 1` reduces the chart to the explicit away-at-one adapter.
    exact finiteTypeAwayOne_of_finiteType

/-- Helper for Chap10 Lemma 10 135 9: finite presentation of the maximal stalk spreads to one
principal-open neighborhood of the maximal ideal. -/
private lemma exists_finitePresentationAway_of_finitePresentation_atMaximal
    [Algebra.FiniteType k S]
    (m : MaximalSpectrum S)
    (hm : Algebra.FinitePresentation k (Localization.AtPrime m.asIdeal)) :
    ∃ g : S, g ∉ m.asIdeal ∧ Algebra.FinitePresentation k (Localization.Away g) := by
  obtain ⟨g, hg, hft⟩ := exists_finiteTypeAway_of_finitePresentation_atMaximal m hm
  -- Proof comment: over the Noetherian base field `k`, finite type already upgrades to finite
  -- presentation on the extracted principal-open chart.
  exact ⟨g, hg, (Algebra.FinitePresentation.of_finiteType).mp hft⟩

/-- Helper for Chap10 Lemma 10 135 9: a maximal complete-intersection stalk admits a principal-open
source chart which is finitely presented over `k`. -/
private lemma exists_finitePresentationAway_nearMaximal_of_completeIntersectionOver
    [Algebra.FiniteType k S]
    (m : MaximalSpectrum S)
    (_hm : IsCompleteIntersectionOver k (Localization.AtPrime m.asIdeal)) :
    ∃ g : S, g ∉ m.asIdeal ∧ Algebra.FinitePresentation k (Localization.Away g) := by
  -- Proof comment: over the Noetherian base field `k`, the unit basic open already gives a
  -- finitely presented chart because `S` is finite type over `k`.
  refine ⟨1, ?_, ?_⟩
  · simpa [Ideal.eq_top_iff_one] using m.2.ne_top
  · have hfpS : Algebra.FinitePresentation k S :=
      (Algebra.FinitePresentation.of_finiteType).mp inferInstance
    let eOne : S ≃ₐ[k] Localization.Away (1 : S) :=
      (IsLocalization.atOne S (Localization.Away (1 : S))).restrictScalars k
    letI : Algebra.FinitePresentation k S := hfpS
    exact Algebra.FinitePresentation.equiv eOne

/-- Helper for Chap10 Lemma 10 135 9: over a finite-type `k`-algebra, a complete-intersection
stalk at `q` yields a principal-open local complete-intersection neighborhood of `q`. -/
private lemma localNearPrime_of_completeIntersectionOver_atPrime
    [Algebra.FiniteType k S] (q : PrimeSpectrum S)
    (hq : IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal)) :
    isLocalCompleteIntersectionNearPrime k q := by
  letI : IsLocalRing (Localization.AtPrime q.asIdeal) := inferInstance
  letI : Algebra.EssFiniteType k (Localization.AtPrime q.asIdeal) := inferInstance
  have hTFAE :=
    @isCompleteIntersectionOver_tfae k _ (Localization.AtPrime q.asIdeal) _ _ _ _
  rcases (hTFAE.out 0 4 rfl rfl).mp hq with ⟨A, hAComm, hAAlg, a, e, hlocalA⟩
  letI : CommRing A := hAComm
  letI : Algebra k A := hAAlg
  classical
  rcases hlocalA.exists_basicOpen_cover with ⟨s, hs, hglobal⟩
  obtain ⟨u, hus, hu⟩ :
      ∃ u ∈ s, u ∉ a.asIdeal := exists_notMem_of_span_eq_top_of_prime s hs
  have hglobalAu : IsGlobalCompleteIntersection k (Localization.Away u) := hglobal u hus
  obtain ⟨au, hau⟩ := exists_primeSpectrum_away_comap_eq_of_notMem a hu
  let eA :
      Localization.AtPrime a.asIdeal ≃ₐ[k] Localization.AtPrime au.asIdeal :=
    localizationAtPrime_away_comapAlgEquiv a hu au hau
  letI : IsGlobalCompleteIntersection k (Localization.Away u) := hglobalAu
  letI : Algebra.FinitePresentation k (Localization.Away u) := inferInstance
  letI : Algebra.FinitePresentation k S :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  obtain ⟨g, gAway, heAway⟩ :=
    exists_awayAlgEquiv_of_localizationAtPrime_algEquiv q au (e.trans eA)
  rcases heAway with ⟨eAway⟩
  let SgAway : Type v := Localization.Away gAway.1
  letI : CommRing SgAway := inferInstance
  letI : Algebra (Localization.Away u) SgAway := inferInstance
  letI : Algebra k SgAway := inferInstance
  letI : IsScalarTower k (Localization.Away u) SgAway := inferInstance
  letI : IsLocalization.Away gAway.1 SgAway := inferInstance
  have hglobalAway : IsGlobalCompleteIntersection k SgAway :=
    IsGlobalCompleteIntersection.of_isLocalizationAway gAway.1 hglobalAu
  letI : IsGlobalCompleteIntersection k (Localization.Away g.1) :=
    IsGlobalCompleteIntersection.of_algEquiv hglobalAway eAway.symm
  exact ⟨g.1, g.2, inferInstance⟩

/-- Helper for Chap10 Lemma 10 135 9: once a maximal stalk is compared with the lifted prime of a
finitely presented principal-open chart, the complete-intersection condition transfers to that
lifted prime. -/
private lemma completeIntersectionOver_atLiftedPrime_of_completeIntersectionOver_maximal
    (m : MaximalSpectrum S) {g : S} (_hg : g ∉ m.asIdeal)
    (qg : PrimeSpectrum (Localization.Away g))
    (hqg : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg = m.toPrimeSpectrum)
    (hm : IsCompleteIntersectionOver k (Localization.AtPrime m.asIdeal)) :
    IsCompleteIntersectionOver k (Localization.AtPrime qg.asIdeal) := by
  letI : IsCompleteIntersectionOver k (Localization.AtPrime m.asIdeal) := hm
  have hqgIdeal :
      Ideal.comap (algebraMap S (Localization.Away g)) qg.asIdeal = m.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqg
  letI : IsLocalization.AtPrime (Localization.AtPrime qg.asIdeal) m.asIdeal := by
    simpa [hqgIdeal] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Submonoid.powers g)
        (Localization.AtPrime qg.asIdeal)
        qg.asIdeal)
  let eS : Localization.AtPrime m.asIdeal ≃ₐ[S] Localization.AtPrime qg.asIdeal :=
    IsLocalization.algEquiv
      m.asIdeal.primeCompl
      (Localization.AtPrime m.asIdeal)
      (Localization.AtPrime qg.asIdeal)
  let eSm : Localization.AtPrime qg.asIdeal ≃ₐ[k] Localization.AtPrime m.asIdeal :=
    eS.symm.restrictScalars k
  letI : Algebra.EssFiniteType k (Localization.AtPrime qg.asIdeal) :=
    (Algebra.EssFiniteType.iff_of_algEquiv eSm).mpr inferInstance
  have hmodel :=
    exists_globalCompleteIntersectionModel_of_completeIntersectionOver m hm
  rcases hmodel with ⟨A, hAComm, hAAlg, a, e, hglobalA⟩
  letI : CommRing A := hAComm
  letI : Algebra k A := hAAlg
  have hTFAE :=
    @isCompleteIntersectionOver_tfae k _ (Localization.AtPrime qg.asIdeal) _ _ _ _
  -- Proof comment: compose the lifted-prime comparison with the global model already supplied by
  -- the maximal stalk.
  exact (hTFAE.out 3 0 rfl rfl).mp ⟨A, inferInstance, inferInstance, a, eSm.trans e, hglobalA⟩

/-- Helper for Chap10 Lemma 10 135 9: a maximal complete-intersection stalk spreads to a
principal-open local complete-intersection neighborhood. -/
private lemma exists_localCompleteIntersectionAway_nearMaximal_of_completeIntersectionOver
    [Algebra.FiniteType k S]
    (m : MaximalSpectrum S)
    (hm : IsCompleteIntersectionOver k (Localization.AtPrime m.asIdeal)) :
    ∃ g : S, g ∉ m.asIdeal ∧ IsLocalCompleteIntersection k (Localization.Away g) := by
  obtain ⟨g, hg, hfpg⟩ :=
    exists_finitePresentationAway_nearMaximal_of_completeIntersectionOver m hm
  letI : Algebra.FinitePresentation k (Localization.Away g) := hfpg
  letI : Algebra.FiniteType k (Localization.Away g) := inferInstance
  obtain ⟨qg, hqg⟩ := exists_primeSpectrum_away_comap_eq_of_notMem m.toPrimeSpectrum hg
  have hqgCI :
      IsCompleteIntersectionOver.{u, v, v} k (Localization.AtPrime qg.asIdeal) :=
    completeIntersectionOver_atLiftedPrime_of_completeIntersectionOver_maximal m hg qg hqg hm
  obtain ⟨u, hu, hlocalu⟩ :=
    localNearPrime_of_completeIntersectionOver_atPrime qg hqgCI
  refine ⟨g * (IsLocalization.Away.sec g u).1, ?_, ?_⟩
  · -- Proof comment: clear the iterated-away denominator back in the original ring `S`.
    exact notMem_original_away_of_iterated_away m.toPrimeSpectrum hg qg hqg hu
  · obtain ⟨e⟩ :
        Nonempty
          (Localization.Away u ≃ₐ[k]
            Localization.Away (g * (IsLocalization.Away.sec g u).1)) :=
      single_original_awayAlgEquiv g u
    -- Proof comment: the local complete-intersection chart on the iterated away-localization is
    -- equivalent to a single principal open of `S`.
    exact isLocalCompleteIntersection_of_algEquiv hlocalu e

/-- Helper for Chap10 Lemma 10 135 9: an away equivalence with a principal open of a global
complete-intersection model transports the global complete-intersection structure back to the
source principal open. -/
private lemma globalCompleteIntersection_of_awayModelEquiv
    {A : Type v} [CommRing A] [Algebra k A]
    (hA : IsGlobalCompleteIntersection k A) {g : S} {gA : A}
    (he : Nonempty (Localization.Away g ≃ₐ[k] Localization.Away gA)) :
    IsGlobalCompleteIntersection k (Localization.Away g) := by
  rcases he with ⟨eAway⟩
  -- Proof comment: first pass the model property to the model-side principal open, then transport
  -- it across the given away-equivalence.
  have hglobalAwayA : IsGlobalCompleteIntersection k (Localization.Away gA) :=
    IsGlobalCompleteIntersection.of_isLocalizationAway gA hA
  exact IsGlobalCompleteIntersection.of_algEquiv hglobalAwayA eAway.symm

/-- Helper for Chap10 Lemma 10 135 9: a local complete-intersection algebra can be shrunk to one
global complete-intersection principal open through any fixed prime. -/
private lemma exists_globalCompleteIntersectionAway_of_localCompleteIntersection_atPrime
    {A : Type*} [CommRing A] [Algebra k A]
    (q : PrimeSpectrum A)
    (hlocal : IsLocalCompleteIntersection k A) :
    ∃ u : A, u ∉ q.asIdeal ∧ IsGlobalCompleteIntersection k (Localization.Away u) := by
  -- Proof comment: shrink the finite local-CI cover to one basic open meeting the chosen prime.
  classical
  rcases hlocal.exists_basicOpen_cover with ⟨s, hs, hglobal⟩
  obtain ⟨u, hus, hu⟩ :
      ∃ u ∈ s, u ∉ q.asIdeal := exists_notMem_of_span_eq_top_of_prime s hs
  exact ⟨u, hu, hglobal u hus⟩

/-- Helper for Chap10 Lemma 10 135 9: over a finite-type `k`-algebra, the stalk at `q` is a
complete intersection exactly when some principal open through `q` is a local complete
intersection. -/
private lemma completeIntersectionOver_atPrime_iff_localNearPrime
    [Algebra.FiniteType k S] (q : PrimeSpectrum S) :
    IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) ↔
      isLocalCompleteIntersectionNearPrime k q := by
  constructor
  · exact localNearPrime_of_completeIntersectionOver_atPrime q
  · rintro ⟨g, hg, hlocalg⟩
    obtain ⟨qg, hqg⟩ := exists_primeSpectrum_away_comap_eq_of_notMem q hg
    let e :
        Localization.AtPrime q.asIdeal ≃ₐ[k] Localization.AtPrime qg.asIdeal :=
      localizationAtPrime_away_comapAlgEquiv q hg qg hqg
    letI : IsLocalRing (Localization.AtPrime q.asIdeal) := inferInstance
    letI : Algebra.EssFiniteType k (Localization.AtPrime q.asIdeal) := inferInstance
    have hTFAE :=
      @isCompleteIntersectionOver_tfae k _ (Localization.AtPrime q.asIdeal) _ _ _ _
    exact (hTFAE.out 4 0 rfl rfl).mp
      ⟨Localization.Away g, inferInstance, inferInstance, qg, e, hlocalg⟩

/-- Helper for Chap10 Lemma 10 135 9: a local complete-intersection algebra has complete
intersection local rings at all primes. -/
private lemma completeIntersectionOver_atPrime_of_isLocalCompleteIntersection
    (hS : IsLocalCompleteIntersection k S) (q : PrimeSpectrum S) :
    IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) := by
  -- Proof comment: apply the prime-neighborhood equivalence to the trivial chart `D(1) = Spec(S)`.
  letI : IsLocalCompleteIntersection k S := hS
  letI : Algebra.FiniteType k S := inferInstance
  have hone : (1 : S) ∉ q.asIdeal := by
    simpa [Ideal.eq_top_iff_one] using q.2.ne_top
  have hnear : isLocalCompleteIntersectionNearPrime k q := ⟨1, hone, inferInstance⟩
  exact (completeIntersectionOver_atPrime_iff_localNearPrime q).mpr hnear

/-- Helper for Chap10 Lemma 10 135 9: a maximal complete-intersection stalk spreads to a
principal-open global complete-intersection neighborhood. -/
private lemma exists_globalCompleteIntersection_nearMaximal_of_completeIntersectionOver
    [Algebra.FiniteType k S]
    (m : MaximalSpectrum S)
    (hm : IsCompleteIntersectionOver k (Localization.AtPrime m.asIdeal)) :
    ∃ g : S, g ∉ m.asIdeal ∧ IsGlobalCompleteIntersection k (Localization.Away g) := by
  -- Route correction: the old proof was circular because `completeIntersectionOver_atPrime_tfae`
  -- on `S` needs `[Algebra.FiniteType k S]`, which is exactly what this maximal-local branch is
  -- supposed to recover. The repaired route first builds a local-CI chart `S_g`, then shrinks
  -- inside that chart exactly as in Lemma `10.135.8`.
  obtain ⟨g, hg, hlocalg⟩ :=
    exists_localCompleteIntersectionAway_nearMaximal_of_completeIntersectionOver m hm
  obtain ⟨qg, hqg⟩ := exists_primeSpectrum_away_comap_eq_of_notMem m.toPrimeSpectrum hg
  obtain ⟨u, hu, hglobalu⟩ :=
    exists_globalCompleteIntersectionAway_of_localCompleteIntersection_atPrime qg hlocalg
  refine ⟨g * (IsLocalization.Away.sec g u).1, ?_, ?_⟩
  · -- Proof comment: the denominator-clearing lemma keeps track of the original maximal ideal.
    exact notMem_original_away_of_iterated_away m.toPrimeSpectrum hg qg hqg hu
  · obtain ⟨e⟩ :
        Nonempty
          (Localization.Away u ≃ₐ[k]
            Localization.Away (g * (IsLocalization.Away.sec g u).1)) :=
      single_original_awayAlgEquiv g u
    -- Proof comment: the global complete-intersection chart inside `S_g` collapses to a single
    -- principal open of `S`.
    exact IsGlobalCompleteIntersection.of_algEquiv hglobalu e

/-- Helper for Chap10 Lemma 10 135 9: maximal principal-open complete-intersection charts admit a
finite spanning subcover. -/
private lemma exists_finiteBasicOpenCover_of_forall_maximal_globalCompleteIntersection
    (hmax :
      ∀ m : MaximalSpectrum S,
        ∃ g : S, g ∉ m.asIdeal ∧ IsGlobalCompleteIntersection k (Localization.Away g)) :
    ∃ s : Finset S,
      Ideal.span (s : Set S) = ⊤ ∧
        ∀ g ∈ s, IsGlobalCompleteIntersection k (Localization.Away g) := by
  -- Proof comment: if the good basic opens did not span the unit ideal, a maximal ideal
  -- containing their span would contradict its own witness.
  classical
  let good : Set S := { g : S | IsGlobalCompleteIntersection k (Localization.Away g) }
  have hspan : Ideal.span good = ⊤ := by
    by_contra hspan
    obtain ⟨I, hImax, hIle⟩ := Ideal.exists_le_maximal (Ideal.span good) hspan
    let m : MaximalSpectrum S := ⟨I, hImax⟩
    obtain ⟨g, hg_not_mem, hg_global⟩ := hmax m
    have hg_mem_span : g ∈ Ideal.span good := Ideal.subset_span hg_global
    have hg_mem : g ∈ m.asIdeal := hIle hg_mem_span
    exact hg_not_mem hg_mem
  obtain ⟨s, hs_subset, hs_top⟩ := (Ideal.span_eq_top_iff_finite good).mp hspan
  refine ⟨s, hs_top, ?_⟩
  intro g hg
  exact hs_subset hg

/-- Helper for Chap10 Lemma 10 135 9: maximal complete-intersection local rings would imply a
local complete-intersection cover once each stalk can be spread to a principal-open chart. -/
private lemma isLocalCompleteIntersection_of_completeIntersectionOver_maximal
    [Algebra.FiniteType k S]
    (hmax :
      ∀ m : MaximalSpectrum S,
        IsCompleteIntersectionOver k (Localization.AtPrime m.asIdeal)) :
    IsLocalCompleteIntersection k S := by
  classical
  have hglobal :
      ∀ m : MaximalSpectrum S,
        ∃ g : S, g ∉ m.asIdeal ∧ IsGlobalCompleteIntersection k (Localization.Away g) := by
    intro m
    -- Proof comment: use the global model supplied by `isCompleteIntersectionOver_tfae` for the
    -- maximal stalk and transport it back to a principal open of `S`.
    exact exists_globalCompleteIntersection_nearMaximal_of_completeIntersectionOver m (hmax m)
  obtain ⟨s, hs_top, hs_global⟩ :=
    exists_finiteBasicOpenCover_of_forall_maximal_globalCompleteIntersection hglobal
  -- Proof comment: the finite global-complete-intersection cover is exactly the definition of a
  -- local complete intersection.
  exact ⟨s, hs_top, hs_global⟩

/- Domain-style sampling pass.

Primary domain: local complete intersections over a field and their detection on prime and maximal
localizations of an algebra.

Sampled owner declarations:
* `IsLocalCompleteIntersection`;
* `IsCompleteIntersectionOver`;
* `completeIntersectionOver_atPrime_tfae`;
* `MaximalSpectrum`.

Best owner abstraction: `IsLocalCompleteIntersection k S` is the source-facing owner on `S`,
while `IsCompleteIntersectionOver k _` is the canonical owner on each local ring. For the
maximal-local criterion, `MaximalSpectrum S` is the canonical indexing object, so the theorem
surface should use it directly instead of a raw ideal plus a maximality proof.

Primitive vs. derived:
* primitive data: the field `k` and the `k`-algebra `S`;
* derived API: finite presentation and finite type of `S` from
  `IsLocalCompleteIntersection k S`, together with the prime-local and maximal-local comparison
  clauses.

Source/core/bridge triage:
* source-facing: the three-way `List.TFAE` below;
* core/canonical: `IsLocalCompleteIntersection k S` and
  `IsCompleteIntersectionOver k _`;
* bridge/view: the specialization from all prime localizations to maximal localizations.
-/

-- Proof sketch: once one of the three clauses holds, the relevant finite-presentation and
-- finite-type hypotheses are recovered from the owner abstractions (`IsLocalCompleteIntersection`
-- or the primewise/maximal complete-intersection conditions). Then apply Lemma `10.135.8` at each
-- prime `q` to identify the local complete-intersection condition on `S` with the
-- complete-intersection condition on `S_q`. The implication from all prime local rings to all
-- maximal localizations is immediate, and the converse follows from the locality of the complete
-- intersection property together with quasi-compactness of `Spec S`.
/-- Chap10 Lemma 10 135 9

For a finite type `k`-algebra `S`, the following are equivalent:
`S` is a local complete intersection over `k`; every local ring `S_q` for
`q : PrimeSpectrum S` is a complete intersection over `k`; and every localization `S_m` at a
maximal ideal `m` of `S` is a complete intersection over `k`. -/
@[stacks 00SH]
theorem isLocalCompleteIntersection_tfae_completeIntersectionOver_localRings
    [Algebra.FiniteType k S] :
    List.TFAE
      [ IsLocalCompleteIntersection k S
      , ∀ q : PrimeSpectrum S,
          IsCompleteIntersectionOver.{u, v, w} k (Localization.AtPrime q.asIdeal)
      , ∀ m : MaximalSpectrum S,
          IsCompleteIntersectionOver.{u, v, w} k (Localization.AtPrime m.asIdeal)
      ] := by
  -- Proof comment: fix one universe level for the complete-intersection owner on all stalks, then
  -- apply the three-term implication cycle `(local) -> (primewise) -> (maximal) -> (local)`.
  let P1 : Prop := IsLocalCompleteIntersection k S
  let P2 : Prop :=
    ∀ q : PrimeSpectrum S,
      IsCompleteIntersectionOver.{u, v, w} k (Localization.AtPrime q.asIdeal)
  let P3 : Prop :=
    ∀ m : MaximalSpectrum S,
      IsCompleteIntersectionOver.{u, v, w} k (Localization.AtPrime m.asIdeal)
  have hTFAE : List.TFAE [P1, P2, P3] := by
    refine tfae_three_of_cycle ?_ ?_ ?_
    · intro hS q
      exact completeIntersectionOver_atPrime_of_isLocalCompleteIntersection hS q
    · intro hq m
      exact hq m.toPrimeSpectrum
    · intro hmax
      exact isLocalCompleteIntersection_of_completeIntersectionOver_maximal hmax
  simpa [P1, P2, P3] using hTFAE

end
