import stacks_proof.stacks_project.Chap05.Definition_5_10_5
import stacks_proof.stacks_project.Chap05.Lemma_5_10_2
import stacks_proof.stacks_project.Chap10.Lemma_10_104_2
import stacks_proof.stacks_project.Chap10.Lemma_10_17_7
import stacks_proof.stacks_project.Chap10.Lemma_10_114_5
import stacks_proof.stacks_project.Chap10.Definition_10_104_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory Sequence

section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
variable [CohenMacaulayRing S] [TopologicalSpace.EquidimensionalSpace (PrimeSpectrum S)]

-- Route correction: the q-to-qbar transport route is already the right global skeleton here.
-- The actual blocker was a private quotient/localization bridge used by that route, so we now
-- reuse the earlier canonical quotient-localization owner and only keep the point-normalization
-- lemmas local.

/-- Helper for Chap10 Lemma 10 129 1: the quotient-spectrum point lying over `q` is represented by
the image ideal `q.asIdeal.map (Ideal.Quotient.mk I)`. -/
lemma quotientZeroLocusPoint_asIdeal
    {A : Type*} [CommRing A] (I : Ideal A) (q : PrimeSpectrum A) (hIq : I ≤ q.asIdeal) :
    ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).symm ⟨q, hIq⟩).asIdeal =
      q.asIdeal.map (Ideal.Quotient.mk I) := by
  -- Proof comment: this is exactly the owner-side formula for the inverse quotient-spectrum
  -- homeomorphism on the zero locus.
  simpa using
    Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_symm_asIdeal I ⟨q, hIq⟩

/-- Helper for Chap10 Lemma 10 129 1: the quotient-spectrum point over `q` contracts back to `q`.
-/
lemma quotientZeroLocusPoint_comap_asIdeal
    {A : Type*} [CommRing A] (I : Ideal A) (q : PrimeSpectrum A) (hIq : I ≤ q.asIdeal) :
    Ideal.comap (Ideal.Quotient.mk I)
        (((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).symm ⟨q, hIq⟩).asIdeal) =
      q.asIdeal := by
  -- Proof comment: after normalizing the quotient point as an image ideal, the standard quotient
  -- contraction formula closes the computation.
  rw [quotientZeroLocusPoint_asIdeal I q hIq]
  simp [Ideal.comap_map_mk hIq]

/-- Helper for Chap10 Lemma 10 129 1: quotienting by an ideal contained in a prime sends the
source prime complement to the induced prime complement in the quotient ring. -/
lemma quotientPrimeCompl_eq_algebraMapSubmonoidAtUnder
    {A : Type*} [CommRing A] (I q : Ideal A) [q.IsPrime]
    [(Ideal.map (Ideal.Quotient.mk I) q).IsPrime] (hIq : I ≤ q) :
    Algebra.algebraMapSubmonoid (A ⧸ I) q.primeCompl =
      (Ideal.map (Ideal.Quotient.mk I) q).primeCompl := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    -- Proof comment: if `a mod I` lands in the quotient prime, contracting along the quotient map
    -- forces `a ∈ q`, contradicting `a ∉ q`.
    change Ideal.Quotient.mk I a ∉ Ideal.map (Ideal.Quotient.mk I) q
    intro hx
    have hqx : a ∈ Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) q) := hx
    exact ha <| by simpa [Ideal.comap_map_mk hIq] using hqx
  · intro hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨a, ?_, rfl⟩
    -- Proof comment: conversely, if `a mod I` avoids the quotient prime, then `a` already
    -- avoids the source prime.
    intro ha
    exact hx (Ideal.mem_map_of_mem (Ideal.Quotient.mk I) ha)

/-- Helper for Chap10 Lemma 10 129 1: the quotient-spectrum point over `q` has local topological
dimension bounded by the global topological dimension of the zero locus. -/
lemma quotientZeroLocusPoint_topologicalKrullDimAt_le
    {A : Type*} [CommRing A] (I : Ideal A) (q : PrimeSpectrum A) (hIq : I ≤ q.asIdeal) :
    topologicalKrullDimAt ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).symm ⟨q, hIq⟩) ≤
      topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set A)) := by
  let qbar : PrimeSpectrum (A ⧸ I) :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).symm ⟨q, hIq⟩
  let U : TopologicalSpace.OpenNhdsOf qbar := ⊤
  have hU : topologicalKrullDim U ≤ topologicalKrullDim (PrimeSpectrum (A ⧸ I)) := by
    -- Proof comment: the whole quotient spectrum is an open neighborhood of `qbar`, so local
    -- dimension is bounded by the ambient quotient-spectrum dimension.
    simpa [U] using
      topologicalKrullDim_subspace_le (PrimeSpectrum (A ⧸ I))
        (Set.univ : Set (PrimeSpectrum (A ⧸ I)))
  -- Proof comment: move from the quotient spectrum to the zero locus by the canonical
  -- homeomorphism from Lemma `10.17.7`.
  calc
    topologicalKrullDimAt qbar ≤ topologicalKrullDim (PrimeSpectrum (A ⧸ I)) :=
      (topologicalKrullDimAt_le qbar U).trans hU
    _ = topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set A)) := by
      simpa using
        IsHomeomorph.topologicalKrullDim_eq
          (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I)
          (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).isHomeomorph

include k

/-- Helper for Chap10 Lemma 10 129 1: localizing the self-module of a ring at a prime ideal
recovers the corresponding localized ring. -/
private noncomputable abbrev localizedSelfLinearEquivAtPrime
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    LocalizedModule.AtPrime p A ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
  (LocalizedModule.equivTensorProduct p.primeCompl A).trans
    (Algebra.TensorProduct.rid A (Localization.AtPrime p)
      (Localization.AtPrime p)).toLinearEquiv

omit [CohenMacaulayRing S] [TopologicalSpace.EquidimensionalSpace (PrimeSpectrum S)] in
/-- Helper for Chap10 Lemma 10 129 1: at a closed point of a finite type affine scheme over a
field, the local topological Krull dimension equals the Krull dimension of the maximal
localization. -/
private lemma topologicalKrullDimAtClosedPointEqRingKrullDimLocalizationAtMaximal
    (m : MaximalSpectrum S) :
    topologicalKrullDimAt m.toPrimeSpectrum =
      ringKrullDim (Localization.AtPrime m.asIdeal) := by
  -- Proof comment: rewrite the local dimension as the infimum over maximal localizations above
  -- `m`, then collapse that infimum because a maximal ideal above `m.asIdeal` must equal `m`.
  rw [topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over
    (k := k) (S := S) m.toPrimeSpectrum]
  letI : Subsingleton { n : MaximalSpectrum S // m.asIdeal ≤ n.asIdeal } := by
    refine ⟨fun a b ↦ Subtype.ext <| MaximalSpectrum.ext <| ?_⟩
    have ha : m.asIdeal = a.1.asIdeal :=
      Ideal.IsMaximal.eq_of_le m.isMaximal a.1.isMaximal.ne_top a.2
    have hb : m.asIdeal = b.1.asIdeal :=
      Ideal.IsMaximal.eq_of_le m.isMaximal b.1.isMaximal.ne_top b.2
    exact ha.symm.trans hb
  let e : { n : MaximalSpectrum S // m.asIdeal ≤ n.asIdeal } := ⟨m, le_rfl⟩
  simpa [e] using
    (ciInf_subsingleton e fun n ↦ ringKrullDim (Localization.AtPrime n.1.asIdeal))

omit [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 129 1: in an equidimensional affine spectrum of finite type over a
field, the local topological Krull dimension is independent of the chosen point. -/
private lemma topologicalKrullDimAt_eq_of_equidimensional
    (x y : PrimeSpectrum S) :
    topologicalKrullDimAt x = topologicalKrullDimAt y := by
  -- Proof comment: both local dimensions are suprema of component dimensions through the chosen
  -- point, and equidimensionality identifies every irreducible-component dimension.
  rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through
    (k := k) (S := S) x]
  rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through
    (k := k) (S := S) y]
  refine le_antisymm ?_ ?_
  · let W : irreducibleComponents (PrimeSpectrum S) :=
      ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
    have hyW : y ∈ (W : Set (PrimeSpectrum S)) := by
      have hySelf : y ∈ irreducibleComponent y := mem_irreducibleComponent
      simpa [W] using hySelf
    refine iSup_le fun Z ↦ ?_
    calc
      topologicalKrullDim (Z.1 : Set (PrimeSpectrum S)) =
          topologicalKrullDim (W : Set (PrimeSpectrum S)) :=
        TopologicalSpace.EquidimensionalSpace.topologicalKrullDim_eq Z.1 W
      _ ≤
          ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
              y ∈ (Z : Set (PrimeSpectrum S)) },
            topologicalKrullDim (Z : Set (PrimeSpectrum S)) :=
        le_iSup_of_le ⟨W, hyW⟩ le_rfl
  · let W : irreducibleComponents (PrimeSpectrum S) :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    have hxW : x ∈ (W : Set (PrimeSpectrum S)) := by
      have hxSelf : x ∈ irreducibleComponent x := mem_irreducibleComponent
      simpa [W] using hxSelf
    refine iSup_le fun Z ↦ ?_
    calc
      topologicalKrullDim (Z.1 : Set (PrimeSpectrum S)) =
          topologicalKrullDim (W : Set (PrimeSpectrum S)) :=
        TopologicalSpace.EquidimensionalSpace.topologicalKrullDim_eq Z.1 W
      _ ≤
          ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
              x ∈ (Z : Set (PrimeSpectrum S)) },
            topologicalKrullDim (Z : Set (PrimeSpectrum S)) :=
        le_iSup_of_le ⟨W, hxW⟩ le_rfl

omit [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 129 1: every point of `Spec(S)` has local topological Krull
dimension equal to the global topological Krull dimension of `Spec(S)`. -/
private lemma topologicalKrullDimAt_eq_topologicalKrullDim
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x = topologicalKrullDim (PrimeSpectrum S) := by
  -- Proof comment: the global dimension is the supremum of all local dimensions, and
  -- equidimensionality makes each summand equal to the value at `x`.
  calc
    topologicalKrullDimAt x = ⨆ y : PrimeSpectrum S, topologicalKrullDimAt y := by
      refine le_antisymm ?_ ?_
      · exact le_iSup (fun y : PrimeSpectrum S ↦ topologicalKrullDimAt y) x
      · refine iSup_le fun y ↦ ?_
        exact le_of_eq (topologicalKrullDimAt_eq_of_equidimensional (k := k) y x)
    _ = topologicalKrullDim (PrimeSpectrum S) := by
      simpa using (topologicalKrullDim_eq_iSup_topologicalKrullDimAt
        (X := PrimeSpectrum S)).symm

omit [CohenMacaulayRing S] in
/-- Helper for Chap10 Lemma 10 129 1: every maximal localization of `S` has Krull dimension
`ringKrullDim S`. -/
private lemma ringKrullDim_localizationAtMaximal_eq_ringKrullDim
    (m : MaximalSpectrum S) :
    ringKrullDim (Localization.AtPrime m.asIdeal) = ringKrullDim S := by
  -- Proof comment: identify the maximal localization with the local topological dimension at the
  -- corresponding closed point, then compare that local value with the global spectrum dimension.
  calc
    ringKrullDim (Localization.AtPrime m.asIdeal) =
        topologicalKrullDimAt m.toPrimeSpectrum := by
      exact
        (topologicalKrullDimAtClosedPointEqRingKrullDimLocalizationAtMaximal (k := k) m).symm
    _ = topologicalKrullDim (PrimeSpectrum S) :=
      topologicalKrullDimAt_eq_topologicalKrullDim (k := k) m.toPrimeSpectrum
    _ = ringKrullDim S := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim S

omit k

/-- Helper for Chap10 Lemma 10 129 1: quotienting a Noetherian local ring by a list of maximal
ideal elements lowers Krull dimension by at most the length of the list. -/
private theorem ringKrullDimLeQuotientOfListAddLengthOfMemMaximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (xs : List A) (hxs : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal A) :
    ringKrullDim A ≤ ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length := by
  classical
  -- Proof comment: Krull's height theorem gives the bound for the finite set of distinct listed
  -- generators; passing from the deduplicated finite set back to the list only weakens the
  -- cardinality term.
  have hset : ((xs.toFinset : Finset A) : Set A) ⊆ Ring.jacobson A := by
    intro x hx
    have hx_mem : x ∈ xs := by
      simpa using hx
    have hx_max : x ∈ IsLocalRing.maximalIdeal A := hxs x hx_mem
    simpa [IsLocalRing.ringJacobson_eq_maximalIdeal A] using hx_max
  have hfinite :=
    ringKrullDim_le_ringKrullDim_quotient_add_card xs.toFinset hset
  have hspan : Ideal.span (((xs.toFinset : Finset A) : Set A)) = Ideal.ofList xs := by
    exact congrArg Ideal.span (List.coe_toFinset xs)
  have hcard : (xs.toFinset.card : WithBot ℕ∞) ≤ (xs.length : WithBot ℕ∞) := by
    exact WithBot.coe_le_coe.mpr (ENat.coe_le_coe.mpr (List.toFinset_card_le xs))
  calc
    ringKrullDim A ≤
        ringKrullDim (A ⧸ Ideal.span (((xs.toFinset : Finset A) : Set A))) +
          xs.toFinset.card := hfinite
    _ = ringKrullDim (A ⧸ Ideal.ofList xs) + xs.toFinset.card := by rw [hspan]
    _ ≤ ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length := by
      simpa [add_comm] using add_le_add_right hcard (ringKrullDim (A ⧸ Ideal.ofList xs))

omit [CohenMacaulayRing S] [TopologicalSpace.EquidimensionalSpace (PrimeSpectrum S)] in
/-- Helper for Chap10 Lemma 10 129 1: the quotient-spectrum point over a maximal ideal is again a
maximal ideal of the quotient ring. -/
private lemma quotientZeroLocusPoint_isMaximal
    (I : Ideal S) (m : MaximalSpectrum S) (hIm : I ≤ m.asIdeal) :
    (((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).symm
        ⟨m.toPrimeSpectrum, hIm⟩).asIdeal).IsMaximal := by
  -- Proof comment: rewrite the quotient point as the image of `m.asIdeal`, so maximality
  -- descends through the surjective quotient map.
  rw [quotientZeroLocusPoint_asIdeal I m.toPrimeSpectrum hIm]
  simpa using
    (Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk I) (m := m.asIdeal) Ideal.Quotient.mk_surjective
      (by simpa [Ideal.mk_ker] using hIm))

omit [CohenMacaulayRing S] [TopologicalSpace.EquidimensionalSpace (PrimeSpectrum S)] in
/-- Helper for Chap10 Lemma 10 129 1: localizing the quotient `S ⧸ I` at the closed point over
`m` is the same as quotienting the maximal localization `Sₘ` by the mapped ideal `I Sₘ`. -/
private noncomputable def maximalQuotientLocalizationRingEquiv
    (I : Ideal S) (m : MaximalSpectrum S) (hIm : I ≤ m.asIdeal) :
    ((Localization.AtPrime m.asIdeal) ⧸
      Ideal.map (algebraMap S (Localization.AtPrime m.asIdeal)) I) ≃+*
      Localization.AtPrime
        (((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).symm
          ⟨m.toPrimeSpectrum, hIm⟩).asIdeal) := by
  let qbar : PrimeSpectrum (S ⧸ I) :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).symm ⟨m.toPrimeSpectrum, hIm⟩
  let M : Submonoid (S ⧸ I) :=
    Algebra.algebraMapSubmonoid (S ⧸ I) m.asIdeal.primeCompl
  let Qloc :=
    ((Localization.AtPrime m.asIdeal) ⧸
      Ideal.map (algebraMap S (Localization.AtPrime m.asIdeal)) I)
  letI : (Ideal.map (Ideal.Quotient.mk I) m.asIdeal).IsPrime := by
    -- Proof comment: the quotient-spectrum point over `m` is prime, and its ideal is exactly the
    -- image ideal needed by the submonoid comparison.
    simpa [qbar, quotientZeroLocusPoint_asIdeal (I := I) (q := m.toPrimeSpectrum) hIm] using qbar.2
  let eLoc : Localization M ≃ₐ[S ⧸ I] Qloc :=
    Localization.algEquiv M Qloc
  have hSub : M = qbar.asIdeal.primeCompl := by
    -- Proof comment: quotienting by `I` sends the complement of `m` to the complement of the
    -- induced quotient prime.
    simpa [M, qbar, quotientZeroLocusPoint_asIdeal (I := I) (q := m.toPrimeSpectrum) hIm] using
      quotientPrimeCompl_eq_algebraMapSubmonoidAtUnder (A := S) I m.asIdeal hIm
  letI : IsLocalization M (Localization.AtPrime qbar.asIdeal) := by
    simpa [hSub] using
      (inferInstance : IsLocalization qbar.asIdeal.primeCompl
        (Localization.AtPrime qbar.asIdeal))
  -- Proof comment: both rings are canonical localizations of `S ⧸ I` at the same prime
  -- complement, so the standard localization equivalence finishes.
  exact (eLoc.symm.trans (Localization.algEquiv M (Localization.AtPrime qbar.asIdeal))).toRingEquiv

include k

omit [CohenMacaulayRing S] [TopologicalSpace.EquidimensionalSpace (PrimeSpectrum S)] in
/-- Helper for Chap10 Lemma 10 129 1: the quotient of the maximal localization `Sₘ` by `I Sₘ`
has Krull dimension bounded by the topological Krull dimension of `V(I)`. -/
private lemma maximalQuotientRingKrullDim_le_zeroLocus
    (I : Ideal S) (m : MaximalSpectrum S) (hIm : I ≤ m.asIdeal) :
    ringKrullDim
        ((Localization.AtPrime m.asIdeal) ⧸
          Ideal.map (algebraMap S (Localization.AtPrime m.asIdeal)) I) ≤
      topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set S)) := by
  let qbar : PrimeSpectrum (S ⧸ I) :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).symm ⟨m.toPrimeSpectrum, hIm⟩
  let mbar : MaximalSpectrum (S ⧸ I) :=
    ⟨qbar.asIdeal, quotientZeroLocusPoint_isMaximal (I := I) m hIm⟩
  -- Proof comment: identify the quotient of the maximal localization with the localization of
  -- `S ⧸ I` at the closed point over `m`, then compare its local dimension with the ambient zero
  -- locus via the quotient-spectrum homeomorphism.
  calc
    ringKrullDim
        ((Localization.AtPrime m.asIdeal) ⧸
          Ideal.map (algebraMap S (Localization.AtPrime m.asIdeal)) I) =
        ringKrullDim (Localization.AtPrime qbar.asIdeal) := by
      simpa [qbar] using
        ringKrullDim_eq_of_ringEquiv
          (maximalQuotientLocalizationRingEquiv (I := I) m hIm)
    _ = topologicalKrullDimAt mbar.toPrimeSpectrum := by
      exact
        (topologicalKrullDimAtClosedPointEqRingKrullDimLocalizationAtMaximal
          (k := k) (S := S ⧸ I) mbar).symm
    _ ≤ topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set S)) := by
      simpa [qbar, mbar] using
        quotientZeroLocusPoint_topologicalKrullDimAt_le I m.toPrimeSpectrum hIm

omit k

include k

/-- Helper for Chap10 Lemma 10 129 1: the localized list is regular at every maximal ideal
containing `Ideal.ofList fs`. -/
private lemma isRegularAtMaximalOfZeroLocusDimensionBound
    {fs : List S}
    (hzero :
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) + fs.length ≤
        ringKrullDim S)
    (m : MaximalSpectrum S) (hIm : Ideal.ofList fs ≤ m.asIdeal) :
    IsRegular (Localization.AtPrime m.asIdeal)
      (fs.map (algebraMap S (Localization.AtPrime m.asIdeal))) := by
  let Sm := Localization.AtPrime m.asIdeal
  letI : Module.CohenMacaulay Sm Sm := localizedRing_cohenMacaulay S m.toPrimeSpectrum
  have hxs_mem :
      ∀ x ∈ fs.map (algebraMap S Sm), x ∈ IsLocalRing.maximalIdeal Sm := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨a, ha, rfl⟩
    have ham : a ∈ m.asIdeal := hIm (Ideal.subset_span ha)
    -- Proof comment: every listed element lands in the image of `m.asIdeal`, which is the maximal
    -- ideal of the prime localization.
    simpa [Sm, Localization.AtPrime.map_eq_maximalIdeal (R := S) (I := m.asIdeal)] using
      Ideal.mem_map_of_mem (algebraMap S Sm) ham
  have hlower :
      ringKrullDim Sm ≤
        ringKrullDim (Sm ⧸ Ideal.ofList (fs.map (algebraMap S Sm))) + fs.length := by
    -- Proof comment: this is the local Krull-height lower bound for the listed generators in the
    -- maximal ideal.
    simpa [List.length_map] using
      ringKrullDimLeQuotientOfListAddLengthOfMemMaximalIdeal
        (A := Sm) (xs := fs.map (algebraMap S Sm)) hxs_mem
  have hupper :
      ringKrullDim (Sm ⧸ Ideal.ofList (fs.map (algebraMap S Sm))) + fs.length ≤
        ringKrullDim Sm := by
    -- Proof comment: the quotient dimension is bounded by the zero-locus dimension, which is
    -- itself bounded by the global Krull dimension of `S`; the maximal-local dimension comparison
    -- then moves that bound to `Sₘ`.
    have hquot_le0 :
        ringKrullDim (Sm ⧸ Ideal.map (algebraMap S Sm) (Ideal.ofList fs)) ≤
          topologicalKrullDim (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) := by
      simpa [Sm] using
        maximalQuotientRingKrullDim_le_zeroLocus (k := k) (I := Ideal.ofList fs) m hIm
    have hquot_le :
        ringKrullDim (Sm ⧸ Ideal.ofList (fs.map (algebraMap S Sm))) ≤
          topologicalKrullDim (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) := by
      rw [← Ideal.map_ofList (f := algebraMap S Sm) fs]
      exact hquot_le0
    calc
      ringKrullDim (Sm ⧸ Ideal.ofList (fs.map (algebraMap S Sm))) + fs.length ≤
          topologicalKrullDim (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) + fs.length := by
        simpa [add_comm] using add_le_add_right hquot_le fs.length
      _ ≤ ringKrullDim S := hzero
      _ = ringKrullDim Sm := (ringKrullDim_localizationAtMaximal_eq_ringKrullDim (k := k) m).symm
  have hEq :
      ringKrullDim (Sm ⧸ Ideal.ofList (fs.map (algebraMap S Sm))) + fs.length =
        ringKrullDim Sm :=
    le_antisymm hupper hlower
  -- Proof comment: the Cohen-Macaulay local regular-sequence criterion converts the exact
  -- dimension formula into regularity of the localized list.
  exact (isRegular_iff_ringKrullDim_quotient_add_length_eq (R := Sm) hxs_mem).mpr <|
    by simpa [List.length_map] using hEq

omit k

omit [CohenMacaulayRing S] [TopologicalSpace.EquidimensionalSpace (PrimeSpectrum S)] in
/-- Helper for Chap10 Lemma 10 129 1: localizing first at `m` and then at the image of `q ≤ m`
recovers the one-step localization at `q`. -/
private theorem comapMapOfLeAtPrime
    {q m : Ideal S} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) :
    Ideal.comap (algebraMap S (Localization.AtPrime m))
      (Ideal.map (algebraMap S (Localization.AtPrime m)) q) = q := by
  -- Proof comment: the complement of `m` is disjoint from `q` because `q ≤ m`, so localization
  -- preserves the prime by extension-contraction.
  exact IsLocalization.comap_map_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m)
    (I := q) inferInstance (by
      rw [Set.disjoint_left]
      intro x hxm hxq
      exact hxm (hqm hxq))

omit [CohenMacaulayRing S] [TopologicalSpace.EquidimensionalSpace (PrimeSpectrum S)] in
/-- Helper for Chap10 Lemma 10 129 1: localizing first at `m` and then at the image of `q ≤ m`
recovers the one-step localization at `q`. -/
private noncomputable def localizationAtPrimeRingEquivOfLe
    {q m : Ideal S} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) :
    let Sm := Localization.AtPrime m
    let qm : Ideal Sm := Ideal.map (algebraMap S Sm) q
    letI : qm.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime m hqm
    Localization.AtPrime q ≃ₐ[S] Localization.AtPrime qm := by
  let Sm := Localization.AtPrime m
  let qm : Ideal Sm := Ideal.map (algebraMap S Sm) q
  letI : qm.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime m hqm
  have hcomap : Ideal.comap (algebraMap S Sm) qm = q := by
    simpa [Sm, qm] using comapMapOfLeAtPrime (q := q) (m := m) hqm
  -- Proof comment: the iterated-localization owner expects the contracted prime as source, so
  -- first rewrite that source to `q`, then collapse the localization tower.
  let eDomain : Localization.AtPrime q ≃ₐ[S]
      Localization.AtPrime (Ideal.comap (algebraMap S Sm) qm) :=
    Localization.localAlgEquiv q (Ideal.comap (algebraMap S Sm) qm)
      (AlgEquiv.refl (R := S) (A₁ := S)) (by simpa using hcomap.symm)
  let eDouble : Localization.AtPrime (Ideal.comap (algebraMap S Sm) qm) ≃ₐ[S]
      Localization.AtPrime qm :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := m.primeCompl) qm
  exact eDomain.trans eDouble

/-
Domain-style sampling:
* primary domain: regular sequences in Cohen-Macaulay affine rings of finite type over a field,
  organized through the chapter owners for local Cohen-Macaulayness, local dimension, and regular
  sequences;
* sampled owner declarations of the same kind:
  `CohenMacaulayRing`,
  `TopologicalSpace.EquidimensionalSpace`,
  `topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over`,
  `isRegular_iff_ringKrullDim_quotient_add_length_eq`;
* best owner abstraction: the ambient owners are `CohenMacaulayRing S` and
  `EquidimensionalSpace (PrimeSpectrum S)`, while the local regular-sequence conclusion should be
  phrased directly with `IsRegular` on `Localization.AtPrime q.asIdeal`;
* primitive data: the finite list `fs` and the zero-locus dimension bound;
* derived API: the regularity of the localized sequence at primes containing `Ideal.ofList fs`,
  together with the source-facing dimension formula for
  `V(Ideal.ofList fs) = PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)`;

Source/core/bridge triage:
* `source-facing`: Lemma 10.129.1, giving the expected codimension of the closed subset
  `V(Ideal.ofList fs)` together with local regularity along that closed set;
* `core/canonical`: `CohenMacaulayRing`, `EquidimensionalSpace`, `ringKrullDim`,
  `topologicalKrullDim`, `PrimeSpectrum.zeroLocus`, `Localization.AtPrime`, and the chapter owner theorem
  `isRegular_iff_ringKrullDim_quotient_add_length_eq`;
* `bridge/view`: passing from the global equidimensional ring to the local rings
  `Localization.AtPrime q.asIdeal` via the local-dimension owner
  `topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over`.

The dimension parameter `d` is not primitive data here: it is completely determined by the owner
`ringKrullDim S`. Keeping it as a separate public binder would only duplicate the canonical global
dimension owner. The source-facing dimension clause should therefore stay stated for the closed
subset `V(Ideal.ofList fs)` itself. Semantic recall also points to `ringKrullDim_quotient`, but
the textbook statement is about the zero locus rather than the quotient ring as the primary owner.
-/
-- Proof sketch: use the equidimensionality and Cohen-Macaulay hypotheses to identify the Krull
-- dimension of every maximal localization of `S` with `ringKrullDim S`. For a prime `q`
-- containing
-- `Ideal.ofList fs`, localize at a maximal ideal above `q` and apply Proposition `10.103.4` in
-- that Cohen-Macaulay local ring to the image of `fs`, using the assumed bound on the nonempty
-- zero locus. For the source-facing dimension clause, record the dimension of the zero locus
-- `V(Ideal.ofList fs)` itself rather than the quotient-spectrum bridge. The source proof reasons
-- through maximal ideals of `V(Ideal.ofList fs)`, so we make the hidden properness hypothesis
-- for that equality clause explicit; equivalently, the zero locus is nonempty by
-- `PrimeSpectrum.zeroLocus_empty_iff_eq_top`. This gives the regularity statement at every prime
-- in that zero locus together with the expected codimension formula.
include k

/-- Helper for Chap10 Lemma 10 129 1: if `Ideal.ofList fs` is proper, then the zero-locus
dimension bound is an equality. -/
private lemma zeroLocusDimensionBound_eq_of_ne_top
    {fs : List S}
    (hzero :
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) + fs.length ≤
        ringKrullDim S)
    (hneq : Ideal.ofList fs ≠ ⊤) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) + fs.length =
      ringKrullDim S := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal (Ideal.ofList fs) hneq
  let m : MaximalSpectrum S := ⟨M, hM⟩
  have hregm :
      IsRegular (Localization.AtPrime m.asIdeal)
        (fs.map (algebraMap S (Localization.AtPrime m.asIdeal))) :=
    isRegularAtMaximalOfZeroLocusDimensionBound (k := k) hzero m hIM
  have hxs_mem :
      ∀ x ∈ fs.map (algebraMap S (Localization.AtPrime m.asIdeal)),
        x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal) := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨a, ha, rfl⟩
    have ham : a ∈ m.asIdeal := hIM (Ideal.subset_span ha)
    -- Proof comment: the chosen maximal ideal contains the list ideal, so the localized list
    -- lands in the maximal ideal of `Sₘ`.
    simpa [Localization.AtPrime.map_eq_maximalIdeal (R := S) (I := m.asIdeal)] using
      Ideal.mem_map_of_mem (algebraMap S (Localization.AtPrime m.asIdeal)) ham
  letI : Module.CohenMacaulay (Localization.AtPrime m.asIdeal)
      (Localization.AtPrime m.asIdeal) := localizedRing_cohenMacaulay S m.toPrimeSpectrum
  have hlocalEq :
      ringKrullDim
          ((Localization.AtPrime m.asIdeal) ⧸
            Ideal.ofList (fs.map (algebraMap S (Localization.AtPrime m.asIdeal)))) +
        fs.length =
          ringKrullDim (Localization.AtPrime m.asIdeal) := by
    simpa [Ideal.map_ofList, List.length_map] using
      (isRegular_iff_ringKrullDim_quotient_add_length_eq
        (R := Localization.AtPrime m.asIdeal) hxs_mem).mp hregm
  -- Proof comment: the maximal-local exact equality forces the global expected-codimension
  -- identity once compared with the zero-locus upper bound.
  refine le_antisymm hzero ?_
  calc
    ringKrullDim S = ringKrullDim (Localization.AtPrime m.asIdeal) :=
      (ringKrullDim_localizationAtMaximal_eq_ringKrullDim (k := k) m).symm
    _ =
        ringKrullDim
          ((Localization.AtPrime m.asIdeal) ⧸
            Ideal.ofList (fs.map (algebraMap S (Localization.AtPrime m.asIdeal)))) +
          fs.length := hlocalEq.symm
    _ ≤ topologicalKrullDim (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) + fs.length := by
      rw [← Ideal.map_ofList (f := algebraMap S (Localization.AtPrime m.asIdeal)) fs]
      simpa [add_comm] using
        add_le_add_right
          (maximalQuotientRingKrullDim_le_zeroLocus (k := k) (I := Ideal.ofList fs) m hIM)
          fs.length

/-- Helper for Chap10 Lemma 10 129 1: at every prime containing `Ideal.ofList fs`, the localized
list is regular once the zero-locus dimension bound holds. -/
private lemma isRegularAtPrimeOfZeroLocusDimensionBound
    {fs : List S}
    (hzero :
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) + fs.length ≤
        ringKrullDim S)
    (q : PrimeSpectrum S) (hIq : Ideal.ofList fs ≤ q.asIdeal) :
    IsRegular (Localization.AtPrime q.asIdeal)
      (fs.map (algebraMap S (Localization.AtPrime q.asIdeal))) := by
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q.asIdeal q.2.1
  let m : MaximalSpectrum S := ⟨M, hM⟩
  let Sm := Localization.AtPrime m.asIdeal
  let qm : Ideal Sm := Ideal.map (algebraMap S Sm) q.asIdeal
  letI : qm.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime m.asIdeal hqM
  let Qm := Localization.AtPrime qm
  have hregm :
      IsRegular Sm (fs.map (algebraMap S Sm)) :=
    isRegularAtMaximalOfZeroLocusDimensionBound (k := k) hzero m (hIq.trans hqM)
  have hmem_qm : ∀ x ∈ fs.map (algebraMap S Sm), x ∈ qm := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨a, ha, rfl⟩
    exact Ideal.mem_map_of_mem (algebraMap S Sm) (hIq (Ideal.subset_span ha))
  have hregLoc :
      IsRegular (LocalizedModule.AtPrime qm Sm)
        ((fs.map (algebraMap S Sm)).map (algebraMap Sm Qm)) := by
    -- Proof comment: localize the regular sequence from `Sₘ` to the prime localization at
    -- `qSₘ`, using that every listed element lies in the target prime ideal.
    simpa using
      hregm.1.isRegular_of_isLocalizedModule_of_mem
        (S := Qm) (p := qm)
        (N := LocalizedModule.AtPrime qm Sm)
        (f := LocalizedModule.mkLinearMap qm.primeCompl Sm) hmem_qm
  have hregQm :
      IsRegular Qm ((fs.map (algebraMap S Sm)).map (algebraMap Sm Qm)) := by
    -- Proof comment: the localized self-module is canonically the localized ring itself.
    exact (localizedSelfLinearEquivAtPrime (A := Sm) qm).isRegular_congr _ |>.1 hregLoc
  let e : Localization.AtPrime q.asIdeal ≃ₐ[S] Qm :=
    localizationAtPrimeRingEquivOfLe (q := q.asIdeal) (m := m.asIdeal) hqM
  have hmapElem (a : S) :
      e.symm ((algebraMap Sm Qm) ((algebraMap S Sm) a)) =
        (algebraMap S (Localization.AtPrime q.asIdeal)) a := by
    simpa [IsScalarTower.algebraMap_eq S Sm Qm] using e.symm.commutes a
  have hlist :
      ((fs.map (algebraMap S Sm)).map (algebraMap Sm Qm)).map e.symm =
        fs.map (algebraMap S (Localization.AtPrime q.asIdeal)) := by
    simpa [List.map_map, Function.comp, hmapElem]
  -- Proof comment: the iterated-localization equivalence identifies the twice-localized list
  -- with the direct image of `fs` in `S_q`.
  have hregBq :
      IsRegular (Localization.AtPrime q.asIdeal)
        (((fs.map (algebraMap S Sm)).map (algebraMap Sm Qm)).map e.symm) :=
    (e.symm.toAddEquiv.isRegular_congr <|
      List.forall₂_map_right_iff.mpr <|
        List.forall₂_same.mpr fun a _ x => by
          simpa [Algebra.smul_def] using e.symm.map_mul a x).1 hregQm
  exact hlist ▸ hregBq

/-- Chap10 Lemma 10 129 1: let `k` be a field, let `S` be a finite type `k`-algebra, and let `fs`
be a finite list of elements of `S`. Assume that `S` is Cohen-Macaulay and equidimensional of
dimension `ringKrullDim S`, and that the closed subset `V(Ideal.ofList fs)` has the expected
codimension lower bound, written canonically as
`topologicalKrullDim (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) + fs.length ≤
  ringKrullDim S`.
Then, provided `Ideal.ofList fs ≠ ⊤` (equivalently `V(Ideal.ofList fs) ≠ ∅`), the zero locus has
the expected codimension; moreover, for every prime `q` of `S`
containing `Ideal.ofList fs`, the image of `fs` in the local ring `S_q` is a regular sequence. -/
@[stacks 00R9]
theorem ringKrullDim_quotient_add_length_eq_and_isRegular_atPrime_of_cohenMacaulay_equidimensional
    {fs : List S}
    (hzero :
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) + fs.length ≤
        ringKrullDim S)
    :
    (Ideal.ofList fs ≠ ⊤ →
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) + fs.length =
        ringKrullDim S) ∧
      ∀ q : PrimeSpectrum S, Ideal.ofList fs ≤ q.asIdeal →
        IsRegular (Localization.AtPrime q.asIdeal)
          (fs.map (algebraMap S (Localization.AtPrime q.asIdeal))) := by
  constructor
  · exact zeroLocusDimensionBound_eq_of_ne_top (k := k) hzero
  · exact isRegularAtPrimeOfZeroLocusDimensionBound (k := k) hzero

end
