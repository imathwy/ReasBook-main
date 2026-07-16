import Mathlib
import stacks_proof.stacks_project.Chap05.Definition_5_10_1
import stacks_proof.stacks_project.Chap05.Lemma_5_20_3
import stacks_proof.stacks_project.Chap10.Lemma_10_17_7
import stacks_proof.stacks_project.Chap10.Definition_10_105_1
import stacks_proof.stacks_project.Chap10.Lemma_10_112_4
import stacks_proof.stacks_project.Chap10.Lemma_10_112_7
import stacks_proof.stacks_project.Chap10.Lemma_10_114_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-!
The following helpers record the part of the source proof that is purely formal around the
specialization order and the indexing type of maximal ideals above a point. The remaining hard
steps are the component-supremum local-dimension formula and the finite-type Jacobson closed-point
selection/comparison.
-/

/-- Helper for Chap10 Lemma 10 114 5: finite algebra fibers have zero-dimensional local rings. -/
private lemma ringKrullDim_fiberLocalRingAt_eq_zero_of_moduleFinite
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
    [Module.Finite R T] (q : PrimeSpectrum T) :
    ringKrullDim (fiberLocalRingAt R T q) = 0 := by
  -- Finiteness makes the fiber Artinian, hence zero-dimensional.
  have hArt : IsArtinianRing (fiberLocalRingAt R T q) := by
    dsimp [fiberLocalRingAt]
    exact IsArtinianRing.localization_artinian
      ((fiberPrimeAt R T q).asIdeal.primeCompl)
      (Localization.AtPrime (fiberPrimeAt R T q).asIdeal)
  letI : IsArtinianRing (fiberLocalRingAt R T q) := hArt
  have hNoeth : IsNoetherianRing (fiberLocalRingAt R T q) := inferInstance
  letI : IsNoetherianRing (fiberLocalRingAt R T q) := hNoeth
  have hle : Ring.KrullDimLE 0 (fiberLocalRingAt R T q) :=
    (isArtinianRing_iff_krullDimLE_zero (R := fiberLocalRingAt R T q)).mp hArt
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hle

/-- Helper for Chap10 Lemma 10 114 5: under a finite going-down map, local dimensions agree with
the contracted prime. -/
private lemma ringKrullDim_localizationAtPrime_eq_under_of_moduleFinite_hasGoingDown
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
    [IsNoetherianRing R] [IsNoetherianRing T] [Module.Finite R T]
    [Algebra.HasGoingDown R T] (q : PrimeSpectrum T) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) := by
  -- Lemma 10.112.7 gives the fiber summand, and the finite fiber has dimension zero.
  calc
    ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
          ringKrullDim (fiberLocalRingAt R T q) :=
      ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
        q
    _ = ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) := by
      rw [ringKrullDim_fiberLocalRingAt_eq_zero_of_moduleFinite (R := R) (T := T) q]
      simp

/-- Helper for Chap10 Lemma 10 114 5: a polynomial ring over a field has the same dimension as
each of its maximal localizations. -/
private lemma ringKrullDim_mvPolynomial_eq_localizationAtMaximal
    {n : ℕ} (m : MaximalSpectrum (MvPolynomial (Fin n) k)) :
    ringKrullDim (MvPolynomial (Fin n) k) =
      ringKrullDim (Localization.AtPrime m.asIdeal) := by
  -- Both sides are the number of variables.
  calc
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
      simp
    _ = ringKrullDim (Localization.AtPrime m.asIdeal) :=
      (ringKrullDim_localizationAtMaximal_mvPolynomial (m := m)).symm

/-- Helper for Chap10 Lemma 10 114 5: a finite injective polynomial normalization reduces the
target equality to the polynomial-ring equality. -/
private lemma ringKrullDim_eq_localizationAtMaximal_of_finite_injective_mvPolynomial
    {n : ℕ} [IsDomain S] (g : MvPolynomial (Fin n) k →ₐ[k] S)
    (hg_inj : Function.Injective g) (hg_fin : g.Finite) (m : MaximalSpectrum S) :
    ringKrullDim S = ringKrullDim (Localization.AtPrime m.asIdeal) := by
  let A := MvPolynomial (Fin n) k
  letI : Algebra A S := g.toAlgebra
  have hFinite : Module.Finite A S := by
    simpa [A, AlgHom.Finite, RingHom.Finite] using hg_fin
  letI : Module.Finite A S := hFinite
  have hIntegral : Algebra.IsIntegral A S := inferInstance
  letI : Algebra.IsIntegral A S := hIntegral
  have hIntClosedA : IsIntegrallyClosed A := inferInstance
  letI : IsIntegrallyClosed A := hIntClosedA
  have hFaithful : FaithfulSMul A S :=
    (faithfulSMul_iff_algebraMap_injective A S).mpr (by
      simpa [A, RingHom.algebraMap_toAlgebra] using hg_inj)
  letI : FaithfulSMul A S := hFaithful
  have hNoethA : IsNoetherianRing A := inferInstance
  letI : IsNoetherianRing A := hNoethA
  have hNoethS : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  letI : IsNoetherianRing S := hNoethS
  have hGoingDown : Algebra.HasGoingDown A S := inferInstance
  letI : Algebra.HasGoingDown A S := hGoingDown
  let p : Ideal A := m.asIdeal.under A
  have hpMax : p.IsMaximal := by
    dsimp [p]
    infer_instance
  let pMax : MaximalSpectrum A := ⟨p, hpMax⟩
  have hglobal : ringKrullDim S = ringKrullDim A := by
    exact
      (ringKrullDim_eq_of_injective_algebraMap_of_isIntegral (R := A) (S := S)
        (by simpa [A, RingHom.algebraMap_toAlgebra] using hg_inj)).symm
  have hpoly : ringKrullDim A = ringKrullDim (Localization.AtPrime p) := by
    simpa [A, pMax] using ringKrullDim_mvPolynomial_eq_localizationAtMaximal (k := k) pMax
  have hlocal :
      ringKrullDim (Localization.AtPrime m.asIdeal) =
        ringKrullDim (Localization.AtPrime p) := by
    simpa [A, p] using
      ringKrullDim_localizationAtPrime_eq_under_of_moduleFinite_hasGoingDown
        (R := A) (T := S) m.toPrimeSpectrum
  calc
    ringKrullDim S = ringKrullDim A := hglobal
    _ = ringKrullDim (Localization.AtPrime p) := hpoly
    _ = ringKrullDim (Localization.AtPrime m.asIdeal) := hlocal.symm

/-- Helper for Chap10 Lemma 10 114 5: finite-type domains over a field have the same dimension
as each maximal localization. -/
private lemma finiteTypeDomain_ringKrullDim_eq_localizationAtMaximal
    (k : Type u) [Field k] [Algebra k S] [Algebra.FiniteType k S]
    [IsDomain S] (m : MaximalSpectrum S) :
    ringKrullDim S = ringKrullDim (Localization.AtPrime m.asIdeal) := by
  obtain ⟨n, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg k S
  exact ringKrullDim_eq_localizationAtMaximal_of_finite_injective_mvPolynomial
    (k := k) (S := S) g hg_inj hg_fin m

/-- Helper for Chap10 Lemma 10 114 5: every prime point of `Spec(S)` lies below a maximal point. -/
private lemma existsMaximalSpectrum_over (x : PrimeSpectrum S) :
    ∃ m : MaximalSpectrum S, x.asIdeal ≤ m.asIdeal := by
  -- Extend the proper prime ideal corresponding to `x` to a maximal ideal.
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal x.asIdeal x.2.1
  exact ⟨⟨M, hM⟩, hxM⟩

/-- Helper for Chap10 Lemma 10 114 5: the type of maximal ideals over a prime is nonempty. -/
private lemma nonemptyMaximalSpectrum_over (x : PrimeSpectrum S) :
    Nonempty { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal } := by
  -- Package the maximal ideal supplied by `existsMaximalSpectrum_over` as an element of the
  -- indexing subtype used in the infimum formula.
  obtain ⟨m, hm⟩ := existsMaximalSpectrum_over (S := S) x
  exact ⟨⟨m, hm⟩⟩

/-- Helper for Chap10 Lemma 10 114 5: specializing from `x` to a maximal point preserves
membership in irreducible components. -/
private lemma mem_irreducibleComponent_of_le_maximal
    {x : PrimeSpectrum S} {m : MaximalSpectrum S} (hxm : x.asIdeal ≤ m.asIdeal)
    (Z : irreducibleComponents (PrimeSpectrum S))
    (hxZ : x ∈ (Z : Set (PrimeSpectrum S))) :
    m.toPrimeSpectrum ∈ (Z : Set (PrimeSpectrum S)) := by
  -- Translate ideal inclusion to specialization and use closedness of irreducible components.
  have hspec : x ⤳ m.toPrimeSpectrum := by
    rw [← PrimeSpectrum.le_iff_specializes]
    simpa using hxm
  exact hspec.mem_closed
    (isClosed_of_mem_irreducibleComponents (Z : Set (PrimeSpectrum S)) Z.2) hxZ

/-- Helper for Chap10 Lemma 10 114 5: component dimensions through a prime are bounded by the
component dimensions through any maximal specialization. -/
private lemma iSup_topologicalKrullDim_components_through_le_of_le_maximal
    {x : PrimeSpectrum S} {m : MaximalSpectrum S} (hxm : x.asIdeal ≤ m.asIdeal) :
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        x ∈ (Z : Set (PrimeSpectrum S)) },
      topologicalKrullDim (Z : Set (PrimeSpectrum S))) ≤
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        m.toPrimeSpectrum ∈ (Z : Set (PrimeSpectrum S)) },
      topologicalKrullDim (Z : Set (PrimeSpectrum S))) := by
  -- Send every component through `x` to the same component viewed as one through `m`.
  refine iSup_le fun Z ↦ ?_
  let W : { Z : irreducibleComponents (PrimeSpectrum S) //
      m.toPrimeSpectrum ∈ (Z : Set (PrimeSpectrum S)) } :=
    ⟨Z.1, mem_irreducibleComponent_of_le_maximal hxm Z.1 Z.2⟩
  exact le_iSup_of_le W le_rfl

/-- Helper for Chap10 Lemma 10 114 5: equal component-containment predicates give equal
component-dimension suprema. -/
private lemma iSup_topologicalKrullDim_components_through_eq_of_iff
    {x y : PrimeSpectrum S}
    (hxy : ∀ Z : irreducibleComponents (PrimeSpectrum S),
      y ∈ (Z : Set (PrimeSpectrum S)) ↔ x ∈ (Z : Set (PrimeSpectrum S))) :
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        y ∈ (Z : Set (PrimeSpectrum S)) },
      topologicalKrullDim (Z : Set (PrimeSpectrum S))) =
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        x ∈ (Z : Set (PrimeSpectrum S)) },
      topologicalKrullDim (Z : Set (PrimeSpectrum S))) := by
  -- Reindex both suprema by the identity on underlying irreducible components.
  refine le_antisymm ?_ ?_
  · refine iSup_le fun Z ↦ ?_
    let W : { Z : irreducibleComponents (PrimeSpectrum S) //
        x ∈ (Z : Set (PrimeSpectrum S)) } := ⟨Z.1, (hxy Z.1).mp Z.2⟩
    exact le_iSup_of_le W le_rfl
  · refine iSup_le fun Z ↦ ?_
    let W : { Z : irreducibleComponents (PrimeSpectrum S) //
        y ∈ (Z : Set (PrimeSpectrum S)) } := ⟨Z.1, (hxy Z.1).mpr Z.2⟩
    exact le_iSup_of_le W le_rfl

/-- Helper for Chap10 Lemma 10 114 5: the component-neighborhood of `x` consists exactly of
points whose irreducible components all pass through `x`. -/
private lemma mem_componentNeighborhood_iff
    {X : Type u} [TopologicalSpace X] (x y : X) :
    y ∈ (((⋃₀ {Z : Set X | Z ∈ irreducibleComponents X ∧ x ∉ Z})ᶜ : Set X)) ↔
      ∀ Z : irreducibleComponents X, y ∈ (Z : Set X) → x ∈ (Z : Set X) := by
  -- Unpack the complement of the union of bad components into the equivalent universal
  -- component-containment statement.
  constructor
  · intro hy Z hyZ
    by_contra hxZ
    exact hy (Set.mem_sUnion.2 ⟨(Z : Set X), ⟨Z.2, hxZ⟩, hyZ⟩)
  · intro h hy_bad
    rcases Set.mem_sUnion.1 hy_bad with ⟨Z, hZbad, hyZ⟩
    exact hZbad.2 (h ⟨Z, hZbad.1⟩ hyZ)

/-- Helper for Chap10 Lemma 10 114 5: maximal ideals over a fixed maximal ideal form a
subsingleton indexing type. -/
private lemma maximalSpectrum_over_closedPoint_subsingleton (m : MaximalSpectrum S) :
    Subsingleton { n : MaximalSpectrum S // m.asIdeal ≤ n.asIdeal } := by
  -- Maximality forces every maximal ideal above `m.asIdeal` to be exactly `m.asIdeal`.
  refine ⟨fun a b ↦ Subtype.ext <| MaximalSpectrum.ext <| ?_⟩
  have ha : m.asIdeal = a.1.asIdeal :=
    Ideal.IsMaximal.eq_of_le m.isMaximal a.1.isMaximal.ne_top a.2
  have hb : m.asIdeal = b.1.asIdeal :=
    Ideal.IsMaximal.eq_of_le m.isMaximal b.1.isMaximal.ne_top b.2
  exact ha.symm.trans hb

/-- Helper for Chap10 Lemma 10 114 5: at a closed point the maximal-localization infimum
collapses to the corresponding single local ring. -/
private lemma iInf_ringKrullDim_localizationAtMaximal_over_closedPoint
    (m : MaximalSpectrum S) :
    (⨅ n : { n : MaximalSpectrum S // m.asIdeal ≤ n.asIdeal },
      ringKrullDim (Localization.AtPrime n.1.asIdeal)) =
    ringKrullDim (Localization.AtPrime m.asIdeal) := by
  -- Use the subsingleton indexing type, with `m` itself as the canonical index.
  letI : Subsingleton { n : MaximalSpectrum S // m.asIdeal ≤ n.asIdeal } :=
    maximalSpectrum_over_closedPoint_subsingleton m
  let e : { n : MaximalSpectrum S // m.asIdeal ≤ n.asIdeal } := ⟨m, le_rfl⟩
  simpa [e] using
    (ciInf_subsingleton e fun n ↦ ringKrullDim (Localization.AtPrime n.1.asIdeal))

omit k

/-- Helper for Chap10 Lemma 10 114 5: components through a point of `Spec S` are reindexed by
minimal primes below the corresponding prime ideal. -/
private theorem iSup_topologicalKrullDim_components_through_eq_iSup_zeroLocus_minimalPrimesBelow
    (x : PrimeSpectrum S) :
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S))) =
      ⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
        topologicalKrullDim (PrimeSpectrum.zeroLocus (q.1.1 : Set S)) := by
  -- Build the explicit correspondence `Z ↦ vanishingIdeal Z`, with inverse `q ↦ V(q)`.
  let e :
      { Z : irreducibleComponents (PrimeSpectrum S) // x ∈ (Z : Set (PrimeSpectrum S)) } ≃
        { q : minimalPrimes S // q.1 ≤ x.asIdeal } := by
    refine
      { toFun := fun Z => ?_
        invFun := fun q => ?_
        left_inv := ?_
        right_inv := ?_ }
    · refine ⟨⟨PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)), ?_⟩, ?_⟩
      · rw [PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
        rw [(isClosed_of_mem_irreducibleComponents
          (Z.1 : Set (PrimeSpectrum S)) Z.1.2).closure_eq]
        exact Z.1.2
      · intro a ha
        exact (PrimeSpectrum.mem_vanishingIdeal
          (Z.1 : Set (PrimeSpectrum S)) a).mp ha x Z.2
    · refine ⟨⟨PrimeSpectrum.zeroLocus (q.1.1 : Set S), ?_⟩, ?_⟩
      · rw [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents]
        rw [Ideal.IsPrime.radical (Ideal.minimalPrimes_isPrime q.1.2)]
        exact q.1.2
      · exact (PrimeSpectrum.mem_zeroLocus x (q.1.1 : Set S)).mpr q.2
    · intro Z
      apply Subtype.ext
      apply Subtype.ext
      dsimp
      -- The zero locus of the vanishing ideal is the closure, and components are closed.
      calc
        PrimeSpectrum.zeroLocus
            (PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)) : Set S) =
            closure (Z.1 : Set (PrimeSpectrum S)) :=
          PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _
        _ = (Z.1 : Set (PrimeSpectrum S)) :=
          (isClosed_of_mem_irreducibleComponents
            (Z.1 : Set (PrimeSpectrum S)) Z.1.2).closure_eq
    · intro q
      apply Subtype.ext
      apply Subtype.ext
      dsimp
      -- A minimal prime is radical, so `V(q)` has vanishing ideal exactly `q`.
      calc
        PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (q.1.1 : Set S)) =
            q.1.1.radical :=
          PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical q.1.1
        _ = q.1.1 :=
          Ideal.IsPrime.radical (Ideal.minimalPrimes_isPrime q.1.2)
  -- Reindex the supremum along this equivalence and normalize the surviving component.
  refine Equiv.iSup_congr e ?_
  intro Z
  dsimp [e]
  calc
    topologicalKrullDim
        (PrimeSpectrum.zeroLocus
          (PrimeSpectrum.vanishingIdeal (Z.1 : Set (PrimeSpectrum S)) : Set S)) =
        topologicalKrullDim (closure (Z.1 : Set (PrimeSpectrum S))) := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    _ = topologicalKrullDim (Z.1 : Set (PrimeSpectrum S)) := by
      rw [(isClosed_of_mem_irreducibleComponents
        (Z.1 : Set (PrimeSpectrum S)) Z.1.2).closure_eq]

/-- Helper for Chap10 Lemma 10 114 5: the component `V(q)` attached to a minimal prime has the
Krull dimension of the quotient ring `S ⧸ q`. -/
private theorem topologicalKrullDim_zeroLocus_minimalPrime_eq_ringKrullDim_quotient
    (q : minimalPrimes S) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (q.1 : Set S)) =
      ringKrullDim (S ⧸ q.1) := by
  -- The quotient spectrum is homeomorphic to `V(q)`, so topological and ring dimensions agree.
  have hhomeo :
      topologicalKrullDim (PrimeSpectrum (S ⧸ q.1)) =
        topologicalKrullDim (PrimeSpectrum.zeroLocus (q.1 : Set S)) := by
    simpa using
      IsHomeomorph.topologicalKrullDim_eq
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus q.1)
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus q.1).isHomeomorph
  rw [← hhomeo]
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (S ⧸ q.1)

/-- Helper for Chap10 Lemma 10 114 5: the prime of `S ⧸ q` corresponding to `x` when
`q` is a minimal prime below `x.asIdeal`. -/
private noncomputable def quotientPrimeOver
    (x : PrimeSpectrum S) (q : minimalPrimes S) (hqx : q.1 ≤ x.asIdeal) :
    PrimeSpectrum (S ⧸ q.1) :=
  (Ideal.primeSpectrumQuotientOrderIsoZeroLocus q.1).symm ⟨x, hqx⟩

/-- Helper for Chap10 Lemma 10 114 5: the quotient prime over `x` contracts back to
`x.asIdeal`. -/
private theorem quotientPrimeOver_comap_asIdeal
    (x : PrimeSpectrum S) (q : minimalPrimes S) (hqx : q.1 ≤ x.asIdeal) :
    Ideal.comap (Ideal.Quotient.mk q.1) (quotientPrimeOver x q hqx).asIdeal = x.asIdeal := by
  -- Apply the quotient-spectrum order isomorphism back to the named quotient prime.
  have hspec :
      (Ideal.primeSpectrumQuotientOrderIsoZeroLocus q.1) (quotientPrimeOver x q hqx) =
        ⟨x, hqx⟩ := by
    exact (Ideal.primeSpectrumQuotientOrderIsoZeroLocus q.1).apply_symm_apply ⟨x, hqx⟩
  exact congrArg (fun z : PrimeSpectrum.zeroLocus (R := S) (q.1 : Set S) => z.1.asIdeal) hspec

/-- Helper for Chap10 Lemma 10 114 5: the quotient prime over `x` is the image of `x.asIdeal`
under the quotient map. -/
private theorem quotientPrimeOver_asIdeal_eq_map
    (x : PrimeSpectrum S) (q : minimalPrimes S) (hqx : q.1 ≤ x.asIdeal) :
    (quotientPrimeOver x q hqx).asIdeal = x.asIdeal.map (Ideal.Quotient.mk q.1) := by
  -- Surjectivity of the quotient map makes equality of ideals equivalent after comapping.
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk q.1) Ideal.Quotient.mk_surjective
  rw [quotientPrimeOver_comap_asIdeal]
  rw [Ideal.comap_map_of_surjective]
  · rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact (sup_eq_left.mpr hqx).symm
  · exact Ideal.Quotient.mk_surjective

/-- Helper for Chap10 Lemma 10 114 5: over a maximal ideal, the quotient prime is maximal. -/
private theorem quotientPrimeOver_isMaximal
    (m : MaximalSpectrum S) (q : minimalPrimes S) (hqm : q.1 ≤ m.asIdeal) :
    (quotientPrimeOver m.toPrimeSpectrum q hqm).asIdeal.IsMaximal := by
  -- Rewrite the quotient prime as the image of `m.asIdeal`; maximality descends through the
  -- surjective quotient map because the kernel is contained in `m.asIdeal`.
  rw [quotientPrimeOver_asIdeal_eq_map]
  simpa using
    (Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk q.1) (m := m.asIdeal) Ideal.Quotient.mk_surjective
      (by simpa [Ideal.mk_ker] using hqm))

/-- Helper for Chap10 Lemma 10 114 5: quotient-prime height is bounded by the height of the
original prime. -/
private theorem quotientPrimeOver_height_le
    (x : PrimeSpectrum S) (q : { q : minimalPrimes S // q.1 ≤ x.asIdeal }) :
    (quotientPrimeOver x q.1 q.2).asIdeal.height ≤ x.asIdeal.height := by
  -- Embed the quotient spectrum as the zero locus and compare heights by strict monotonicity.
  let e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus q.1.1
  let f : PrimeSpectrum (S ⧸ q.1.1) → PrimeSpectrum S := fun y => (e y).1
  have hf : StrictMono f := by
    intro a b hab
    simpa [f] using e.strictMono hab
  have hheight :=
    Order.height_le_height_apply_of_strictMono f hf (quotientPrimeOver x q.1 q.2)
  have himage : f (quotientPrimeOver x q.1 q.2) = x := by
    apply PrimeSpectrum.ext
    exact quotientPrimeOver_comap_asIdeal (S := S) x q.1 q.2
  rw [himage] at hheight
  simpa [Ideal.height_eq_primeHeight, Ideal.primeHeight] using hheight

/-- Helper for Chap10 Lemma 10 114 5: every chain ending at `x` maps into a quotient component
over a minimal prime below its head. -/
private theorem ltSeries_length_le_iSup_quotientPrimeOver_height
    (x : PrimeSpectrum S) (l : LTSeries (PrimeSpectrum S)) (hlast : l.last = x) :
    (l.length : ℕ∞) ≤
      ⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
        (quotientPrimeOver x q.1 q.2).asIdeal.height := by
  -- Choose a minimal prime below the head of the chain; since the chain ends at `x`, this
  -- minimal prime also lies below `x.asIdeal`.
  obtain ⟨p, hp_min, hp_le_head⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := l.head.asIdeal) bot_le
  let qmin : minimalPrimes S := ⟨p, hp_min⟩
  have hq_le_x : qmin.1 ≤ x.asIdeal := by
    exact hp_le_head.trans (by simpa [hlast] using (l.head_le_last : l.head ≤ l.last))
  let qidx : { q : minimalPrimes S // q.1 ≤ x.asIdeal } := ⟨qmin, hq_le_x⟩
  let e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus qmin.1
  have hq_le_i (i : Fin (l.length + 1)) : qmin.1 ≤ (l i).asIdeal := by
    exact hp_le_head.trans (show l.head.asIdeal ≤ (l i).asIdeal from l.head_le i)
  -- Transport the whole chain into the quotient spectrum attached to the chosen minimal prime.
  let lq : LTSeries (PrimeSpectrum (S ⧸ qmin.1)) :=
    LTSeries.mk l.length
      (fun i => e.symm ⟨l i, hq_le_i i⟩)
      (fun i j hij => by
        apply e.symm.strictMono
        exact show (⟨l i, hq_le_i i⟩ :
            PrimeSpectrum.zeroLocus (R := S) (qmin.1 : Set S)) <
            ⟨l j, hq_le_i j⟩ from l.strictMono hij)
  have hlast_lq : lq.last = e.symm ⟨x, hq_le_x⟩ := by
    apply e.injective
    simpa [lq, e, RelSeries.last] using hlast
  have hlen : (l.length : ℕ∞) ≤ (e.symm ⟨x, hq_le_x⟩).asIdeal.height := by
    have h := Order.length_le_height_last (p := lq)
    rw [hlast_lq] at h
    simpa only [Ideal.height_eq_primeHeight, Ideal.primeHeight] using h
  -- The chosen quotient component is one of the terms of the supremum.
  exact le_trans hlen (by
    simpa [quotientPrimeOver, qidx, qmin, e] using
      (le_iSup (fun q : { q : minimalPrimes S // q.1 ≤ x.asIdeal } =>
        (quotientPrimeOver x q.1 q.2).asIdeal.height) qidx))

/-- Helper for Chap10 Lemma 10 114 5: quotient primes over all minimal components below `x`
recover exactly the height of `x`. -/
private theorem iSup_quotientPrimeOver_height_eq_height
    (x : PrimeSpectrum S) :
    (⨆ q : { q : minimalPrimes S // q.1 ≤ x.asIdeal },
        (quotientPrimeOver x q.1 q.2).asIdeal.height) = x.asIdeal.height := by
  -- The upper bound is functoriality of height under the quotient-spectrum embedding; the lower
  -- bound maps every chain ending at `x` into a suitable quotient component.
  refine le_antisymm ?_ ?_
  · exact iSup_le fun q => quotientPrimeOver_height_le (S := S) x q
  · rw [Ideal.height_eq_primeHeight, Ideal.primeHeight, Order.height_eq_iSup_last_eq]
    exact iSup₂_le fun l hlast =>
      ltSeries_length_le_iSup_quotientPrimeOver_height (S := S) x l hlast

/-- Helper for Chap10 Lemma 10 114 5: every point in the component-neighborhood of `x` has height
bounded by the supremum of the dimensions of the components passing through `x`. -/
private theorem primeHeight_le_iSup_components_through_of_mem_componentNeighborhood
    (x y : PrimeSpectrum S)
    (hy : y ∈
      (((⋃₀ {Z : Set (PrimeSpectrum S) |
        Z ∈ irreducibleComponents (PrimeSpectrum S) ∧ x ∉ Z})ᶜ :
          Set (PrimeSpectrum S)))) :
    ((y.asIdeal.height : ℕ∞) : WithBot ℕ∞) ≤
      ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
          x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S)) := by
  -- Rewrite the height of `y` as the supremum of quotient-prime heights over the minimal
  -- components below `y`.
  have hcomponents :=
    (mem_componentNeighborhood_iff (X := PrimeSpectrum S) x y).1 hy
  have hnonempty :
      Nonempty { q : minimalPrimes S // q.1 ≤ y.asIdeal } := by
    obtain ⟨p, hp_min, hp_le_y⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := y.asIdeal) bot_le
    exact ⟨⟨⟨p, hp_min⟩, hp_le_y⟩⟩
  letI : Nonempty { q : minimalPrimes S // q.1 ≤ y.asIdeal } := hnonempty
  calc
    ((y.asIdeal.height : ℕ∞) : WithBot ℕ∞) =
        (⨆ q : { q : minimalPrimes S // q.1 ≤ y.asIdeal },
          ((quotientPrimeOver y q.1 q.2).asIdeal.height : WithBot ℕ∞)) := by
      rw [← WithBot.coe_iSup (OrderTop.bddAbove
        (Set.range fun q : { q : minimalPrimes S // q.1 ≤ y.asIdeal } =>
          (quotientPrimeOver y q.1 q.2).asIdeal.height))]
      exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞))
        (iSup_quotientPrimeOver_height_eq_height (S := S) y).symm
    _ ≤ ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
          x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S)) := by
      refine iSup_le fun q ↦ ?_
      -- The minimal prime `q` gives the component `V(q)`, and neighborhood membership promotes
      -- its containment of `y` to containment of `x`.
      have hq_component :
          PrimeSpectrum.zeroLocus (q.1.1 : Set S) ∈
            irreducibleComponents (PrimeSpectrum S) := by
        rw [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents]
        rw [Ideal.IsPrime.radical (Ideal.minimalPrimes_isPrime q.1.2)]
        exact q.1.2
      have hy_component :
          y ∈ (PrimeSpectrum.zeroLocus (q.1.1 : Set S) : Set (PrimeSpectrum S)) :=
        (PrimeSpectrum.mem_zeroLocus y (q.1.1 : Set S)).mpr q.2
      have hx_component :
          x ∈ (PrimeSpectrum.zeroLocus (q.1.1 : Set S) : Set (PrimeSpectrum S)) :=
        hcomponents ⟨PrimeSpectrum.zeroLocus (q.1.1 : Set S), hq_component⟩ hy_component
      let Zthrough : { Z : irreducibleComponents (PrimeSpectrum S) //
          x ∈ (Z : Set (PrimeSpectrum S)) } :=
        ⟨⟨PrimeSpectrum.zeroLocus (q.1.1 : Set S), hq_component⟩, hx_component⟩
      calc
        ((quotientPrimeOver y q.1 q.2).asIdeal.height : WithBot ℕ∞) ≤
            ringKrullDim (S ⧸ q.1.1) := by
          simpa [Ideal.height_eq_primeHeight] using
            (Ideal.primeHeight_le_ringKrullDim
              (I := (quotientPrimeOver y q.1 q.2).asIdeal))
        _ = topologicalKrullDim (PrimeSpectrum.zeroLocus (q.1.1 : Set S)) := by
          exact (topologicalKrullDim_zeroLocus_minimalPrime_eq_ringKrullDim_quotient
            (S := S) q.1).symm
        _ ≤ ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
              x ∈ (Z : Set (PrimeSpectrum S)) },
            topologicalKrullDim (Z : Set (PrimeSpectrum S)) :=
          le_iSup_of_le Zthrough le_rfl

include k

/-- Helper for Chap10 Lemma 10 114 5: in the quotient by a minimal prime below a maximal ideal,
the quotient-domain dimension is the quotient-prime height. -/
private theorem ringKrullDim_minimalPrimeQuotient_eq_quotientPrimeOver_height
    (m : MaximalSpectrum S) (q : { q : minimalPrimes S // q.1 ≤ m.asIdeal }) :
    ringKrullDim (S ⧸ q.1.1) =
      ((quotientPrimeOver m.toPrimeSpectrum q.1 q.2).asIdeal.height : WithBot ℕ∞) := by
  -- Apply the finite-type domain theorem to the quotient component, then normalize the resulting
  -- maximal localization by the height formula.
  letI : q.1.1.IsPrime := Ideal.minimalPrimes_isPrime q.1.2
  letI : IsDomain (S ⧸ q.1.1) := Ideal.Quotient.isDomain q.1.1
  let mq : MaximalSpectrum (S ⧸ q.1.1) :=
    ⟨(quotientPrimeOver m.toPrimeSpectrum q.1 q.2).asIdeal,
      quotientPrimeOver_isMaximal (S := S) m q.1 q.2⟩
  calc
    ringKrullDim (S ⧸ q.1.1) =
        ringKrullDim (Localization.AtPrime mq.asIdeal) := by
      exact
        finiteTypeDomain_ringKrullDim_eq_localizationAtMaximal
          (k := k) (S := S ⧸ q.1.1) mq
    _ = ((quotientPrimeOver m.toPrimeSpectrum q.1 q.2).asIdeal.height : WithBot ℕ∞) := by
      simpa [mq] using
        IsLocalization.AtPrime.ringKrullDim_eq_height
          (quotientPrimeOver m.toPrimeSpectrum q.1 q.2).asIdeal
          (Localization.AtPrime (quotientPrimeOver m.toPrimeSpectrum q.1 q.2).asIdeal)

/-- Helper for Chap10 Lemma 10 114 5: the supremum of quotient-domain dimensions below a maximal
ideal is the height of that maximal ideal. -/
private theorem iSup_ringKrullDim_minimalPrimeQuotientsBelow_maximal_eq_height
    (m : MaximalSpectrum S) :
    (⨆ q : { q : minimalPrimes S // q.1 ≤ m.asIdeal }, ringKrullDim (S ⧸ q.1.1)) =
      (m.asIdeal.height : WithBot ℕ∞) := by
  -- Rewrite each quotient dimension to the height of the corresponding quotient prime, then use
  -- the pure order comparison of quotient-prime heights.
  calc
    (⨆ q : { q : minimalPrimes S // q.1 ≤ m.asIdeal }, ringKrullDim (S ⧸ q.1.1)) =
        ⨆ q : { q : minimalPrimes S // q.1 ≤ m.asIdeal },
          ((quotientPrimeOver m.toPrimeSpectrum q.1 q.2).asIdeal.height : WithBot ℕ∞) := by
      exact iSup_congr fun q =>
        ringKrullDim_minimalPrimeQuotient_eq_quotientPrimeOver_height (k := k) (S := S) m q
    _ = (m.asIdeal.height : WithBot ℕ∞) := by
      have hnonempty :
          Nonempty { q : minimalPrimes S // q.1 ≤ m.asIdeal } := by
        obtain ⟨p, hp_min, hp_le_m⟩ :=
          Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := m.asIdeal) bot_le
        exact ⟨⟨⟨p, hp_min⟩, hp_le_m⟩⟩
      letI : Nonempty { q : minimalPrimes S // q.1 ≤ m.asIdeal } := hnonempty
      rw [← WithBot.coe_iSup (OrderTop.bddAbove
        (Set.range fun q : { q : minimalPrimes S // q.1 ≤ m.asIdeal } =>
          (quotientPrimeOver m.toPrimeSpectrum q.1 q.2).asIdeal.height))]
      exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞))
        (iSup_quotientPrimeOver_height_eq_height (S := S) m.toPrimeSpectrum)

/-- Helper for Chap10 Lemma 10 114 5: at a maximal point, the local ring dimension is the
supremum of the dimensions of the irreducible components passing through that point. -/
private lemma ringKrullDim_localizationAtMaximal_eq_iSup_components_through
    (m : MaximalSpectrum S) :
    ringKrullDim (Localization.AtPrime m.asIdeal) =
      ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
          m.toPrimeSpectrum ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S)) := by
  -- Route correction: avoid the circular closed-point local-dimension bridge. Compute both sides
  -- through minimal-prime quotient domains and the localization-height owner.
  calc
    ringKrullDim (Localization.AtPrime m.asIdeal) = (m.asIdeal.height : WithBot ℕ∞) := by
      exact IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal
        (Localization.AtPrime m.asIdeal)
    _ = (⨆ q : { q : minimalPrimes S // q.1 ≤ m.asIdeal }, ringKrullDim (S ⧸ q.1.1)) :=
      (iSup_ringKrullDim_minimalPrimeQuotientsBelow_maximal_eq_height (k := k) (S := S) m).symm
    _ = (⨆ q : { q : minimalPrimes S // q.1 ≤ m.asIdeal },
          topologicalKrullDim (PrimeSpectrum.zeroLocus (q.1.1 : Set S))) := by
      exact iSup_congr fun q =>
        (topologicalKrullDim_zeroLocus_minimalPrime_eq_ringKrullDim_quotient (S := S) q.1).symm
    _ = (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
          m.toPrimeSpectrum ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S))) :=
      (iSup_topologicalKrullDim_components_through_eq_iSup_zeroLocus_minimalPrimesBelow
        (S := S) m.toPrimeSpectrum).symm

/-- Helper for Chap10 Lemma 10 114 5: a prime admits a maximal specialization with exactly the
same irreducible components through it. -/
private lemma existsMaximalSpectrum_over_with_same_components_through
    (x : PrimeSpectrum S) :
    ∃ m : MaximalSpectrum S, x.asIdeal ≤ m.asIdeal ∧
      ∀ Z : irreducibleComponents (PrimeSpectrum S),
        m.toPrimeSpectrum ∈ (Z : Set (PrimeSpectrum S)) ↔
          x ∈ (Z : Set (PrimeSpectrum S)) := by
  classical
  -- Work in the noetherian Jacobson spectrum of the finite-type algebra `S`.
  letI : IsNoetherianRing k := inferInstance
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k) (B := S)
  let U : Set (PrimeSpectrum S) :=
    (⋃₀ {Z : Set (PrimeSpectrum S) |
      Z ∈ irreducibleComponents (PrimeSpectrum S) ∧ x ∉ Z})ᶜ
  have hU_open : IsOpen U := by
    simpa [U] using
      IsDimensionFunction.isOpen_component_neighborhood (X := PrimeSpectrum S) x
  have hxU : x ∈ U := by
    -- A point is in its own component-neighborhood because every component containing it
    -- tautologically contains it.
    exact (mem_componentNeighborhood_iff (X := PrimeSpectrum S) x x).2 fun _ hxZ ↦ hxZ
  let L : Set (PrimeSpectrum S) := PrimeSpectrum.zeroLocus (x.asIdeal : Set S) ∩ U
  have hL_nonempty : L.Nonempty := by
    refine ⟨x, ?_⟩
    exact ⟨(PrimeSpectrum.mem_zeroLocus x (x.asIdeal : Set S)).mpr subset_rfl, hxU⟩
  have hL_locallyClosed : IsLocallyClosed L := by
    exact (PrimeSpectrum.isClosed_zeroLocus (x.asIdeal : Set S)).isLocallyClosed.inter
      hU_open.isLocallyClosed
  -- A Jacobson space has a closed point in every nonempty locally closed subset.
  obtain ⟨y, hyL, hyClosed⟩ := nonempty_inter_closedPoints hL_nonempty hL_locallyClosed
  have hyMax : y.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp
      (by simpa [closedPoints] using hyClosed)
  let m : MaximalSpectrum S := ⟨y.asIdeal, hyMax⟩
  have hxm : x.asIdeal ≤ m.asIdeal := by
    exact (PrimeSpectrum.mem_zeroLocus y (x.asIdeal : Set S)).mp hyL.1
  refine ⟨m, hxm, fun Z ↦ ?_⟩
  constructor
  · intro hmZ
    -- Membership of the chosen closed point in the component-neighborhood rules out any
    -- component through `m` which does not already contain `x`.
    by_contra hxZ
    exact hxZ
      ((mem_componentNeighborhood_iff (X := PrimeSpectrum S) x y).1 hyL.2 Z
        (by simpa [m] using hmZ))
  · intro hxZ
    -- Specialization from `x` to the chosen maximal point preserves membership in closed
    -- irreducible components.
    exact mem_irreducibleComponent_of_le_maximal hxm Z hxZ

/-- Helper for Chap10 Lemma 10 114 5: every open neighbourhood of a prime contains a maximal
specialization of that prime. -/
private lemma existsMaximalSpectrum_over_mem_openNhdsOf
    (x : PrimeSpectrum S) (U : OpenNhdsOf x) :
    ∃ m : MaximalSpectrum S,
      x.asIdeal ≤ m.asIdeal ∧ m.toPrimeSpectrum ∈ (U : Set (PrimeSpectrum S)) := by
  classical
  -- Finite type algebras over fields are noetherian Jacobson rings, so nonempty locally closed
  -- subsets of their spectra contain closed points.
  letI : IsNoetherianRing k := inferInstance
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k) (B := S)
  let L : Set (PrimeSpectrum S) := PrimeSpectrum.zeroLocus (x.asIdeal : Set S) ∩ (U : Set _)
  have hL_nonempty : L.Nonempty := by
    refine ⟨x, ?_⟩
    exact ⟨(PrimeSpectrum.mem_zeroLocus x (x.asIdeal : Set S)).mpr subset_rfl, U.2⟩
  have hL_locallyClosed : IsLocallyClosed L := by
    exact (PrimeSpectrum.isClosed_zeroLocus (x.asIdeal : Set S)).isLocallyClosed.inter
      U.1.2.isLocallyClosed
  -- Choose a closed point of `V(x.asIdeal) ∩ U`, then package its maximal ideal.
  obtain ⟨y, hyL, hyClosed⟩ := nonempty_inter_closedPoints hL_nonempty hL_locallyClosed
  have hyMax : y.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp
      (by simpa [closedPoints] using hyClosed)
  let m : MaximalSpectrum S := ⟨y.asIdeal, hyMax⟩
  have hxm : x.asIdeal ≤ m.asIdeal := by
    exact (PrimeSpectrum.mem_zeroLocus y (x.asIdeal : Set S)).mp hyL.1
  have hmU : m.toPrimeSpectrum ∈ (U : Set (PrimeSpectrum S)) := by
    simpa [m] using hyL.2
  exact ⟨m, hxm, hmU⟩

/-- Helper for Chap10 Lemma 10 114 5: the maximal-localization infimum is bounded above by
choosing a closed specialization with exactly the same components through it. -/
private lemma iInf_ringKrullDim_localizationAtMaximal_over_le_iSup_components_through
    (x : PrimeSpectrum S) :
    (⨅ m : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal },
      ringKrullDim (Localization.AtPrime m.1.asIdeal)) ≤
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        x ∈ (Z : Set (PrimeSpectrum S)) },
      topologicalKrullDim (Z : Set (PrimeSpectrum S))) := by
  -- Pick a closed point above `x` that introduces no new irreducible components, then evaluate
  -- the infimum at that index and rewrite its local dimension by the maximal comparison.
  obtain ⟨m, hxm, hcomponents⟩ :=
    existsMaximalSpectrum_over_with_same_components_through (k := k) (S := S) x
  let mOver : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal } := ⟨m, hxm⟩
  calc
    (⨅ n : { n : MaximalSpectrum S // x.asIdeal ≤ n.asIdeal },
        ringKrullDim (Localization.AtPrime n.1.asIdeal)) ≤
        ringKrullDim (Localization.AtPrime mOver.1.asIdeal) :=
      iInf_le (fun n : { n : MaximalSpectrum S // x.asIdeal ≤ n.asIdeal } ↦
        ringKrullDim (Localization.AtPrime n.1.asIdeal)) mOver
    _ =
        ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
            x ∈ (Z : Set (PrimeSpectrum S)) },
          topologicalKrullDim (Z : Set (PrimeSpectrum S)) := by
      rw [ringKrullDim_localizationAtMaximal_eq_iSup_components_through (k := k)]
      exact iSup_topologicalKrullDim_components_through_eq_of_iff hcomponents

/-- Helper for Chap10 Lemma 10 114 5: every maximal localization above `x` dominates the
component-dimension supremum through `x`. -/
private lemma iSup_components_through_le_iInf_ringKrullDim_localizationAtMaximal_over
    (x : PrimeSpectrum S) :
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        x ∈ (Z : Set (PrimeSpectrum S)) },
      topologicalKrullDim (Z : Set (PrimeSpectrum S))) ≤
    (⨅ m : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal },
      ringKrullDim (Localization.AtPrime m.1.asIdeal)) := by
  -- For each maximal point above `x`, specialization sends components through `x` to components
  -- through that maximal point, where the maximal comparison identifies the local ring dimension.
  refine le_iInf fun m ↦ ?_
  have hcomponent_le :=
    iSup_topologicalKrullDim_components_through_le_of_le_maximal (S := S) m.2
  rw [ringKrullDim_localizationAtMaximal_eq_iSup_components_through (k := k) m.1]
  exact hcomponent_le

/-- Helper for Chap10 Lemma 10 114 5: the infimum of maximal-localization dimensions over the
maximal ideals above a point is the component-dimension supremum through that point. -/
private lemma iInf_ringKrullDim_localizationAtMaximal_over_eq_iSup_components_through
    (x : PrimeSpectrum S) :
    (⨅ m : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal },
      ringKrullDim (Localization.AtPrime m.1.asIdeal)) =
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        x ∈ (Z : Set (PrimeSpectrum S)) },
      topologicalKrullDim (Z : Set (PrimeSpectrum S))) := by
  -- Compare every maximal-localization term to the component supremum, then evaluate the
  -- infimum at a closed point with no extra components.
  exact le_antisymm
    (iInf_ringKrullDim_localizationAtMaximal_over_le_iSup_components_through (k := k) x)
    (iSup_components_through_le_iInf_ringKrullDim_localizationAtMaximal_over (k := k) x)

omit k

include k

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 114 5: a point belongs to its own component-neighborhood. -/
private lemma self_mem_componentNeighborhood (x : PrimeSpectrum S) :
    x ∈ (((⋃₀ {Z : Set (PrimeSpectrum S) |
      Z ∈ irreducibleComponents (PrimeSpectrum S) ∧ x ∉ Z})ᶜ :
        Set (PrimeSpectrum S))) := by
  -- Every irreducible component containing `x` contains `x`, so no excluded component contains it.
  exact (mem_componentNeighborhood_iff (X := PrimeSpectrum S) x x).2 fun _ hxZ ↦ hxZ

/-- Helper for Chap10 Lemma 10 114 5: the component-neighborhood of a point is open. -/
private lemma isOpen_componentNeighborhood_prime (x : PrimeSpectrum S) :
    IsOpen (((⋃₀ {Z : Set (PrimeSpectrum S) |
      Z ∈ irreducibleComponents (PrimeSpectrum S) ∧ x ∉ Z})ᶜ :
        Set (PrimeSpectrum S))) := by
  -- Finite type over a field supplies the noetherian hypotheses for the component-neighborhood
  -- openness theorem.
  letI : IsNoetherianRing k := inferInstance
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  simpa using IsDimensionFunction.isOpen_component_neighborhood (X := PrimeSpectrum S) x

/-- Helper for Chap10 Lemma 10 114 5: the component-neighborhood as an open neighbourhood. -/
private noncomputable def componentNeighborhoodOpenNhdsOf (x : PrimeSpectrum S) :
    OpenNhdsOf x :=
  ⟨⟨(((⋃₀ {Z : Set (PrimeSpectrum S) |
      Z ∈ irreducibleComponents (PrimeSpectrum S) ∧ x ∉ Z})ᶜ :
        Set (PrimeSpectrum S))), isOpen_componentNeighborhood_prime (k := k) (S := S) x⟩,
    self_mem_componentNeighborhood (S := S) x⟩

/-- Helper for Chap10 Lemma 10 114 5: the component-neighborhood gives the standard upper bound
for the local Krull dimension at a point. -/
private lemma topologicalKrullDimAt_le_componentNeighborhood (x : PrimeSpectrum S) :
    topologicalKrullDimAt x ≤
      topologicalKrullDim (componentNeighborhoodOpenNhdsOf (k := k) (S := S) x) := by
  -- The component-neighborhood is one of the open neighbourhoods in the infimum defining the
  -- local Krull dimension.
  exact topologicalKrullDimAt_le x (componentNeighborhoodOpenNhdsOf (k := k) (S := S) x)

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 114 5: an open subspace of `PrimeSpectrum S` has topological
Krull dimension equal to the Krull dimension of its inherited prime-order subtype. -/
private lemma topologicalKrullDim_open_eq_krullDim_points
    (U : Opens (PrimeSpectrum S)) :
    topologicalKrullDim U = Order.krullDim U := by
  -- The generic-point equivalence identifies irreducible closed subsets of the open subspace with
  -- points of the open subspace, with the order dual to the inherited prime order.
  letI : QuasiSober U := U.isOpenEmbedding'.quasiSober
  let e : U ≃o (IrreducibleCloseds U)ᵒᵈ :=
    { __ := irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
      map_rel_iff' := fun {p q} =>
        (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans
          ((subtype_specializes_iff p q).trans
            (PrimeSpectrum.le_iff_specializes p.1 q.1).symm) }
  rw [topologicalKrullDim]
  calc
    Order.krullDim (IrreducibleCloseds U) =
        Order.krullDim ((IrreducibleCloseds U)ᵒᵈ) := by
      exact (Order.krullDim_orderDual (α := IrreducibleCloseds U)).symm
    _ = Order.krullDim U := by
      exact (Order.krullDim_eq_of_orderIso e).symm

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 114 5: an open neighbourhood of a point in `PrimeSpectrum S` has
topological Krull dimension equal to the Krull dimension of its inherited prime-order subtype. -/
private lemma topologicalKrullDim_openNhdsOf_eq_krullDim_points
    (x : PrimeSpectrum S) (U : OpenNhdsOf x) :
    topologicalKrullDim U = Order.krullDim U := by
  -- This is the same generic-point comparison as for `Opens`, stated for the neighbourhood
  -- subtype used by `topologicalKrullDimAt`.
  letI : QuasiSober U := U.toOpens.isOpenEmbedding'.quasiSober
  let e : U ≃o (IrreducibleCloseds U)ᵒᵈ :=
    { __ := irreducibleSetEquivPoints.toEquiv.symm.trans OrderDual.toDual
      map_rel_iff' := fun {p q} =>
        (RelIso.symm irreducibleSetEquivPoints).map_rel_iff.trans
          ((subtype_specializes_iff p q).trans
            (PrimeSpectrum.le_iff_specializes p.1 q.1).symm) }
  rw [topologicalKrullDim]
  calc
    Order.krullDim (IrreducibleCloseds U) =
        Order.krullDim ((IrreducibleCloseds U)ᵒᵈ) := by
      exact (Order.krullDim_orderDual (α := IrreducibleCloseds U)).symm
    _ = Order.krullDim U := by
      exact (Order.krullDim_eq_of_orderIso e).symm

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 114 5: an open subset of `Spec S` containing a prime also contains
all smaller primes in the specialization order. -/
private lemma mem_open_of_le_of_mem_primeSpectrum
    (U : Opens (PrimeSpectrum S)) {z y : PrimeSpectrum S}
    (hzy : z ≤ y) (hy : y ∈ (U : Set (PrimeSpectrum S))) :
    z ∈ (U : Set (PrimeSpectrum S)) := by
  -- Convert the ideal-order comparison to specialization and use the defining stability of opens
  -- under generization.
  exact (PrimeSpectrum.le_iff_specializes z y).mp hzy |>.mem_open U.2 hy

omit k [Field k] [Algebra k S] [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 114 5: the height of a prime contained in an open subspace is
bounded by the topological Krull dimension of that open subspace. -/
private lemma primeHeight_le_topologicalKrullDim_open_of_mem
    (U : Opens (PrimeSpectrum S)) (y : PrimeSpectrum S)
    (hy : y ∈ (U : Set (PrimeSpectrum S))) :
    ((y.asIdeal.height : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim U := by
  -- Embed the whole interval of primes below `y` into `U`; openness supplies the membership of
  -- every point in the interval.
  let f : Set.Iic y → U := fun z =>
    ⟨z.1, mem_open_of_le_of_mem_primeSpectrum U z.2 hy⟩
  have hf : StrictMono f := by
    intro a b hab
    simpa [f] using hab
  have hdim_le : Order.krullDim (Set.Iic y) ≤ Order.krullDim U :=
    Order.krullDim_le_of_strictMono f hf
  calc
    ((y.asIdeal.height : ℕ∞) : WithBot ℕ∞) = ((Order.height y : ℕ∞) : WithBot ℕ∞) := by
      rw [Ideal.height_eq_primeHeight, Ideal.primeHeight]
    _ = Order.krullDim (Set.Iic y) := by
      exact Order.height_eq_krullDim_Iic y
    _ ≤ Order.krullDim U := hdim_le
    _ = topologicalKrullDim U :=
      (topologicalKrullDim_open_eq_krullDim_points U).symm

/-- Helper for Chap10 Lemma 10 114 5: the component-neighborhood has dimension at most the
supremum of the dimensions of the irreducible components passing through the base point. -/
private lemma topologicalKrullDim_componentNeighborhood_le_iSup_components_through
    (x : PrimeSpectrum S) :
    topologicalKrullDim (componentNeighborhoodOpenNhdsOf (k := k) (S := S) x) ≤
      ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
          x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S)) := by
  -- Rewrite the open subspace dimension as the Krull dimension of its points, then bound every
  -- point-height using the component-neighborhood height estimate proved above.
  rw [topologicalKrullDim_openNhdsOf_eq_krullDim_points]
  rw [Order.krullDim_eq_iSup_height]
  refine iSup_le fun y ↦ ?_
  have hheight_le : Order.height y ≤ Order.height (y : PrimeSpectrum S) := by
    exact Order.height_le_height_apply_of_strictMono
      (fun z : componentNeighborhoodOpenNhdsOf (k := k) (S := S) x => (z : PrimeSpectrum S))
      (fun _ _ h ↦ h) y
  have hglobal :
      ((Order.height (y : PrimeSpectrum S) : ℕ∞) : WithBot ℕ∞) ≤
        ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
            x ∈ (Z : Set (PrimeSpectrum S)) },
          topologicalKrullDim (Z : Set (PrimeSpectrum S)) := by
    calc
      ((Order.height (y : PrimeSpectrum S) : ℕ∞) : WithBot ℕ∞) =
          ((y.1.asIdeal.height : ℕ∞) : WithBot ℕ∞) := by
        rw [Ideal.height_eq_primeHeight, Ideal.primeHeight]
      _ ≤ ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
            x ∈ (Z : Set (PrimeSpectrum S)) },
          topologicalKrullDim (Z : Set (PrimeSpectrum S)) :=
        primeHeight_le_iSup_components_through_of_mem_componentNeighborhood
          (S := S) x y.1 y.2
  exact (WithBot.coe_le_coe.mpr hheight_le).trans hglobal

/-- Helper for Chap10 Lemma 10 114 5: every open neighbourhood of a point has dimension at least
the supremum of the dimensions of the irreducible components through that point. -/
private lemma iSup_components_through_le_topologicalKrullDim_openNhdsOf
    (x : PrimeSpectrum S) (U : OpenNhdsOf x) :
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        x ∈ (Z : Set (PrimeSpectrum S)) },
      topologicalKrullDim (Z : Set (PrimeSpectrum S))) ≤ topologicalKrullDim U := by
  -- Choose a closed specialization inside the open neighbourhood, compare components through `x`
  -- with components through that closed point, and then use the open height bridge.
  obtain ⟨m, hxm, hmU⟩ := existsMaximalSpectrum_over_mem_openNhdsOf (k := k) (S := S) x U
  calc
    (⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
        x ∈ (Z : Set (PrimeSpectrum S)) },
      topologicalKrullDim (Z : Set (PrimeSpectrum S))) ≤
        ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) //
            m.toPrimeSpectrum ∈ (Z : Set (PrimeSpectrum S)) },
          topologicalKrullDim (Z : Set (PrimeSpectrum S)) :=
      iSup_topologicalKrullDim_components_through_le_of_le_maximal (S := S) hxm
    _ = ringKrullDim (Localization.AtPrime m.asIdeal) := by
      exact (ringKrullDim_localizationAtMaximal_eq_iSup_components_through
        (k := k) (S := S) m).symm
    _ = ((m.asIdeal.height : ℕ∞) : WithBot ℕ∞) := by
      exact IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal
        (Localization.AtPrime m.asIdeal)
    _ ≤ topologicalKrullDim U :=
      primeHeight_le_topologicalKrullDim_open_of_mem (S := S) U.1 m.toPrimeSpectrum hmU

/-- Helper for Chap10 Lemma 10 114 5: for finite type affine spectra over a field, local Krull
dimension at a point is the supremum of dimensions of the irreducible components containing that
point. -/
private lemma topologicalKrullDimAt_eq_iSup_components_through_of_finiteType
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) // x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S)) := by
  -- Route correction: the previous noetherian-space helper is false in that generality
  -- (for example, a generic point of a two-point noetherian local spectrum can have a smaller
  -- open neighbourhood). The remaining target-specific gap is the finite-type/Jacobson
  -- topological local-component formula.
  -- The component-neighborhood gives the upper bound; every open neighbourhood gives the lower
  -- bound after choosing a maximal specialization inside it.
  refine le_antisymm ?_ ?_
  · exact (topologicalKrullDimAt_le_componentNeighborhood (k := k) (S := S) x).trans
      (topologicalKrullDim_componentNeighborhood_le_iSup_components_through
        (k := k) (S := S) x)
  · rw [topologicalKrullDimAt]
    exact le_iInf fun U ↦
      iSup_components_through_le_topologicalKrullDim_openNhdsOf
        (k := k) (S := S) x U

/- 
Domain-style sampling for local Krull dimension on affine schemes of finite type over a field:
- primary domain: local dimension in `Spec(S)`, compared both with irreducible components through a
  point and with localizations at maximal ideals above that point;
- sampled owner declarations of the same kind:
  `topologicalKrullDimAt`,
  `PrimeSpectrum.localizationAtPrimeIrreducibleComponents`,
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`;
- best owner abstraction: the local dimension owner is `topologicalKrullDimAt`, while irreducible
  components should be indexed through the canonical owner subtype `irreducibleComponents
  (PrimeSpectrum S)` rather than through a parallel raw-set wrapper;
- primitive data: the point `x : PrimeSpectrum S`;
- derived API: the supremum formula over irreducible components through `x` and the infimum formula
  over maximal localizations above `x`.

Source/core/bridge triage:
* `source-facing`: the two textbook formulas for the local Krull dimension at `x`;
* `core/canonical`: `topologicalKrullDimAt`, `irreducibleComponents (PrimeSpectrum S)`,
  `MaximalSpectrum S`, and the localization owner `Localization.AtPrime`;
* `bridge/view`: `PrimeSpectrum.localizationAtPrimeIrreducibleComponents` and the ring/topological
  Krull-dimension comparison on spectra.

This file should expose only those source-facing formulas, written against the existing owner
abstractions, rather than introducing parallel wrappers for components-through-`x` or maximal
ideals above `x`.
-/

-- Proof sketch: remove the irreducible components not containing `x` and work on the resulting
-- open neighbourhood of `x`. On every smaller open neighbourhood, the surviving irreducible
-- components are precisely the intersections with those components through `x`, and each such
-- intersection has the same Krull dimension as the ambient component. This identifies the local
-- dimension at `x` with the maximum of the dimensions of the irreducible components passing
-- through `x`.
include k

/-- Chap10 Lemma 10 114 5: if `S` is a finite type `k`-algebra and `x : PrimeSpectrum S` is the
point of `X = Spec(S)` corresponding to a prime ideal `𝔭 ⊂ S`, then the local Krull dimension
`topologicalKrullDimAt x` equals the supremum, hence the
maximum, of the Krull dimensions of the irreducible components of `X` containing `x`. -/
@[stacks 00OT]
theorem topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ⨆ Z : { Z : irreducibleComponents (PrimeSpectrum S) // x ∈ (Z : Set (PrimeSpectrum S)) },
        topologicalKrullDim (Z : Set (PrimeSpectrum S)) := by
  -- Specialize the noetherian topological component formula to the affine finite-type spectrum.
  letI : IsNoetherianRing k := inferInstance
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  exact topologicalKrullDimAt_eq_iSup_components_through_of_finiteType (k := k) (S := S) x

-- Proof sketch: for each maximal ideal `m` containing `x.asIdeal`, the local ring `Sₘ` has
-- Krull dimension equal to the maximum of the dimensions of the irreducible components through the
-- corresponding closed point. Choosing a closed point of `V(x.asIdeal)` outside the union of the
-- components not containing `x` ensures that exactly the components through `x` occur, so this
-- common maximum is also the minimum of the dimensions of the localizations `Sₘ` with
-- `x.asIdeal ≤ m.asIdeal`.
/-- The local Krull dimension at a point of `Spec(S)` is the infimum, hence the minimum, of the
Krull dimensions of the localizations `Sₘ` at maximal ideals `m` containing `x.asIdeal`. -/
theorem topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over
    (x : PrimeSpectrum S) :
    topologicalKrullDimAt x =
      ⨅ m : { m : MaximalSpectrum S // x.asIdeal ≤ m.asIdeal },
        ringKrullDim (Localization.AtPrime m.1.asIdeal) := by
  -- Reduce both sides to the common component-supremum normal form through `x`.
  rw [topologicalKrullDimAt_eq_iSup_topologicalKrullDim_irreducibleComponents_through
    (k := k) (S := S) x]
  exact
    (iInf_ringKrullDim_localizationAtMaximal_over_eq_iSup_components_through
      (k := k) (S := S) x).symm

end
