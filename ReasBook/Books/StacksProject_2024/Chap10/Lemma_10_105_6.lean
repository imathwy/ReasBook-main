import Mathlib.Data.List.TFAE
import stacks_project.Chap10.Lemma_10_26_3
import stacks_project.Chap10.Lemma_10_105_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open TopologicalSpace PrimeSpectrum IsLocalization.AtPrime

universe u v

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace (PrimeSpectrum R)` from `Chap05/Definition_5_11_4`
- ring owner: `IsCatenaryRing R` from `Lemma_10_105_2`
- universal owner: `UniversallyCatenaryRing R` from `Definition_10_105_3`
- localization bridge: `localization_isCatenaryRing` and
  `localization_universallyCatenaryRing` from `Lemma_10_105_4`

Layer triage:
- `source-facing`: Lemma 10.105.6 records the prime-local and maximal-local TFAE criteria
- `core/canonical`: `IsCatenaryRing` and `UniversallyCatenaryRing`
- `bridge/view`: the localization predicates below are derived from the canonical owner instances

Primitive data already belongs to the upstream owner abstractions, so this file should only expose
the TFAE bridge and should not duplicate the catenary owner definitions locally.
-/

/-- Helper for Lemma 10.105.6: an order isomorphism restricts to the corresponding closed
intervals. -/
private noncomputable def orderIso_interval {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o β) (a b : α) : Set.Icc a b ≃o Set.Icc (e a) (e b) where
  toFun x := ⟨e x.1, e.monotone x.2.1, e.monotone x.2.2⟩
  invFun y := ⟨e.symm y.1, by
    simpa using e.symm.monotone y.2.1, by
    simpa using e.symm.monotone y.2.2⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_rel_iff' := by
    intro x y
    simpa using e.le_iff_le

/-- Helper for Lemma 10.105.6: forgetting a subtype condition identifies the corresponding
interval in the subtype with the ambient interval. -/
private noncomputable def subtype_interval_orderIso {α : Type*} [Preorder α]
    {P : α → Prop} {a b : α} (ha : P a) (hb : P b)
    (hP : ∀ ⦃x : α⦄, a ≤ x → x ≤ b → P x) :
    Set.Icc (⟨a, ha⟩ : { x : α // P x }) ⟨b, hb⟩ ≃o Set.Icc a b where
  toFun x := ⟨x.1.1, x.2.1, x.2.2⟩
  invFun x := ⟨⟨x.1, hP x.2.1 x.2.2⟩, x.2.1, x.2.2⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
  map_rel_iff' := by
    intro x y
    rfl

/-- Helper for Lemma 10.105.6: catenarity transports across ring equivalences. -/
private theorem isCatenaryRing_of_ringEquiv {A : Type v} {B : Type v}
    [CommRing A] [CommRing B] (e : A ≃+* B) [IsCatenaryRing A] :
    IsCatenaryRing B := by
  -- Transport the catenary-space structure through the induced homeomorphism on spectra.
  simpa [IsCatenaryRing] using
    (PrimeSpectrum.homeomorphOfRingEquiv e).catenarySpace

/-- Helper for Lemma 10.105.6: irreducible closed subsets of `Spec(R_𝔭)` identify with ambient
irreducible closed subsets of `Spec R` containing `𝔭`. -/
private noncomputable def localizationAtPrimeIrreducibleClosedsSubtypeOrderIso
    (p : PrimeSpectrum R) :
    IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) ≃o
      { Z : IrreducibleCloseds (PrimeSpectrum R) //
        p ∈ (Z : Set (PrimeSpectrum R)) } :=
  ((PrimeSpectrum.pointsEquivIrreducibleCloseds (Localization.AtPrime p.asIdeal)).symm.trans
    (PrimeSpectrum.localizationAtPrimeIrreducibleCloseds p)).dual

/-- Helper for Lemma 10.105.6: the localization preimages of comparable irreducible closed sets
remain comparable. -/
private theorem localizationAtPrime_preimage_le (p : PrimeSpectrum R)
    {T T' : IrreducibleCloseds (PrimeSpectrum R)}
    (hpT : p ∈ (T : Set (PrimeSpectrum R)))
    (hpT' : p ∈ (T' : Set (PrimeSpectrum R)))
    (hTT' : T ≤ T') :
    (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T, hpT⟩ ≤
      (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T', hpT'⟩ := by
  -- Compare in the subtype first, then transport back through the order isomorphism.
  exact
    (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm.monotone hTT'

/-- Helper for Lemma 10.105.6: localizing at a point of the smaller irreducible closed set
preserves the codimension of the interval. -/
private theorem localizationAtPrime_codim_transport (p : PrimeSpectrum R)
    {T T' : IrreducibleCloseds (PrimeSpectrum R)}
    (hpT : p ∈ (T : Set (PrimeSpectrum R)))
    (hpT' : p ∈ (T' : Set (PrimeSpectrum R)))
    (hTT' : T ≤ T') :
    codimBetween
        ((localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T, hpT⟩)
        ((localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T', hpT'⟩)
        (localizationAtPrime_preimage_le (R := R) p hpT hpT' hTT') =
      codimBetween T T' hTT' := by
  let e := localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p
  let TU : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) := e.symm ⟨T, hpT⟩
  let T'U : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) := e.symm ⟨T', hpT'⟩
  let eSub :
      Set.Icc (⟨T, hpT⟩ : { Z : IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ (Z : Set (PrimeSpectrum R)) }) ⟨T', hpT'⟩ ≃o
        Set.Icc T T' :=
    subtype_interval_orderIso
      (P := fun Z : IrreducibleCloseds (PrimeSpectrum R) ↦ p ∈ (Z : Set (PrimeSpectrum R)))
      (a := T) (b := T') hpT hpT' fun {_} hTZ _ ↦ hTZ hpT
  -- Compare both codimensions through the Krull dimensions of the corresponding intervals.
  apply WithBot.coe_injective
  have heTU :
      e TU =
        (⟨T, hpT⟩ : { Z : IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ (Z : Set (PrimeSpectrum R)) }) := by
    simp [e, TU]
  have heT'U :
      e T'U =
        (⟨T', hpT'⟩ : { Z : IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ (Z : Set (PrimeSpectrum R)) }) := by
    simp [e, T'U]
  calc
    codimBetween TU T'U (localizationAtPrime_preimage_le (R := R) p hpT hpT' hTT') =
        Order.krullDim (Set.Icc TU T'U) :=
      codimBetween_eq_krullDim _
    _ = Order.krullDim (Set.Icc (e TU) (e T'U)) :=
      Order.krullDim_eq_of_orderIso (orderIso_interval e TU T'U)
    _ =
        Order.krullDim
          (Set.Icc
            (⟨T, hpT⟩ : { Z : IrreducibleCloseds (PrimeSpectrum R) //
              p ∈ (Z : Set (PrimeSpectrum R)) })
            ⟨T', hpT'⟩) := by
      rw [heTU, heT'U]
    _ = Order.krullDim (Set.Icc T T') :=
      Order.krullDim_eq_of_orderIso eSub
    _ = codimBetween T T' hTT' :=
      (codimBetween_eq_krullDim _).symm

/-- Helper for Lemma 10.105.6: if every prime localization is catenary, then `R` is catenary. -/
private theorem isCatenaryRing_of_forall_prime_localizations
    (hlocal : ∀ p : PrimeSpectrum R, IsCatenaryRing (Localization.AtPrime p.asIdeal)) :
    IsCatenaryRing R := by
  rw [isCatenaryRing_iff_catenarySpace_primeSpectrum]
  rw [catenarySpace_iff_finite_codimBetween_and_codimBetween_additive]
  refine ⟨?_, ?_⟩
  · intro T T' hTT'
    -- Choose a point of the smaller irreducible closed set so both ends of the interval contain it.
    obtain ⟨p, hpT⟩ := T.isIrreducible.nonempty
    have hpT' : p ∈ (T' : Set (PrimeSpectrum R)) := hTT' hpT
    letI : IsCatenaryRing (Localization.AtPrime p.asIdeal) := hlocal p
    let TU : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) :=
      (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T, hpT⟩
    let T'U : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) :=
      (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T', hpT'⟩
    let hTUU : TU ≤ T'U :=
      localizationAtPrime_preimage_le (R := R) p hpT hpT' hTT'
    have hcodim :
        codimBetween TU T'U hTUU = codimBetween T T' hTT' := by
      simpa [TU, T'U, hTUU] using
        localizationAtPrime_codim_transport (R := R) p hpT hpT' hTT'
    -- Apply catenarity in the chosen prime localization and transport the codimension back.
    have hfinite : codimBetween TU T'U hTUU < ⊤ :=
      CatenarySpace.finite_codimBetween hTUU
    simpa [hcodim] using hfinite
  · intro T T' T'' hTT' hT'T''
    -- The same point of the smallest irreducible closed set lies in the whole interval.
    obtain ⟨p, hpT⟩ := T.isIrreducible.nonempty
    have hpT' : p ∈ (T' : Set (PrimeSpectrum R)) := hTT' hpT
    have hpT'' : p ∈ (T'' : Set (PrimeSpectrum R)) := hT'T'' hpT'
    letI : IsCatenaryRing (Localization.AtPrime p.asIdeal) := hlocal p
    let TU : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) :=
      (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T, hpT⟩
    let T'U : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) :=
      (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T', hpT'⟩
    let T''U : IrreducibleCloseds (PrimeSpectrum (Localization.AtPrime p.asIdeal)) :=
      (localizationAtPrimeIrreducibleClosedsSubtypeOrderIso (R := R) p).symm ⟨T'', hpT''⟩
    let hTT'U : TU ≤ T'U :=
      localizationAtPrime_preimage_le (R := R) p hpT hpT' hTT'
    let hT'T''U : T'U ≤ T''U :=
      localizationAtPrime_preimage_le (R := R) p hpT' hpT'' hT'T''
    let hTT''U : TU ≤ T''U :=
      localizationAtPrime_preimage_le (R := R) p hpT hpT'' (hTT'.trans hT'T'')
    have hcodim01 :
        codimBetween TU T'U hTT'U = codimBetween T T' hTT' := by
      simpa [TU, T'U, hTT'U] using
        localizationAtPrime_codim_transport (R := R) p hpT hpT' hTT'
    have hcodim12 :
        codimBetween T'U T''U hT'T''U = codimBetween T' T'' hT'T'' := by
      simpa [T'U, T''U, hT'T''U] using
        localizationAtPrime_codim_transport (R := R) p hpT' hpT'' hT'T''
    have hcodim02 :
        codimBetween TU T''U hTT''U = codimBetween T T'' (hTT'.trans hT'T'') := by
      simpa [TU, T''U, hTT''U] using
        localizationAtPrime_codim_transport (R := R) p hpT hpT'' (hTT'.trans hT'T'')
    -- Additivity holds in the localization and therefore in the original interval.
    have hadd :
        codimBetween TU T''U hTT''U =
          codimBetween TU T'U hTT'U + codimBetween T'U T''U hT'T''U :=
      CatenarySpace.codimBetween_additive hTT'U hT'T''U
    simpa [hcodim01, hcodim12, hcodim02] using hadd

/-- Helper for Lemma 10.105.6: for `𝔭 ⊆ 𝔪`, this is the corresponding prime of `Spec(R_𝔪)`. -/
private noncomputable abbrev localization_prime_of_le_maximal
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p ≤ m.toPrimeSpectrum) :
    PrimeSpectrum (Localization.AtPrime m.asIdeal) :=
  (IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime m.asIdeal) m.asIdeal).symm
    ⟨p, hpm⟩

/-- Helper for Lemma 10.105.6: the prime chosen in `Spec(R_𝔪)` contracts back to `𝔭`. -/
private theorem localization_prime_of_le_maximal_comap
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p ≤ m.toPrimeSpectrum) :
    PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m.asIdeal))
      (localization_prime_of_le_maximal (R := R) p m hpm) = p := by
  -- Unpack the prime-spectrum order isomorphism defining the point of `Spec(R_𝔪)`.
  change
    ((IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime m.asIdeal) m.asIdeal)
      (localization_prime_of_le_maximal (R := R) p m hpm)).1 = p
  simp [localization_prime_of_le_maximal]

/-- Helper for Lemma 10.105.6: the corresponding prime of `Spec(R_𝔪)` has contracted ideal
`𝔭.asIdeal`. -/
private theorem localization_prime_of_le_maximal_comap_asIdeal
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p ≤ m.toPrimeSpectrum) :
    Ideal.comap (algebraMap R (Localization.AtPrime m.asIdeal))
      (localization_prime_of_le_maximal (R := R) p m hpm).asIdeal = p.asIdeal := by
  -- Pass from the prime-spectrum equality to the underlying ideal equality.
  simpa [PrimeSpectrum.comap_asIdeal] using
    congrArg PrimeSpectrum.asIdeal
      (localization_prime_of_le_maximal_comap (R := R) p m hpm)

/-- Helper for Lemma 10.105.6: the iterated localization `(R_𝔪)_𝔮` is a localization of `R` at
`𝔭` when `𝔮` is the prime of `Spec(R_𝔪)` corresponding to `𝔭 ⊆ 𝔪`. -/
private theorem isLocalizationAtPrime_of_le_maximal
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p ≤ m.toPrimeSpectrum) :
    IsLocalization.AtPrime
      (Localization.AtPrime (localization_prime_of_le_maximal (R := R) p m hpm).asIdeal)
      p.asIdeal := by
  -- Apply the standard iterated-localization theorem after identifying the contracted prime.
  simpa [localization_prime_of_le_maximal_comap_asIdeal (R := R) p m hpm] using
    (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := m.asIdeal.primeCompl)
      (T := Localization.AtPrime (localization_prime_of_le_maximal (R := R) p m hpm).asIdeal)
      (localization_prime_of_le_maximal (R := R) p m hpm).asIdeal)

/-- Helper for Lemma 10.105.6: catenarity descends from `R_𝔪` to `R_𝔭` whenever `𝔭 ⊆ 𝔪`. -/
private theorem isCatenaryRing_localizationAtPrime_of_le_maximal
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p ≤ m.toPrimeSpectrum)
    [IsCatenaryRing (Localization.AtPrime m.asIdeal)] :
    IsCatenaryRing (Localization.AtPrime p.asIdeal) := by
  let q := localization_prime_of_le_maximal (R := R) p m hpm
  -- Localize the maximal localization once more at the corresponding prime.
  letI : IsCatenaryRing (Localization.AtPrime q.asIdeal) :=
    localization_isCatenaryRing (R := Localization.AtPrime m.asIdeal) q.asIdeal.primeCompl
  letI : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p.asIdeal :=
    isLocalizationAtPrime_of_le_maximal (R := R) p m hpm
  let e : Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal :=
    (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).toRingEquiv
  -- Then transport the catenary structure back along the canonical ring equivalence.
  exact isCatenaryRing_of_ringEquiv e.symm

/-- Lemma 10.105.6 (1): for a commutative ring `R`, the following are equivalent: `R` is
catenary, every localization `R_𝔭` at a prime ideal is catenary, and every localization `R_𝔪`
at a maximal ideal is catenary. -/
-- Proof sketch: `(1) → (2)` is Lemma `10.105.4`. `(2) → (3)` is immediate because maximal ideals
-- are prime. For `(3) → (1)`, compare chains of prime ideals between `𝔭 ⊆ 𝔮` in `R` with the
-- corresponding chains in a localization `R_𝔪` for a maximal ideal `𝔪` containing `𝔮`.
theorem isCatenaryRing_localization_tfae :
    List.TFAE
      [ IsCatenaryRing R,
        ∀ p : PrimeSpectrum R, IsCatenaryRing (Localization.AtPrime p.asIdeal),
        ∀ m : MaximalSpectrum R, IsCatenaryRing (Localization.AtPrime m.asIdeal) ] := by
  tfae_have 1 → 2 := by
    intro hR p
    letI : IsCatenaryRing R := hR
    -- The prime-local clause is exactly the localization stability from Lemma 10.105.4.
    exact localization_isCatenaryRing (R := R) p.asIdeal.primeCompl
  tfae_have 2 → 3 := by
    intro h p
    -- Maximal ideals are prime, so this is just specialization of the previous clause.
    exact h p.toPrimeSpectrum
  tfae_have 3 → 1 := by
    intro h
    -- Route correction: first recover every prime localization from a maximal localization, and
    -- only then invoke the already-proved prime-local criterion.
    refine isCatenaryRing_of_forall_prime_localizations (R := R) ?_
    intro p
    obtain ⟨mI, hmI, hpmI⟩ := Ideal.exists_le_maximal p.asIdeal p.2.1
    let m : MaximalSpectrum R := ⟨mI, hmI⟩
    have hpm : p ≤ m.toPrimeSpectrum := by
      simpa using hpmI
    letI : IsCatenaryRing (Localization.AtPrime m.asIdeal) := h m
    -- The chosen maximal ideal supplies the source-faithful bridge `R_𝔪 → R_𝔭`.
    exact isCatenaryRing_localizationAtPrime_of_le_maximal (R := R) p m hpm
  tfae_finish

section

variable [IsNoetherianRing R]

/-- Helper for Lemma 10.105.6: a finite-type witness subalgebra inside an essentially finite type
algebra over a universally catenary ring is catenary. -/
private theorem essFiniteType_witness_carrier_isCatenary {A : Type v}
    [CommRing A] [Algebra R A] [UniversallyCatenaryRing.{u, v} R]
    {S₀ : Subalgebra R A} [Algebra.FiniteType R S₀] : IsCatenaryRing S₀ := by
  -- Evaluate the universal catenarity owner on the finite-type witness carrier.
  let A₀ : Type v := S₀
  change IsCatenaryRing A₀
  exact (inferInstance : UniversallyCatenaryRing R).catenary_of_finiteType

/-- Helper for Lemma 10.105.6: the localization witness for an essentially finite type algebra
produces the canonical ring equivalence from the witness localization to the target algebra. -/
private noncomputable def essFiniteType_witness_localization_equiv {A : Type v}
    [CommRing A] [Algebra R A] {S₀ : Subalgebra R A} (M₀ : Submonoid S₀)
    [IsLocalization M₀ A] : Localization M₀ ≃+* A :=
  (IsLocalization.algEquiv M₀ (Localization M₀) A).toRingEquiv

/-- Helper for Lemma 10.105.6: essentially finite type algebras over a universally catenary ring
are catenary. -/
private theorem isCatenaryRing_of_essFiniteType {A : Type v}
    [CommRing A] [Algebra R A] [UniversallyCatenaryRing.{u, v} R]
    [Algebra.EssFiniteType R A] : IsCatenaryRing A := by
  obtain ⟨S₀, M₀, hft, hloc⟩ :=
    (Algebra.essFiniteType_iff_exists_subalgebra (R := R) (S := A)).1 inferInstance
  letI : Algebra.FiniteType R S₀ := hft
  letI : IsLocalization M₀ A := hloc
  -- First make the finite-type witness catenary, then localize and transport back to `A`.
  letI : IsCatenaryRing S₀ := essFiniteType_witness_carrier_isCatenary (R := R) (S₀ := S₀)
  letI : IsCatenaryRing (Localization M₀) := localization_isCatenaryRing (R := S₀) M₀
  exact isCatenaryRing_of_ringEquiv
    (essFiniteType_witness_localization_equiv (R := R) (A := A) (S₀ := S₀) M₀)

/-- Helper for Lemma 10.105.6: universal catenarity transports across a ring equivalence. -/
private theorem universallyCatenaryRing_of_ringEquiv {A : Type u} {B : Type u}
    [CommRing A] [CommRing B] (e : A ≃+* B) [UniversallyCatenaryRing.{u, v} A] :
    UniversallyCatenaryRing.{u, v} B := by
  letI : IsNoetherianRing B := isNoetherianRing_of_ringEquiv A e
  refine { catenary_of_finiteType := ?_ }
  intro T _ _ _
  letI : Algebra A B := RingHom.toAlgebra e.toRingHom
  letI : Algebra A T := RingHom.toAlgebra ((algebraMap B T).comp e.toRingHom)
  letI : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  -- Regard finite type `B`-algebras as finite type `A`-algebras through the equivalence.
  have hAB : Algebra.FiniteType A B := by
    let eAlg : A ≃ₐ[A] B := AlgEquiv.ofRingEquiv (f := e) fun x ↦ rfl
    exact Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType A A) eAlg
  have hAT : Algebra.FiniteType A T := Algebra.FiniteType.trans hAB inferInstance
  letI : Algebra.FiniteType A T := hAT
  -- Universal catenarity on `A` now applies directly to the transported algebra structure.
  exact (inferInstance : UniversallyCatenaryRing.{u, v} A).catenary_of_finiteType

/-- Helper for Lemma 10.105.6: universal catenarity descends from `R_𝔪` to `R_𝔭` whenever
`𝔭 ⊆ 𝔪`. -/
private theorem universallyCatenaryRing_localizationAtPrime_of_le_maximal
    (p : PrimeSpectrum R) (m : MaximalSpectrum R) (hpm : p ≤ m.toPrimeSpectrum)
    [UniversallyCatenaryRing.{u, v} (Localization.AtPrime m.asIdeal)] :
    UniversallyCatenaryRing.{u, v} (Localization.AtPrime p.asIdeal) := by
  let q := localization_prime_of_le_maximal (R := R) p m hpm
  -- Localize the universally catenary maximal localization at the corresponding prime.
  letI : UniversallyCatenaryRing.{u, v} (Localization.AtPrime q.asIdeal) :=
    localization_universallyCatenaryRing (R := Localization.AtPrime m.asIdeal) q.asIdeal.primeCompl
  letI : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p.asIdeal :=
    isLocalizationAtPrime_of_le_maximal (R := R) p m hpm
  let e : Localization.AtPrime p.asIdeal ≃+* Localization.AtPrime q.asIdeal :=
    (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).toRingEquiv
  -- Transport the universal owner back across the canonical ring equivalence.
  exact universallyCatenaryRing_of_ringEquiv e.symm

/-- Helper for Lemma 10.105.6: localizing a finite-type `R`-algebra `A` at `q` is essentially
finite type over the contracted base localization `R_(q ∩ R)`. -/
private theorem localizationAtPrime_essFiniteType_of_finiteType_contraction {A : Type v}
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (q : PrimeSpectrum A) :
    Algebra.EssFiniteType
      (Localization.AtPrime (PrimeSpectrum.comap (algebraMap R A) q).asIdeal)
      (Localization.AtPrime q.asIdeal) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
  letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R A) rfl).toAlgebra
  letI : IsScalarTower R (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    inferInstance
  letI : Algebra.EssFiniteType R (Localization.AtPrime q.asIdeal) := by
    infer_instance
  -- First view `A_𝔮` as essentially finite type over `R`, then restrict scalars to `R_𝔭`.
  exact Algebra.EssFiniteType.of_comp R (Localization.AtPrime p.asIdeal)
    (Localization.AtPrime q.asIdeal)

/-- Helper for Lemma 10.105.6: if the contracted base localization `R_(q ∩ R)` is universally
catenary, then the target localization `A_𝔮` is catenary. -/
private theorem isCatenaryRing_localizationAtPrime_of_finiteType_contraction {A : Type v}
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (q : PrimeSpectrum A)
    [UniversallyCatenaryRing.{u, v}
      (Localization.AtPrime (PrimeSpectrum.comap (algebraMap R A) q).asIdeal)] :
    IsCatenaryRing (Localization.AtPrime q.asIdeal) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
  letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R A) rfl).toAlgebra
  letI : IsScalarTower R (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    inferInstance
  letI : Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) :=
    localizationAtPrime_essFiniteType_of_finiteType_contraction (R := R) (A := A) q
  -- Apply the essentially-finite-type catenary bridge over the contracted base localization.
  exact isCatenaryRing_of_essFiniteType
    (R := Localization.AtPrime p.asIdeal) (A := Localization.AtPrime q.asIdeal)

/-- Helper for Lemma 10.105.6: if every prime localization is universally catenary, then `R` is
universally catenary. -/
private theorem universallyCatenaryRing_of_forall_prime_localizations
    (hlocal : ∀ p : PrimeSpectrum R,
      UniversallyCatenaryRing.{u, v} (Localization.AtPrime p.asIdeal)) :
    UniversallyCatenaryRing.{u, v} R := by
  refine { catenary_of_finiteType := ?_ }
  intro A _ _ _
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have hAq :
      ∀ q : PrimeSpectrum A, IsCatenaryRing (Localization.AtPrime q.asIdeal) := by
    intro q
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) q
    letI : UniversallyCatenaryRing.{u, v} (Localization.AtPrime p.asIdeal) := hlocal p
    -- The source proof localizes the finite-type algebra at `q` over the contracted base `p`.
    exact isCatenaryRing_localizationAtPrime_of_finiteType_contraction
      (R := R) (A := A) q
  -- Once every prime localization of `A` is catenary, the first TFAE recovers `A` itself.
  exact ((isCatenaryRing_localization_tfae (R := A)).out 1 0 rfl rfl).mp hAq

/-- Lemma 10.105.6 (2): for a Noetherian commutative ring `R`, the following are equivalent:
`R` is universally catenary, every localization `R_𝔭` at a prime ideal is universally catenary,
and every localization `R_𝔪` at a maximal ideal is universally catenary. -/
-- Proof sketch: `(1) → (2)` is Lemma `10.105.4`. `(2) → (3)` is immediate. For `(3) → (1)`,
-- let `R → A` be a finite type algebra. Localizing at a prime `𝔮` of `A` above `𝔭 ⊆ R`, choose a
-- maximal ideal `𝔪` of `R` containing `𝔭`; then `R_𝔭` is a localization of `R_𝔪`, so `A_𝔮` is
-- catenary, and the first TFAE gives catenarity of `A`.
theorem universallyCatenaryRing_localization_tfae :
    List.TFAE
      [ UniversallyCatenaryRing.{u, v} R,
        ∀ p : PrimeSpectrum R, UniversallyCatenaryRing.{u, v} (Localization.AtPrime p.asIdeal),
        ∀ m : MaximalSpectrum R, UniversallyCatenaryRing.{u, v} (Localization.AtPrime m.asIdeal) ] := by
  tfae_have 1 → 2 := by
    intro hR p
    letI : UniversallyCatenaryRing.{u, v} R := hR
    -- The prime-local clause is exactly localization stability from Lemma 10.105.4.
    exact localization_universallyCatenaryRing (R := R) p.asIdeal.primeCompl
  tfae_have 2 → 3 := by
    intro h m
    -- Maximal ideals are prime, so this is immediate from the prime-local clause.
    exact h m.toPrimeSpectrum
  tfae_have 3 → 1 := by
    intro h
    -- Route correction: first descend from maximal localizations to all prime localizations, and
    -- then apply the prime-local universal criterion proved above.
    refine universallyCatenaryRing_of_forall_prime_localizations (R := R) ?_
    intro p
    obtain ⟨mI, hmI, hpmI⟩ := Ideal.exists_le_maximal p.asIdeal p.2.1
    let m : MaximalSpectrum R := ⟨mI, hmI⟩
    have hpm : p ≤ m.toPrimeSpectrum := by
      simpa using hpmI
    letI : UniversallyCatenaryRing.{u, v} (Localization.AtPrime m.asIdeal) := h m
    -- The maximal-local hypothesis provides the source-faithful bridge `R_𝔪 → R_𝔭`.
    exact universallyCatenaryRing_localizationAtPrime_of_le_maximal (R := R) p m hpm
  tfae_finish

end

end
