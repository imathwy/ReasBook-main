import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_127_11
import stacks_proof.stacks_project.Chap10.Lemma_10_143_5
import stacks_proof.stacks_project.Chap10.Lemma_10_50_9
import stacks_proof.stacks_project.Chap15.Definition_15_124_1
import stacks_proof.stacks_project.Chap15.Lemma_15_105_4
import stacks_proof.stacks_project.Chap15.Lemma_15_105_14
import stacks_proof.stacks_project.Chap15.Lemma_15_105_18
import stacks_proof.stacks_project.Chap15.Lemma_15_108_1
import stacks_proof.stacks_project.Chap15.Lemma_15_112_2
import stacks_proof.stacks_project.Chap15.Lemma_15_124_2
import stacks_proof.stacks_project.Chap15.Lemma_15_124_4

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open IsExtensionOfValuationRings

universe u v

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
variable {B : Type v} [CommRing B] [Algebra A B] [Algebra.Etale A B]
variable (m : Ideal B) [m.IsPrime] [m.LiesOver (maximalIdeal A)]

local notation "Bₘ" => Localization.AtPrime m
local notation "K[A]" => FractionRing A
local notation "K[Bₘ]" => FractionRing Bₘ
local notation "Γ[A]" => ValuativeRel.ValueGroupWithZero K[A]
local notation "Γ[Bₘ]" => ValuativeRel.ValueGroupWithZero K[Bₘ]
local notation "Q" =>
  Γ[Bₘ]ˣ ⧸ MonoidWithZeroHom.valueGroup
    (ValuativeExtension.mapValueGroupWithZero K[A] K[Bₘ])

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/- Domain-style sampling for Lemma 15.124.5:
- primary domain: étale localizations over valuation rings and the induced weakly unramified
  extension-of-valuation-rings owner;
- sampled owner declarations:
  `IsExtensionOfValuationRings`,
  `IsExtensionOfValuationRings.WeaklyUnramified`,
  `IsLocalization.AtPrime.isLocalRing`,
  `Localization.localRingHom`,
  `IsLocalHom.mk`,
  `map_eq_maximalIdeal_of_exists_etale_away`;
- best owner abstraction: the source-facing main theorem should conclude the canonical owner
  predicate `WeaklyUnramified A Bₘ`, while the localized domain,
  valuation-ring support, and extension-of-valuation-rings structure are supplied by canonical
  localization owners together with the one genuinely new local bridge instance;
- primitive-vs-derived split:
  primitive data: the prime `m` of `B` together with the lying-over condition over `maximalIdeal A`;
  derived API: the local branch fact that `Bₘ` is a domain, the local valuation-ring support on
  `Bₘ`, the local bridge instance `IsExtensionOfValuationRings A Bₘ`, and the
  weakly-unramified conclusion.

Source/core/bridge triage:
- `source-facing`: the weakly unramified branch over `maximalIdeal A`;
- `core/canonical`: `IsExtensionOfValuationRings`, `WeaklyUnramified`, and the canonical
  localization-at-prime algebra;
- `bridge/view`: the canonical instance layer realizing `Bₘ` as the
  canonical target valuation ring over `A`. -/

/-- Helper for Lemma 15.124.5: weak dimension transfers across the étale map `A → B`, so the
localized branch `Bₘ` is a domain and a valuation ring. -/
private theorem localizationAtPrime_domain_and_valuationRing_of_etale :
    ∃ (_ : IsDomain Bₘ), ValuationRing Bₘ := by
  let q : PrimeSpectrum B := ⟨m, inferInstance⟩
  have hAwd : HasWeakDimensionLE A 1 := by
    -- Localizations of a valuation ring are valuation rings, so clause `(5)` of Lemma `15.105.18`
    -- applies to every prime localization of `A`.
    refine
      ((weakDimensionLEOne_idealFlat_fgIdealFlat_submoduleFlat_localizations_valuationRing_tfae
        (A := A)).out 4 0).mp ?_
    intro p
    exact ⟨inferInstance, inferInstance⟩
  have hBwd : HasWeakDimensionLE B 1 :=
    hasWeakDimensionLE_of_isWeaklyEtale (A := A) (B := B) (d := 1) inferInstance
  -- Apply the same `15.105.18` criterion to `B` and evaluate it at the chosen branch `m`.
  exact
    ((weakDimensionLEOne_idealFlat_fgIdealFlat_submoduleFlat_localizations_valuationRing_tfae
      (A := B)).out 0 4).mp hBwd q

local instance : IsDomain Bₘ := by
  classical
  -- Extract the domain witness from the weak-dimension localization criterion above.
  exact
    (localizationAtPrime_domain_and_valuationRing_of_etale (A := A) (B := B) (m := m)).choose

local instance : ValuationRing Bₘ := by
  classical
  -- Extract the valuation-ring witness from the same localized weak-dimension argument.
  exact
    Classical.choose_spec
      (localizationAtPrime_domain_and_valuationRing_of_etale (A := A) (B := B) (m := m))

/-- Helper for Lemma 15.124.5: the maximal ideal of `A` maps to the maximal ideal of the local
étale branch `Bₘ`. -/
private theorem localizationAtPrime_map_maximalIdeal_of_etale :
    (maximalIdeal A).map (algebraMap A Bₘ) = maximalIdeal Bₘ := by
  have hm_under : maximalIdeal A = m.under A :=
    (Ideal.liesOver_iff m (maximalIdeal A)).1 inferInstance
  have hm_ne_top : m ≠ ⊤ :=
    Ideal.IsPrime.ne_top (p := m) inferInstance
  have hEtaleAway : ∃ g : B, g ∉ m ∧ Algebra.Etale A (Localization.Away g) :=
    ⟨1, by simpa [Ideal.ne_top_iff_one] using hm_ne_top, inferInstance⟩
  -- The general étale-away local criterion identifies the mapped contracted prime with the
  -- maximal ideal of the localization, and the lying-over hypothesis rewrites the contraction.
  calc
    (maximalIdeal A).map (algebraMap A Bₘ) = (m.under A).map (algebraMap A Bₘ) := by
      rw [hm_under]
    _ = maximalIdeal Bₘ :=
      map_eq_maximalIdeal_of_exists_etale_away (R := A) (S := B) m hEtaleAway

/-- The canonical map from `A` to the localization at a prime over `maximalIdeal A` is an
extension of valuation rings. -/
instance localizationAtPrime_isExtensionOfValuationRings_of_etale :
    IsExtensionOfValuationRings A Bₘ := by
  refine
    { toIsLocalHom := ?_
      algebraMap_injective := ?_ }
  · refine IsLocalHom.mk fun a ha_unit ↦ ?_
    by_contra ha_nonunit
    have ha_mem : a ∈ maximalIdeal A := by
      -- In a local ring, nonunits are exactly the elements of the maximal ideal.
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact ha_nonunit
    have hmap_mem : algebraMap A Bₘ a ∈ maximalIdeal Bₘ := by
      -- The mapped maximal ideal is the maximal ideal of the localized branch.
      rw [← localizationAtPrime_map_maximalIdeal_of_etale (A := A) (B := B) (m := m)]
      exact Ideal.mem_map_of_mem _ ha_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmap_mem
    exact hmap_mem ha_unit
  · -- Étale maps are flat, localizations are flat, and the target branch is a domain.
    exact algebraMap_injective_of_flat_domain_target (A := A) (B := Bₘ)

/-- Helper for Lemma 15.124.5: the induced map on value groups for the localized branch is
injective because it is always strictly monotone for extensions of valuation rings. -/
private theorem localizationAtPrime_mapValueGroupWithZero_injective :
    Function.Injective
      (ValuativeExtension.mapValueGroupWithZero (FractionRing A) (FractionRing Bₘ)) := by
  -- The canonical value-group map is strictly monotone, so injectivity is automatic.
  exact ValuativeExtension.mapValueGroupWithZero_strictMono.injective

/-- Helper for Lemma 15.124.5: once the value-group map for the localized branch is known to be
surjective, weak unramifiedness follows immediately. -/
private theorem localizationAtPrime_weaklyUnramified_iff_surjective :
    WeaklyUnramified A Bₘ ↔
      Function.Surjective
        (ValuativeExtension.mapValueGroupWithZero (FractionRing A) (FractionRing Bₘ)) := by
  constructor
  · intro hweak
    -- Unpack the owner definition: bijectivity already contains the needed surjectivity.
    exact hweak.surjective
  · intro hsurj
    -- Reassemble weak unramifiedness from injectivity plus the supplied surjectivity.
    exact ⟨localizationAtPrime_mapValueGroupWithZero_injective (A := A) (B := B) (m := m), hsurj⟩

/-- Helper for Lemma 15.124.5: the induced extension of fraction rings along the localized étale
branch is finite-dimensional over `FractionRing A`. -/
private theorem localizationAtPrime_fractionRing_finiteDimensional_of_etale :
    FiniteDimensional (FractionRing A) (FractionRing Bₘ) := by
  let _ : Algebra (FractionRing A) (FractionRing Bₘ) := inferInstance
  let _ : Algebra.Etale (FractionRing A) (FractionRing Bₘ) := inferInstance
  -- Over a field, an étale algebra is a finite product of finite separable field extensions.
  obtain ⟨I, hI, Li, hField, hAlg, e, hsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (FractionRing A) (FractionRing Bₘ)).mp inferInstance
  let _ : Fintype I := Fintype.ofFinite I
  letI : ∀ i, Field (Li i) := hField
  letI : ∀ i, Algebra (FractionRing A) (Li i) := hAlg
  letI : ∀ i, Module.Finite (FractionRing A) (Li i) := fun i ↦ (hsep i).1
  let _ : Module.Finite (FractionRing A) (Π i, Li i) := inferInstance
  let _ : Module.Finite (FractionRing A) (FractionRing Bₘ) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  -- Finite modules over a field are finite-dimensional.
  exact FiniteDimensional.of_finite (FractionRing A) (FractionRing Bₘ)

/-- Helper for Lemma 15.124.5: the quotient of the localized target value group by the source image
is finite because the linear-independence argument from Lemma `15.124.2` bounds its cardinality by
the generic-fiber dimension. -/
private theorem localizationAtPrime_valueGroupQuotient_finite_of_etale :
    Finite
      Q := by
  let _ : FiniteDimensional K[A] K[Bₘ] :=
    localizationAtPrime_fractionRing_finiteDimensional_of_etale (A := A) (B := B) (m := m)
  let _ : FiniteDimensional (ResidueField A) (ResidueField Bₘ) :=
    finiteDimensional_residueField_of_finiteDimensional_fractionField_extension
      (A := A) (B := Bₘ)
  let c : Q → (FractionRing Bₘ)ˣ :=
    value_group_quotient_representative (A := A) (B := Bₘ)
  have hu :
      LinearIndependent (ResidueField A)
        (fun _ : PUnit ↦ IsLocalRing.residue Bₘ (1 : Bₘ)) := by
    classical
    -- The one-element family consisting of `1` in the residue field is linearly independent.
    rw [linearIndependent_iff]
    intro l hl
    ext x
    have hsum :
        l.sum
            (fun i a ↦ a • IsLocalRing.residue Bₘ (1 : Bₘ)) = 0 := by
      -- Expand the linear combination for the singleton-indexed family.
      simpa [Finsupp.linearCombination] using hl
    simpa using hsum
  have hc :
      Function.Injective fun q ↦
        ((Quotient.mk''
          (Units.map
            (Valuation.toMonoidWithZeroHom
              (ValuativeRel.valuation (FractionRing Bₘ))).toMonoidHom
            (c q))) : Q) := by
    intro q₁ q₂ hq
    -- The chosen representatives were built to recover their original quotient classes.
    simpa [c, value_group_quotient_representative_spec] using hq
  have hlin :
      LinearIndependent (FractionRing A)
        (fun p : PUnit × Q ↦ algebraMap Bₘ (FractionRing Bₘ) (1 : Bₘ) * (c p.2 : FractionRing Bₘ)) :=
    products_of_residue_lifts_and_distinct_value_classes_linearIndependent
      (A := A) (B := Bₘ) (fun _ : PUnit ↦ (1 : Bₘ)) c hu hc
  have hcard :
      Cardinal.mk Q ≤ Module.finrank (FractionRing A) (FractionRing Bₘ) := by
    -- Collapsing the harmless `PUnit` factor leaves a direct bound on the quotient cardinality.
    have hprod :
        Cardinal.mk (PUnit × Q) ≤ Module.finrank (FractionRing A) (FractionRing Bₘ) :=
      hlin.cardinalMk_le_finrank
    simpa using hprod
  -- Any type with cardinal bounded by a natural number is finite.
  exact Cardinal.lt_aleph0_iff_finite.mp (lt_of_le_of_lt hcard Cardinal.natCast_lt_aleph0)

/-- Helper for Lemma 15.124.5: an element of the localized branch has valuation at most `1`
because it is integral over the branch valuation ring. -/
private theorem localizationAtPrime_valuation_le_one_of_mem (x : Bₘ) :
    (ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] x) ≤ 1 := by
  let v := ValuationRing.valuation Bₘ K[Bₘ]
  let e := ValuativeRel.ValueGroupWithZero.orderMonoidIso v
  have hxv : v (algebraMap Bₘ K[Bₘ] x) ≤ 1 := by
    rw [Valuation.mem_integer_iff]
    exact (ValuationRing.mem_integer_iff Bₘ K[Bₘ] (algebraMap Bₘ K[Bₘ] x)).2 ⟨x, rfl⟩
  -- Translate the valuation-ring bound back to the canonical valuative-rel valuation.
  change e ((ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] x)) ≤ e 1
  simpa [e, v, ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀] using hxv

/-- Helper for Lemma 15.124.5: a source fraction-field element whose valuation is at most `1`
already comes from an element of `A`. -/
private theorem localizationAtPrime_exists_source_element_of_value_le_one {x : K[A]}
    (hx : (ValuativeRel.valuation K[A]) x ≤ 1) :
    ∃ f : A, algebraMap A K[A] f = x := by
  let v := ValuationRing.valuation A K[A]
  let e := ValuativeRel.ValueGroupWithZero.orderMonoidIso v
  have hxv : v x ≤ 1 := by
    have horder : e ((ValuativeRel.valuation K[A]) x) ≤ e 1 := by
      simpa [e, v, ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀] using hx
    simpa using horder
  -- Being integral over the source valuation ring is exactly the condition `v(x) ≤ 1`.
  exact (ValuationRing.mem_integer_iff A K[A] x).1 (by simpa [Valuation.mem_integer_iff] using hxv)

/-- Helper for Lemma 15.124.5: finite index of the source value group forces a positive power of a
nonzero branch element to have the same valuation as a source element, hence to differ from that
source element by a unit of `Bₘ`. -/
private theorem localizationAtPrime_exists_source_element_and_unit_for_power_of_nonzero
    {h : Bₘ} (hh : h ≠ 0) :
    ∃ (n : ℕ) (_ : 0 < n) (f : A) (w : Bₘˣ),
      algebraMap A Bₘ f = (w : Bₘ) * h ^ n := by
  classical
  let _ : Finite Q := localizationAtPrime_valueGroupQuotient_finite_of_etale (A := A) (B := B) (m := m)
  let _ : Fintype Q := Fintype.ofFinite Q
  let uh : K[Bₘ]ˣ := Units.mk0 (algebraMap Bₘ K[Bₘ] h) <| by
    exact map_ne_zero_iff (algebraMap Bₘ K[Bₘ]) (IsFractionRing.injective Bₘ K[Bₘ]) |>.2 hh
  let γh : Γ[Bₘ]ˣ :=
    Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[Bₘ])).toMonoidHom uh
  let qh : Q := Quotient.mk'' γh
  refine ⟨Fintype.card Q, Fintype.card_pos_iff.mpr inferInstance, ?_, ?_, ?_⟩
  have hqh : qh ^ Fintype.card Q = 1 := by
    simpa [qh] using pow_card_eq_one qh
  have htriv :
      ((Quotient.mk'' (γh ^ Fintype.card Q)) : Q) =
        ((Quotient.mk'' (1 : Γ[Bₘ]ˣ)) : Q) := by
    simpa [qh] using hqh
  have hmem :
      γh ^ Fintype.card Q ∈
        MonoidWithZeroHom.valueGroup
          (ValuativeExtension.mapValueGroupWithZero K[A] K[Bₘ]) := by
    rw [QuotientGroup.eq] at htriv
    simpa using htriv
  obtain ⟨δ, hδ⟩ :=
    exists_source_value_group_unit_of_mem_valueGroup (A := A) (B := Bₘ) hmem
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (K := K[A]) (δ : Γ[A])
  have hmapx :
      ValuativeExtension.mapValueGroupWithZero K[A] K[Bₘ]
          ((ValuativeRel.valuation K[A]) x) =
        (ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] h ^ Fintype.card Q) := by
    -- Unpack the subgroup witness as an equality of the underlying value-group elements.
    have hδ' := congrArg (fun u : Γ[Bₘ]ˣ ↦ (u : Γ[Bₘ])) hδ
    calc
      ValuativeExtension.mapValueGroupWithZero K[A] K[Bₘ]
          ((ValuativeRel.valuation K[A]) x)
          = ValuativeExtension.mapValueGroupWithZero K[A] K[Bₘ] (δ : Γ[A]) := by
              simpa [hx]
      _ = (γh ^ Fintype.card Q : Γ[Bₘ]ˣ) := by simpa using hδ'
      _ = (ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] h ^ Fintype.card Q) := by
              simp [γh, uh, map_pow]
  have hx_le_one :
      (ValuativeRel.valuation K[A]) x ≤ 1 := by
    have hhpow_le :
        (ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] h ^ Fintype.card Q) ≤ 1 := by
      simpa [map_pow] using
        localizationAtPrime_valuation_le_one_of_mem (A := A) (B := B) (m := m)
          (x := h ^ Fintype.card Q)
    -- Reflect the target inequality across the strictly monotone value-group map.
    exact ValuativeExtension.mapValueGroupWithZero_strictMono.le_iff_le.mp <| by
      simpa [hmapx] using hhpow_le
  obtain ⟨f, hf⟩ :=
    localizationAtPrime_exists_source_element_of_value_le_one
      (A := A) (B := B) (m := m) hx_le_one
  have hvaleq :
      (ValuativeRel.valuation K[Bₘ]) (algebraMap A K[Bₘ] f) =
        (ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] h ^ Fintype.card Q) := by
    simpa [hf] using hmapx
  have hhpow0 : algebraMap Bₘ K[Bₘ] h ^ Fintype.card Q ≠ 0 := by
    exact pow_ne_zero _ <| map_ne_zero_iff (algebraMap Bₘ K[Bₘ]) (IsFractionRing.injective Bₘ K[Bₘ]) |>.2 hh
  let z : K[Bₘ] :=
    algebraMap A K[Bₘ] f * (algebraMap Bₘ K[Bₘ] h ^ Fintype.card Q)⁻¹
  have hz :
      (ValuativeRel.valuation K[Bₘ]) z = 1 := by
    -- Equal valuations imply that the quotient has valuation `1`.
    calc
      (ValuativeRel.valuation K[Bₘ]) z
          = (ValuativeRel.valuation K[Bₘ]) (algebraMap A K[Bₘ] f) *
              ((ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] h ^ Fintype.card Q))⁻¹ := by
                simp [z]
      _ = 1 := by rw [hvaleq]
  obtain ⟨w, hw⟩ := target_ring_unit_of_valuation_eq_one (A := A) (B := Bₘ) hz
  refine ⟨f, w, ?_⟩
  apply IsFractionRing.injective Bₘ K[Bₘ]
  calc
    algebraMap Bₘ K[Bₘ] (algebraMap A Bₘ f)
        = algebraMap A K[Bₘ] f := by
            simp [IsScalarTower.algebraMap_eq A Bₘ K[Bₘ]]
    _ = algebraMap Bₘ K[Bₘ] (w : Bₘ) * (algebraMap Bₘ K[Bₘ] h ^ Fintype.card Q) := by
          calc
            algebraMap A K[Bₘ] f
                = z * (algebraMap Bₘ K[Bₘ] h ^ Fintype.card Q) := by
                    field_simp [z, hhpow0]
            _ = algebraMap Bₘ K[Bₘ] (w : Bₘ) * (algebraMap Bₘ K[Bₘ] h ^ Fintype.card Q) := by
                    rw [hw]
    _ = algebraMap Bₘ K[Bₘ] ((w : Bₘ) * h ^ Fintype.card Q) := by
          simp [map_mul, map_pow]

/-- Helper for Lemma 15.124.5: once the finite-index argument produces
`algebraMap A Bₘ f = (w : Bₘ) * h ^ n`, the remaining source-faithful step is exactly the
Noetherian-normal étale approximation from the textbook proof. -/
private theorem localizationAtPrime_algebraMap_essFinitePresentation_of_etale :
    RingHom.EssFinitePresentation (algebraMap A Bₘ) := by
  -- Étale algebras are finitely presented, so the localized branch map is essentially finitely
  -- presented without any extra approximation work.
  rw [RingHom.essFinitePresentation_algebraMap]
  infer_instance

/-- Helper for Lemma 15.124.5: the local étale map `A → Bₘ` admits the prime-localization stage
approximation used by the textbook descent argument. -/
private theorem localizationAtPrime_exists_localEssFinitePresentationApproximation_of_etale :
    ∃ Aapprox : DirectedLocalHomApproximation (algebraMap A Bₘ),
      DirectedLocalHomApproximation.HasPrimeLocalizationTransitions Aapprox := by
  let hess : RingHom.EssFinitePresentation (algebraMap A Bₘ) :=
    localizationAtPrime_algebraMap_essFinitePresentation_of_etale (A := A) (B := B) (m := m)
  -- This is the exact Chapter 10 approximation package needed to descend the local branch to a
  -- finite-type normal stage over `ℤ`.
  exact exists_localEssFinitePresentationApproximation (f := algebraMap A Bₘ) hess

/-- Helper for Lemma 15.124.5: a descended finite stage packages exactly the Noetherian normal
local branch needed to apply Lemma `15.124.4` and then map the resulting factorization back to
`A`. -/
private structure DescendedPowerStage (f : A) (h : Bₘ) (n : ℕ) where
  R0 : Type u
  S0 : Type v
  instCommRingR0 : CommRing R0
  instCommRingS0 : CommRing S0
  instAlgebraR0S0 : Algebra R0 S0
  instIsLocalRingR0 : IsLocalRing R0
  instIsLocalRingS0 : IsLocalRing S0
  instIsLocalHomR0S0 : IsLocalHom (algebraMap R0 S0)
  instIsNoetherianRingR0 : IsNoetherianRing R0
  instIsNoetherianRingS0 : IsNoetherianRing S0
  instIsDomainR0 : IsDomain R0
  instIsDomainS0 : IsDomain S0
  instIsNormalRingR0 : IsNormalRing R0
  instIsNormalRingS0 : IsNormalRing S0
  instFlatR0S0 : Module.Flat R0 S0
  sourceMap : R0 →+* A
  targetMap : S0 →+* Bₘ
  f0 : R0
  h0 : S0
  sourceMap_f0 : sourceMap f0 = f
  targetMap_h0 : targetMap h0 = h
  target_source_compat :
    targetMap.comp (algebraMap R0 S0) = (algebraMap A Bₘ).comp sourceMap
  power_relation :
    ∃ w0 : S0ˣ, algebraMap R0 S0 f0 = (w0 : S0) * h0 ^ n
  weak_heightOne_branches : HasWeaklyUnramifiedHeightOneBranches R0 S0

attribute [instance] DescendedPowerStage.instCommRingR0
attribute [instance] DescendedPowerStage.instCommRingS0
attribute [instance] DescendedPowerStage.instAlgebraR0S0
attribute [instance] DescendedPowerStage.instIsLocalRingR0
attribute [instance] DescendedPowerStage.instIsLocalRingS0
attribute [instance] DescendedPowerStage.instIsLocalHomR0S0
attribute [instance] DescendedPowerStage.instIsNoetherianRingR0
attribute [instance] DescendedPowerStage.instIsNoetherianRingS0
attribute [instance] DescendedPowerStage.instIsDomainR0
attribute [instance] DescendedPowerStage.instIsDomainS0
attribute [instance] DescendedPowerStage.instIsNormalRingR0
attribute [instance] DescendedPowerStage.instIsNormalRingS0
attribute [instance] DescendedPowerStage.instFlatR0S0

/-- Helper for Lemma 15.124.5: a raw local stage package records only the displayed powered
relation and its compatibility with the source and target maps; the Noetherian normal branch data
needed for Lemma `15.124.4` is built later from such a package. -/
private structure StagewisePowerRelationData (f : A) (h : Bₘ) (n : ℕ)
    where
  R0 : Type u
  S0 : Type v
  instCommRingR0 : CommRing R0
  instCommRingS0 : CommRing S0
  instAlgebraR0S0 : Algebra R0 S0
  instIsLocalRingR0 : IsLocalRing R0
  instIsLocalRingS0 : IsLocalRing S0
  instIsLocalHomR0S0 : IsLocalHom (algebraMap R0 S0)
  sourceMap : R0 →+* A
  targetMap : S0 →+* Bₘ
  f0 : R0
  h0 : S0
  sourceMap_f0 : sourceMap f0 = f
  targetMap_h0 : targetMap h0 = h
  target_source_compat :
    targetMap.comp (algebraMap R0 S0) = (algebraMap A Bₘ).comp sourceMap
  power_relation :
    ∃ w0 : S0ˣ, algebraMap R0 S0 f0 = (w0 : S0) * h0 ^ n

attribute [instance] StagewisePowerRelationData.instCommRingR0
attribute [instance] StagewisePowerRelationData.instCommRingS0
attribute [instance] StagewisePowerRelationData.instAlgebraR0S0
attribute [instance] StagewisePowerRelationData.instIsLocalRingR0
attribute [instance] StagewisePowerRelationData.instIsLocalRingS0
attribute [instance] StagewisePowerRelationData.instIsLocalHomR0S0

/-- Helper for Lemma 15.124.5: once a descended Noetherian normal local stage is available, Lemma
`15.124.4` produces the required factorization in `A` by mapping the stage-level source root and
unit forward along the descended source map. -/
private theorem localizationAtPrime_exists_unit_mul_pow_in_source_of_descended_stage
    {f : A} {h : Bₘ} {n : ℕ}
    (stage : DescendedPowerStage (A := A) (B := B) (m := m) f h n) :
    ∃ g : A, ∃ u : Aˣ, f = (u : A) * g ^ n := by
  -- Apply Lemma `15.124.4` at the descended stage, where the Noetherian normal hypotheses and
  -- the height-one weak-unramified branch condition are already bundled.
  obtain ⟨g0, u0, hu0⟩ :=
    exists_unit_mul_pow_in_source_of_exists_unit_mul_pow_in_target
      (A := stage.R0) (B := stage.S0) stage.weak_heightOne_branches stage.power_relation
  refine ⟨stage.sourceMap g0, Units.map stage.sourceMap.toMonoidHom u0, ?_⟩
  -- Mapping the stage factorization along `R0 → A` gives the desired factorization of `f`.
  calc
    f = stage.sourceMap stage.f0 := by simpa using stage.sourceMap_f0.symm
    _ = stage.sourceMap ((u0 : stage.R0) * g0 ^ n) := by rw [hu0]
    _ = (Units.map stage.sourceMap.toMonoidHom u0 : Aˣ) * stage.sourceMap g0 ^ n := by
          simp [map_mul, map_pow]

/-- Helper for Lemma 15.124.5: before carrying out the finite-stage descent, one can package the
given relation `f = unit * h^n` as a raw local-stage witness on the terminal branch `A → Bₘ`. -/
private theorem localizationAtPrime_common_stage_relation_package_of_etale
    {f : A} {h : Bₘ} {n : ℕ} (hn : 0 < n)
    (hpow : ∃ w : Bₘˣ, algebraMap A Bₘ f = (w : Bₘ) * h ^ n) :
    Nonempty (StagewisePowerRelationData (A := A) (B := B) (m := m) f h n) := by
  obtain ⟨w, hw⟩ := hpow
  have hsourceMap_f0 : (RingHom.id A) f = f := rfl
  have htargetMap_h0 : (RingHom.id Bₘ) h = h := rfl
  have hcompat :
      (RingHom.id Bₘ).comp (algebraMap A Bₘ) =
        (algebraMap A Bₘ).comp (RingHom.id A) := rfl
  have hpower :
      ∃ w0 : Bₘˣ, algebraMap A Bₘ f = (w0 : Bₘ) * h ^ n := ⟨w, hw⟩
  let _ := hn
  -- Record the displayed relation on the actual local branch. The finite-stage descent that the
  -- source proof needs will refine this raw package later.
  refine ⟨{
    R0 := A
    S0 := Bₘ
    instCommRingR0 := inferInstance
    instCommRingS0 := inferInstance
    instAlgebraR0S0 := inferInstance
    instIsLocalRingR0 := inferInstance
    instIsLocalRingS0 := inferInstance
    instIsLocalHomR0S0 := inferInstance
    sourceMap := RingHom.id A
    targetMap := RingHom.id Bₘ
    f0 := f
    h0 := h
    sourceMap_f0 := hsourceMap_f0
    targetMap_h0 := htargetMap_h0
    target_source_compat := hcompat
    power_relation := hpower
  }⟩

/-- Helper for Lemma 15.124.5: the downstream theorem name is now a thin adapter around the raw
relation package. -/
private theorem localizationAtPrime_stagewise_power_relation_descent_of_etale
    {f : A} {h : Bₘ} {n : ℕ} (hn : 0 < n)
    (hpow : ∃ w : Bₘˣ, algebraMap A Bₘ f = (w : Bₘ) * h ^ n) :
    Nonempty (StagewisePowerRelationData (A := A) (B := B) (m := m) f h n) := by
  -- Packaging the relation itself is now separated from the later normalization/descent step.
  exact
    localizationAtPrime_common_stage_relation_package_of_etale
      (A := A) (B := B) (m := m) hn hpow

/-- Helper for Lemma 15.124.5: once the stagewise relation package is available, the downstream
argument still needs a descended Noetherian normal local stage. -/
private theorem localizationAtPrime_descendedPowerStage_of_stagewise_data
    {f : A} {h : Bₘ} {n : ℕ}
    (data : StagewisePowerRelationData (A := A) (B := B) (m := m) f h n) :
    DescendedPowerStage (A := A) (B := B) (m := m) f h n := by
  -- Route correction: the raw package above deliberately no longer pretends to be the final
  -- Noetherian normal branch. The remaining source-faithful step is to replace `data` by a finite
  -- local stage, normalize it, descend the étale model, and localize at the branch over the
  -- maximal ideal.
  --
  -- TODO: construct the finite approximation stage promised by the textbook proof, then transport
  -- `data.power_relation` to the resulting Noetherian normal branch and verify the height-one
  -- weakly-unramified hypothesis needed by Lemma `15.124.4`.
  let _ := data
  sorry

/-- Helper for Lemma 15.124.5: the source-faithful approximation argument should descend the
original powered relation to one Noetherian normal local stage carrying the exact hypotheses of
Lemma `15.124.4`. -/
private theorem localizationAtPrime_descendedPowerStage_of_etale
    {f : A} {h : Bₘ} {n : ℕ} (hn : 0 < n)
    (hpow : ∃ w : Bₘˣ, algebraMap A Bₘ f = (w : Bₘ) * h ^ n) :
    Nonempty (DescendedPowerStage (A := A) (B := B) (m := m) f h n) := by
  obtain ⟨data⟩ :=
    localizationAtPrime_stagewise_power_relation_descent_of_etale
      (A := A) (B := B) (m := m) hn hpow
  -- After the stagewise descent step, the remaining packaging is just forgetting the auxiliary
  -- approximation bookkeeping.
  exact
    ⟨localizationAtPrime_descendedPowerStage_of_stagewise_data
      (A := A) (B := B) (m := m) data⟩

/-- Helper for Lemma 15.124.5: once the finite-index argument produces
`algebraMap A Bₘ f = (w : Bₘ) * h ^ n`, the remaining source-faithful step is exactly the
Noetherian-normal étale approximation from the textbook proof. -/
private theorem localizationAtPrime_exists_unit_mul_pow_in_source_of_exists_unit_mul_pow_in_target_of_etale
    {f : A} {h : Bₘ} {n : ℕ} (hn : 0 < n)
    (hpow : ∃ w : Bₘˣ, algebraMap A Bₘ f = (w : Bₘ) * h ^ n) :
    ∃ g : A, ∃ u : Aˣ, f = (u : A) * g ^ n := by
  obtain ⟨stage⟩ :=
    localizationAtPrime_descendedPowerStage_of_etale
      (A := A) (B := B) (m := m) hn hpow
  -- The approximation/descent package reduces the current helper to the stage-level version of
  -- Lemma `15.124.4`, followed by mapping the source factorization back to `A`.
  exact
    localizationAtPrime_exists_unit_mul_pow_in_source_of_descended_stage
      (A := A) (B := B) (m := m) stage

/-- Helper for Lemma 15.124.5: once the finite-index argument produces
`algebraMap A Bₘ f = (w : Bₘ) * h ^ n`, the remaining source-faithful step is exactly the
Noetherian-normal étale approximation from the textbook proof. -/
private theorem localizationAtPrime_value_of_nonzero_mem_image_of_etale
    {h : Bₘ} (hh : h ≠ 0) :
    ∃ δ : Γ[A],
      ValuativeExtension.mapValueGroupWithZero K[A] K[Bₘ] δ =
        (ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] h) := by
  obtain ⟨n, hn, f, w, hw⟩ :=
    localizationAtPrime_exists_source_element_and_unit_for_power_of_nonzero
      (A := A) (B := B) (m := m) hh
  obtain ⟨g, u, hsource⟩ :=
    localizationAtPrime_exists_unit_mul_pow_in_source_of_exists_unit_mul_pow_in_target_of_etale
      (A := A) (B := B) (m := m) hn ⟨w, hw⟩
  have hExt : IsExtensionOfValuationRings A Bₘ :=
    localizationAtPrime_isExtensionOfValuationRings_of_etale (A := A) (B := B) (m := m)
  have hhK0 : algebraMap Bₘ K[Bₘ] h ≠ 0 := by
    exact
      (map_ne_zero_iff (algebraMap Bₘ K[Bₘ]) (IsFractionRing.injective Bₘ K[Bₘ])).2 hh
  have hfBₘ0 : algebraMap A Bₘ f ≠ 0 := by
    -- The target-side powered relation forces `f` to stay nonzero because `h` is nonzero and `w`
    -- is a unit.
    rw [hw]
    exact mul_ne_zero (Units.ne_zero w) (pow_ne_zero n hh)
  have hf0 : f ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap A Bₘ) hExt.algebraMap_injective).1 hfBₘ0
  have hg0 : g ≠ 0 := by
    -- The source-side factorization cannot have zero root because `f` is already nonzero.
    intro hg0
    apply hf0
    rw [hsource, hg0]
    simp [hn.ne']
  have hwK :
      algebraMap A K[Bₘ] f =
        algebraMap Bₘ K[Bₘ] (w : Bₘ) * (algebraMap Bₘ K[Bₘ] h) ^ n := by
    -- Move the target-side factorization to the fraction field of `Bₘ`.
    calc
      algebraMap A K[Bₘ] f = algebraMap Bₘ K[Bₘ] (algebraMap A Bₘ f) := by
        simpa [RingHom.comp_apply] using
          DFunLike.congr_fun (IsScalarTower.algebraMap_eq A Bₘ K[Bₘ]) f
      _ = algebraMap Bₘ K[Bₘ] ((w : Bₘ) * h ^ n) := by rw [hw]
      _ = algebraMap Bₘ K[Bₘ] (w : Bₘ) * (algebraMap Bₘ K[Bₘ] h) ^ n := by
        simp [map_mul, map_pow]
  have hsourceK :
      algebraMap A K[A] f =
        algebraMap A K[A] (u : A) * (algebraMap A K[A] g) ^ n := by
    -- Move the descended source-side factorization to the source fraction field.
    simpa [map_mul, map_pow] using congrArg (algebraMap A K[A]) hsource
  have hval_target :
      (ValuativeRel.valuation K[Bₘ]) (algebraMap A K[Bₘ] f) =
        ((ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] h)) ^ n := by
    -- Units contribute valuation `1`, so only the `n`-th power of `h` remains.
    calc
      (ValuativeRel.valuation K[Bₘ]) (algebraMap A K[Bₘ] f)
          = (ValuativeRel.valuation K[Bₘ])
              (algebraMap Bₘ K[Bₘ] (w : Bₘ) * (algebraMap Bₘ K[Bₘ] h) ^ n) := by
                rw [hwK]
      _ =
          (ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] (w : Bₘ)) *
            ((ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] h)) ^ n := by
              simp [map_mul, map_pow]
      _ = ((ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] h)) ^ n := by simp
  have hval_source :
      (ValuativeRel.valuation K[A]) (algebraMap A K[A] f) =
        ((ValuativeRel.valuation K[A]) (algebraMap A K[A] g)) ^ n := by
    -- The same valuation computation on the source side removes the source unit.
    calc
      (ValuativeRel.valuation K[A]) (algebraMap A K[A] f)
          = (ValuativeRel.valuation K[A])
              (algebraMap A K[A] (u : A) * (algebraMap A K[A] g) ^ n) := by
                rw [hsourceK]
      _ =
          (ValuativeRel.valuation K[A]) (algebraMap A K[A] (u : A)) *
            ((ValuativeRel.valuation K[A]) (algebraMap A K[A] g)) ^ n := by
              simp [map_mul, map_pow]
      _ = ((ValuativeRel.valuation K[A]) (algebraMap A K[A] g)) ^ n := by simp
  refine ⟨(ValuativeRel.valuation K[A]) (algebraMap A K[A] g), ?_⟩
  have hval_source_target :
      (ValuativeExtension.mapValueGroupWithZero K[A] K[Bₘ]
          ((ValuativeRel.valuation K[A]) (algebraMap A K[A] g))) ^ n =
        ((ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] h)) ^ n := by
    -- Compare the valuation of `f` computed from the descended source root and from the original
    -- target root.
    calc
      (ValuativeExtension.mapValueGroupWithZero K[A] K[Bₘ]
          ((ValuativeRel.valuation K[A]) (algebraMap A K[A] g))) ^ n
          =
        ValuativeExtension.mapValueGroupWithZero K[A] K[Bₘ]
          ((ValuativeRel.valuation K[A]) (algebraMap A K[A] f)) := by
            rw [hval_source]
            simp
      _ = (ValuativeRel.valuation K[Bₘ]) (algebraMap A K[Bₘ] f) := by
            simp [ValuativeExtension.mapValueGroupWithZero_valuation]
      _ = ((ValuativeRel.valuation K[Bₘ]) (algebraMap Bₘ K[Bₘ] h)) ^ n := hval_target
  -- Cancel the positive power in the totally ordered target value group.
  exact (pow_left_strictMono hn.ne').injective hval_source_target

/-- Helper for Lemma 15.124.5: the remaining source-faithful task is surjectivity of the
localized value-group map. -/
private theorem localizationAtPrime_valueGroupWithZero_surjective_of_etale :
    Function.Surjective
      (ValuativeExtension.mapValueGroupWithZero K[A] K[Bₘ]) := by
  intro γ
  by_cases hγ : γ = 0
  · refine ⟨0, ?_⟩
    simpa [hγ]
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (K := K[Bₘ]) γ
  have hy0 : y ≠ 0 := by
    intro hy0
    exact hγ (by simpa [hy0] using hy.symm)
  rcases (ValuationRing.iff_isInteger_or_isInteger Bₘ K[Bₘ]).mp inferInstance y with hyInt | hyInvInt
  · obtain ⟨h, hhEq⟩ := hyInt
    obtain ⟨δ, hδ⟩ :=
      localizationAtPrime_value_of_nonzero_mem_image_of_etale
        (A := A) (B := B) (m := m) (h := h) (by
          intro hh0
          exact hy0 (by simpa [hh0] using hhEq.symm))
    refine ⟨δ, ?_⟩
    simpa [hy, hhEq]
  · obtain ⟨h, hhEq⟩ := hyInvInt
    obtain ⟨δ, hδ⟩ :=
      localizationAtPrime_value_of_nonzero_mem_image_of_etale
        (A := A) (B := B) (m := m) (h := h) (by
          intro hh0
          have : y⁻¹ = 0 := by simpa [hh0] using hhEq.symm
          exact hy0 <| inv_eq_zero.mp this)
    refine ⟨δ⁻¹, ?_⟩
    -- Passing from the inverse-integral case back to `y` just inverts the value-group equality.
    calc
      ValuativeExtension.mapValueGroupWithZero K[A] K[Bₘ] δ⁻¹
          = (ValuativeExtension.mapValueGroupWithZero K[A] K[Bₘ] δ)⁻¹ := by simp
      _ = ((ValuativeRel.valuation K[Bₘ]) y⁻¹)⁻¹ := by simpa [hhEq] using congrArg Inv.inv hδ
      _ = (ValuativeRel.valuation K[Bₘ]) y := by
            simp [map_inv₀, hy0]
      _ = γ := hy

-- Proof sketch: apply the valuation-ring analogue of the étale-local normal Noetherian argument
-- to the localization `B_m`. The prime above `maximalIdeal A` gives the canonical local
-- `A`-algebra structure on `Localization.AtPrime m`; one shows this localization is again a
-- valuation ring, that the induced local map is injective, and that the induced map on value
-- groups is bijective.
/-- Lemma 15.124.5: if `A` is a valuation ring, `A → B` is étale, and `m` is a prime of `B`
lying over the maximal ideal of `A`, then the canonical localized branch `Bₘ` is weakly
unramified over `A`. -/
@[stacks 0ASJ]
theorem localizationAtPrime_isWeaklyUnramifiedExtensionOfValuationRings_of_etale :
    WeaklyUnramified A Bₘ := by
  let _ : IsExtensionOfValuationRings A Bₘ := inferInstance
  -- Reduce the theorem to the surjectivity half of the value-group map.
  rw [localizationAtPrime_weaklyUnramified_iff_surjective (A := A) (B := B) (m := m)]
  -- TODO: the only remaining blocker is the source-faithful surjectivity construction described
  -- in `localizationAtPrime_valueGroupWithZero_surjective_of_etale`.
  exact localizationAtPrime_valueGroupWithZero_surjective_of_etale (A := A) (B := B) (m := m)

end
