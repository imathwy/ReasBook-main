import Mathlib
import Mathlib.Topology.Sets.Closeds
import StacksProject_2024.Chap10.Definition_10_54_1
import StacksProject_2024.Chap10.Lemma_10_54_5
import StacksProject_2024.Chap10.Definition_10_105_3
import StacksProject_2024.Chap10.Lemma_10_18_4
import StacksProject_2024.Chap10.Lemma_10_97_3
import StacksProject_2024.Chap10.Lemma_10_97_5
import StacksProject_2024.Chap10.Lemma_10_105_4
import StacksProject_2024.Chap10.Lemma_10_105_6
import StacksProject_2024.Chap10.Lemma_10_105_7
import StacksProject_2024.Chap10.Lemma_10_105_8
import StacksProject_2024.Chap10.Lemma_10_156_2
import StacksProject_2024.Chap10.Lemma_10_160_2
import StacksProject_2024.Chap10.Remark_10_160_9
import StacksProject_2024.Chap15.Definition_15_110_1
import StacksProject_2024.Chap15.Lemma_15_43_1
import StacksProject_2024.Chap15.Lemma_15_90_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing TopologicalSpace
open scoped TensorProduct

section

variable {A : Type u} [CommRing A]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/- Domain-style sampling for the formal-catenary to universal-catenary bridge:
- primary domain: Noetherian local commutative rings, formal catenarity, and universal
  catenarity;
- sampled owner declarations:
  `IsFormallyCatenaryRing`,
  `UniversallyCatenaryRing`,
  `universallyCatenaryRing_of_support_eq_univ_of_locallyCohenMacaulay`,
  `universallyCatenaryRing_of_isCompleteLocalRing`;
- best owner abstraction: `IsFormallyCatenaryRing` is the source-facing owner and
  `UniversallyCatenaryRing` is the canonical core owner; this file supplies only the bridge from
  the former to the latter;
- primitive data: the owner hypothesis `[IsFormallyCatenaryRing A]`;
- derived API: any term-level theorem restating the resulting instance is redundant.

Source/core/bridge triage:
- `source-facing`: the textbook implication that formally catenary Noetherian local rings are
  universally catenary;
- `core/canonical`: `UniversallyCatenaryRing`;
- `bridge/view`: the instance upgrading `[IsFormallyCatenaryRing A]` to
  `[UniversallyCatenaryRing A]`.
-/

-- Proof sketch: combine the formally catenary hypothesis with the equidimensionality of the
-- completed quotients by minimal primes, then apply the local-to-global criterion for universal
-- catenarity through local finite type algebras and the complete local case.
/-- Helper for Lemma 15.110.4: the formal-catenary hypothesis already gives equidimensionality for
the completion quotient by each minimal prime of `A`. -/
lemma equidimensional_completion_quotient_of_minimalPrime [IsFormallyCatenaryRing A]
    (p : minimalPrimes A) :
    EquidimensionalSpace
      (PrimeSpectrum (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1)) := by
  -- This is exactly the defining datum of formal catenarity.
  exact IsFormallyCatenaryRing.equidimensional_completion_quotient (A := A) p

/-- Helper for Lemma 15.110.4: the quotient by a minimal prime of a local ring is still local. -/
local instance minimalPrimeQuotient_isLocalRing [IsFormallyCatenaryRing A] (p : minimalPrimes A) :
    IsLocalRing (A ⧸ p.1) := by
  -- Minimal primes are proper, so the standard local-quotient theorem applies.
  exact IsLocalRing.quotient p.1 (Ideal.minimalPrimes_isPrime p.2).ne_top

/-- Helper for Lemma 15.110.4: the ideal residue field at the maximal ideal of a local ring
matches the canonical local residue field. -/
private noncomputable abbrev maximalIdeal_residueField_equiv
    (R : Type*) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Lemma 15.110.4: under the maximal-ideal residue-field identification, residue
classes of elements agree with the usual local residue classes. -/
private theorem maximalIdeal_residueField_equiv_apply_algebraMap
    (R : Type*) [CommRing R] [IsLocalRing R] (a : R) :
    maximalIdeal_residueField_equiv R (algebraMap R (maximalIdeal R).ResidueField a) =
      residue R a := by
  -- Compare both residue classes after moving them through the inverse quotient equivalence.
  rw [show algebraMap R (maximalIdeal R).ResidueField a =
      algebraMap (ResidueField R) (maximalIdeal R).ResidueField (residue R a) by rfl]
  change
    maximalIdeal_residueField_equiv R
        ((maximalIdeal_residueField_equiv R).symm (residue R a)) =
      residue R a
  exact (maximalIdeal_residueField_equiv R).apply_symm_apply (residue R a)

/-- Helper for Lemma 15.110.4: after identifying ideal residue fields with local residue fields,
the ideal-level residue-field map becomes the usual local residue-field map. -/
private theorem maximalIdeal_residueField_equiv_comp_residueFieldMap
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] :
    (maximalIdeal_residueField_equiv S).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (ResidueField.map f).comp (maximalIdeal_residueField_equiv R).toRingHom := by
  -- It is enough to compare both ring maps on residue classes of source elements.
  apply Ideal.ResidueField.ringHom_ext
  ext a
  change
    maximalIdeal_residueField_equiv S
        (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) f
          (IsLocalRing.maximalIdeal_comap f).symm
          (algebraMap R (maximalIdeal R).ResidueField a)) =
      ResidueField.map f
        (maximalIdeal_residueField_equiv R (algebraMap R (maximalIdeal R).ResidueField a))
  rw [Ideal.ResidueField.map_algebraMap, maximalIdeal_residueField_equiv_apply_algebraMap,
    maximalIdeal_residueField_equiv_apply_algebraMap, IsLocalRing.ResidueField.map_residue]

/-- Helper for Lemma 15.110.4: a surjective local homomorphism induces a bijection on residue
fields. -/
private theorem residueField_bijective_of_surjective_localHom
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Nontrivial S] (f : R →+* S) (hf : Function.Surjective f) [IsLocalHom f] :
    Function.Bijective (ResidueField.map f) := by
  constructor
  · -- A map out of a field into a nontrivial ring is injective.
    exact RingHom.injective (ResidueField.map f)
  · intro z
    -- Lift a target residue class back through the surjective local map.
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective z
    rcases hf s with ⟨r, rfl⟩
    refine ⟨residue R r, ?_⟩
    simpa using IsLocalRing.ResidueField.map_residue f r

/-- Helper for Lemma 15.110.4: quotient maps out of local rings are local homomorphisms. -/
private local instance quotientMap_isLocalHom
    (R : Type*) [CommRing R] [IsLocalRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    IsLocalHom (Ideal.Quotient.mk I) :=
  Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective

/-- Helper for Lemma 15.110.4: quotienting a local ring by a proper ideal does not change its
residue field. -/
private noncomputable abbrev residueField_equiv_of_quotient
    (R : Type*) [CommRing R] [IsLocalRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    ResidueField (R ⧸ I) ≃+* ResidueField R :=
  (RingEquiv.ofBijective (ResidueField.map (Ideal.Quotient.mk I))
    (residueField_bijective_of_surjective_localHom
      (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective)).symm

/-- Helper for Lemma 15.110.4: the maximal-ideal completion of a formally catenary local ring is
Noetherian. -/
local instance completion_isNoetherianRing [IsFormallyCatenaryRing A] :
    IsNoetherianRing ACompletion := by
  -- Lemma `10.97.5` applies because the residue ring is Noetherian and the maximal ideal is
  -- finitely generated.
  exact
    (adicCompletion_isNoetherian_and_isAdicComplete
      (R := A) (I := maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A))).1

/-- Helper for Lemma 15.110.4: an order isomorphism on irreducible closed subsets preserves
relative codimension. -/
lemma codimBetween_eq_of_irreducibleCloseds_orderIso
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : IrreducibleCloseds X ≃o IrreducibleCloseds Y)
    {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween (e T) (e T') (e.monotone hTT') = codimBetween T T' hTT' := by
  -- Compare the interval owner `[T, T']` with its image under the order isomorphism.
  let eIcc : ↥(Set.Icc T T') ≃o ↥(Set.Icc (e T) (e T')) :=
    { toFun := fun z ↦ ⟨e z.1, by
        rcases z.2 with ⟨hz₁, hz₂⟩
        exact ⟨e.monotone hz₁, e.monotone hz₂⟩⟩
      invFun := fun z ↦ ⟨e.symm z.1, by
        rcases z.2 with ⟨hz₁, hz₂⟩
        exact ⟨by simpa using e.symm.monotone hz₁, by simpa using e.symm.monotone hz₂⟩⟩
      left_inv := by
        intro z
        ext x
        simp
      right_inv := by
        intro z
        ext x
        simp
      map_rel_iff' := by
        intro a b
        change e a.1 ≤ e b.1 ↔ a.1 ≤ b.1
        exact e.map_rel_iff }
  -- The interval bottom is the left endpoint, so `coheight` is unchanged by `eIcc`.
  let _ : Fact (T ≤ T') := ⟨hTT'⟩
  let _ : Fact (e T ≤ e T') := ⟨e.monotone hTT'⟩
  simpa [codimBetween, eIcc] using
    (Order.coheight_orderIso eIcc (⊥ : Set.Icc T T'))

/-- Helper for Lemma 15.110.4: an order isomorphism of irreducible closed subsets transports the
full catenary-space structure. -/
lemma catenarySpace_of_irreducibleCloseds_orderIso
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : IrreducibleCloseds X ≃o IrreducibleCloseds Y) (hX : CatenarySpace X) :
    CatenarySpace Y := by
  -- Both catenary fields are interval statements, so they transport through the induced interval
  -- order isomorphisms coming from `e`.
  let _ : CatenarySpace X := hX
  refine ⟨?_, ?_⟩
  · intro U U' hUU'
    have hback :
        codimBetween (e.symm U) (e.symm U') (e.symm.monotone hUU') =
          codimBetween U U' hUU' :=
      codimBetween_eq_of_irreducibleCloseds_orderIso
        (e := e.symm) (T := U) (T' := U') hUU'
    exact hback.symm ▸ hX.finite_codimBetween (e.symm.monotone hUU')
  · intro U U' hUU' s hs
    -- Pull a maximal chain in `[U, U']` back to the source interval and apply the source formula.
    let eIcc : ↥(Set.Icc (e.symm U) (e.symm U')) ≃o ↥(Set.Icc U U') :=
      { toFun := fun z ↦ ⟨e z.1, by
          rcases z.2 with ⟨hz₁, hz₂⟩
          exact ⟨by simpa using e.monotone hz₁, by simpa using e.monotone hz₂⟩⟩
        invFun := fun z ↦ ⟨e.symm z.1, by
          rcases z.2 with ⟨hz₁, hz₂⟩
          exact ⟨e.symm.monotone hz₁, e.symm.monotone hz₂⟩⟩
        left_inv := by
          intro z
          ext x
          simp
        right_inv := by
          intro z
          ext x
          simp
        map_rel_iff' := by
          intro a b
          change e a.1 ≤ e b.1 ↔ a.1 ≤ b.1
          exact e.map_rel_iff }
    have hs_source : IsMaxChain (· ≤ ·) (eIcc.symm '' s) :=
      hs.image eIcc.symm
    calc
      s.encard = (eIcc.symm '' s).encard := by
        symm
        exact eIcc.symm.injective.encard_image s
      _ =
          (ENat.toNat
              (codimBetween (e.symm U) (e.symm U')
                (e.symm.monotone hUU')) + 1 : ℕ∞) :=
        hX.maximalIrreducibleClosedChainsHaveLength
          (hTT' := e.symm.monotone hUU') (s := eIcc.symm '' s) hs_source
      _ = (ENat.toNat (codimBetween U U' hUU') + 1 : ℕ∞) := by
        rw [codimBetween_eq_of_irreducibleCloseds_orderIso
          (e := e.symm) (T := U) (T' := U') hUU']

/-- Helper for Lemma 15.110.4: mapping irreducible closed subsets along a homeomorphism reflects
the inclusion order. -/
lemma homeomorph_irreducibleCloseds_map_rel_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (T T' : IrreducibleCloseds X) :
    IrreducibleCloseds.map e e.continuous T ≤ IrreducibleCloseds.map e e.continuous T' ↔ T ≤ T' := by
  constructor
  · intro h x hx
    -- Pull membership in the target closure back to an actual image point using closedness.
    have hex' : e x ∈ (e '' (T' : Set X)) := by
      have hclosed : IsClosed (e '' (T' : Set X)) := e.isClosedMap _ T'.isClosed
      have hmemT : e x ∈ (IrreducibleCloseds.map e e.continuous T : Set Y) := by
        rw [IrreducibleCloseds.coe_map]
        exact subset_closure ⟨x, hx, rfl⟩
      have hmem : e x ∈ (IrreducibleCloseds.map e e.continuous T' : Set Y) := h hmemT
      rw [IrreducibleCloseds.coe_map] at hmem
      rwa [hclosed.closure_eq] at hmem
    rcases hex' with ⟨x', hx', hx'eq⟩
    simpa [e.injective hx'eq] using hx'
  · intro h
    -- Forward inclusion is preserved by the canonical `IrreducibleCloseds.map`.
    exact IrreducibleCloseds.map_mono e.continuous h

/-- Helper for Lemma 15.110.4: mapping along a homeomorphism and then back along the inverse fixes
every irreducible closed subset. -/
lemma homeomorph_irreducibleCloseds_left_inv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (T : IrreducibleCloseds X) :
    IrreducibleCloseds.map e.symm e.symm.continuous (IrreducibleCloseds.map e e.continuous T) = T := by
  apply IrreducibleCloseds.ext
  apply Set.Subset.antisymm
  · -- Collapse the pulled-back closure using that the homeomorphic image of `T` is closed.
    rw [IrreducibleCloseds.coe_map]
    refine closure_minimal ?_ T.isClosed
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy' : y ∈ (e '' (T : Set X)) := by
      have hclosed : IsClosed (e '' (T : Set X)) := e.isClosedMap _ T.isClosed
      have hmem : y ∈ closure (e '' (T : Set X)) := by
        simpa [IrreducibleCloseds.coe_map] using hy
      rwa [hclosed.closure_eq] at hmem
    rcases hy' with ⟨x', hx', hx'eq⟩
    rw [← hx'eq]
    simpa using hx'
  · intro x hx
    -- Every point of `T` comes from the image point `e x` in the mapped irreducible closed set.
    rw [IrreducibleCloseds.coe_map]
    apply subset_closure
    refine ⟨e x, ?_, by simp⟩
    rw [IrreducibleCloseds.coe_map]
    exact subset_closure ⟨x, hx, rfl⟩

/-- Helper for Lemma 15.110.4: the inverse-side identity for irreducible closed subsets under a
homeomorphism. -/
lemma homeomorph_irreducibleCloseds_right_inv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (T : IrreducibleCloseds Y) :
    IrreducibleCloseds.map e e.continuous (IrreducibleCloseds.map e.symm e.symm.continuous T) = T := by
  -- This is the same argument as `homeomorph_irreducibleCloseds_left_inv`, applied to `e.symm`.
  simpa using homeomorph_irreducibleCloseds_left_inv (e := e.symm) T

/-- Helper for Lemma 15.110.4: a homeomorphism induces an order isomorphism on irreducible closed
subsets. -/
noncomputable def homeomorph_irreducibleCloseds_orderIso
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    IrreducibleCloseds X ≃o IrreducibleCloseds Y :=
  { toEquiv :=
      { toFun := fun T ↦ IrreducibleCloseds.map e e.continuous T
        invFun := fun T ↦ IrreducibleCloseds.map e.symm e.symm.continuous T
        left_inv := homeomorph_irreducibleCloseds_left_inv (e := e)
        right_inv := homeomorph_irreducibleCloseds_right_inv (e := e) }
    , map_rel_iff' := @homeomorph_irreducibleCloseds_map_rel_iff X Y _ _ e }

/-- Helper for Lemma 15.110.4: homeomorphic spaces are simultaneously catenary. -/
lemma homeomorph_catenarySpace_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    CatenarySpace X ↔ CatenarySpace Y := by
  -- Route correction: use the explicit `IrreducibleCloseds.map` construction instead of the
  -- unavailable older closure-image helper names from the previous attempt.
  constructor
  · intro hX
    -- Push the catenary-space owner along the induced order isomorphism.
    exact
      catenarySpace_of_irreducibleCloseds_orderIso
        (homeomorph_irreducibleCloseds_orderIso e) hX
  · intro hY
    -- Pull back along the inverse homeomorphism to return to the source space.
    exact
      catenarySpace_of_irreducibleCloseds_orderIso
        (homeomorph_irreducibleCloseds_orderIso e.symm) hY

/-- Helper for Lemma 15.110.4: catenarity is preserved under ring equivalence. -/
lemma ringEquiv_isCatenaryRing_iff
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    IsCatenaryRing R ↔ IsCatenaryRing S := by
  -- Route correction: transport catenarity through the prime-spectrum homeomorphism induced by the
  -- ring equivalence, instead of trying to rewrite the localization adapter directly.
  simpa [IsCatenaryRing] using
    (homeomorph_catenarySpace_iff (PrimeSpectrum.homeomorphOfRingEquiv e))

/-- Helper for Lemma 15.110.4: a localization of a quotient of a catenary ring is catenary. -/
lemma isCatenaryRing_of_isLocalizationOfQuotient
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : RingHom.IsLocalizationOfQuotient f) [IsCatenaryRing R] :
    IsCatenaryRing S := by
  rcases hf with ⟨I, _, M, _, rfl⟩
  -- First pass catenarity to the quotient appearing in the presentation.
  let _ : IsCatenaryRing (R ⧸ I) := quotient_catenaryRing (R := R) (I := I)
  -- Then apply the canonical localization theorem to the model localization.
  let _ : IsCatenaryRing (Localization M) := localization_isCatenaryRing (R := R ⧸ I) M
  -- Finally identify the arbitrary localization target with the canonical model via `algEquiv`.
  exact
    (ringEquiv_isCatenaryRing_iff
      ((IsLocalization.algEquiv M (Localization M) S).toRingEquiv)).1 inferInstance

/-- Helper for Lemma 15.110.4: the completed quotient ideal attached to a minimal prime is proper. -/
lemma completion_quotient_map_ne_top [IsFormallyCatenaryRing A] (p : minimalPrimes A) :
    Ideal.map (algebraMap A ACompletion) p.1 ≠ ⊤ := by
  let hff : (algebraMap A ACompletion).FaithfullyFlat :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A
  let _ : Module.FaithfullyFlat A ACompletion :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hff
  intro htop
  have hcomap :
      (Ideal.map (algebraMap A ACompletion) p.1).comap (algebraMap A ACompletion) = p.1 :=
    Ideal.comap_map_eq_self_of_faithfullyFlat (A := A) (B := ACompletion) p.1
  have hp_top : p.1 = ⊤ := by
    calc
      p.1 = (Ideal.map (algebraMap A ACompletion) p.1).comap (algebraMap A ACompletion) := by
        symm
        exact hcomap
      _ = ⊤ := by
        simp [htop]
  -- Contracting `⊤` back to `A` would force the chosen minimal prime to be improper.
  exact (Ideal.minimalPrimes_isPrime p.2).ne_top hp_top

/-- Helper for Lemma 15.110.4: the completion quotient by a minimal prime is a complete local ring. -/
lemma completion_quotient_isCompleteLocalRing [IsFormallyCatenaryRing A]
    (p : minimalPrimes A) :
    IsCompleteLocalRing (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1) := by
  -- The maximal-ideal completion is complete local, and proper quotients preserve that owner.
  exact
    quotient_isCompleteLocalRing
      (I := Ideal.map (algebraMap A ACompletion) p.1)
      (completion_quotient_map_ne_top (A := A) p)

/-- Helper for Lemma 15.110.4: the completion quotient by a minimal prime is a local ring. -/
local instance completion_quotient_isLocalRing [IsFormallyCatenaryRing A]
    (p : minimalPrimes A) :
    IsLocalRing (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1) := by
  let _ :
      IsCompleteLocalRing
        (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1) :=
    completion_quotient_isCompleteLocalRing (A := A) p
  infer_instance

/-- Helper for Lemma 15.110.4: the quotient map
`A / p → A^∧ / p A^∧` inherited from the completion map is flat. -/
lemma completion_quotient_algebraMap_flat [IsFormallyCatenaryRing A]
    (p : minimalPrimes A) :
    (quotientMapModIdeal (algebraMap A ACompletion) p.1).Flat := by
  -- Flatness survives quotienting along the faithfully flat completion map.
  let hff : (algebraMap A ACompletion).FaithfullyFlat :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A
  exact quotientMap_flat_of_flat (algebraMap A ACompletion) p.1 hff.flat

/-- Helper for Lemma 15.110.4: the quotient map
`A / p → A^∧ / p A^∧` is a local ring homomorphism. -/
lemma completion_quotient_algebraMap_local [IsFormallyCatenaryRing A]
    (p : minimalPrimes A) :
    IsLocalHom (quotientMapModIdeal (algebraMap A ACompletion) p.1) := by
  let q := quotientMapModIdeal (algebraMap A ACompletion) p.1
  -- Reflect units from the quotient target back through the quotient completion map and then
  -- through the original completion map.
  exact IsLocalHom.mk fun x hx ↦ by
    revert hx
    refine Quotient.inductionOn' x ?_
    intro a hx
    letI :
        Nontrivial (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1) :=
      Ideal.Quotient.nontrivial_iff.2 (completion_quotient_map_ne_top (A := A) p)
    have hqa :
        IsUnit ((Ideal.Quotient.mk
          (Ideal.map (algebraMap A ACompletion) p.1))
            ((algebraMap A ACompletion) a)) := by
      have hq_apply :
          q ((Ideal.Quotient.mk p.1) a) =
            (Ideal.Quotient.mk
              (Ideal.map (algebraMap A ACompletion) p.1))
              ((algebraMap A ACompletion) a) := by
        rfl
      exact hq_apply ▸ hx
    letI :
        IsLocalHom
          (Ideal.Quotient.mk (Ideal.map (algebraMap A ACompletion) p.1)) :=
      Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
    have hcompletion_unit : IsUnit ((algebraMap A ACompletion) a) :=
      IsUnit.of_map
        (Ideal.Quotient.mk (Ideal.map (algebraMap A ACompletion) p.1))
        ((algebraMap A ACompletion) a) hqa
    have ha_unit : IsUnit a := IsUnit.of_map (algebraMap A ACompletion) a hcompletion_unit
    exact ha_unit.map (Ideal.Quotient.mk p.1)

/-- Helper for Lemma 15.110.4: in the maximal-ideal completion of a Noetherian local ring, the
extended maximal ideal is the completed maximal ideal. -/
private lemma completion_map_maximalIdeal_eq_maximalIdeal
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (maximalIdeal R) =
      maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  let RCompletion := AdicCompletion (maximalIdeal R) R
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  letI : Field (R ⧸ (maximalIdeal R) ^ 1) := by
    let e : R ⧸ (maximalIdeal R) ^ 1 ≃+* R ⧸ maximalIdeal R :=
      Ideal.quotEquivOfEq (pow_one (maximalIdeal R))
    exact IsField.toField (e.toMulEquiv.isField (Field.toIsField _))
  have hker :
      Ideal.map (algebraMap R RCompletion) (maximalIdeal R) =
        RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) 1) := by
    simpa [pow_one] using
      completionIdeal_pow_eq_ker_evalₐ (maximalIdeal R)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) 1
  have hmax :
      Ideal.IsMaximal (Ideal.map (algebraMap R RCompletion) (maximalIdeal R)) := by
    simpa [hker] using
      (RingHom.ker_isMaximal_of_surjective
        (AdicCompletion.evalₐ (maximalIdeal R) 1)
        (AdicCompletion.surjective_evalₐ (maximalIdeal R) 1) :
          Ideal.IsMaximal (RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) 1)))
  letI :
      Ideal.IsMaximal (Ideal.map (algebraMap R RCompletion) (maximalIdeal R)) := hmax
  exact IsLocalRing.eq_maximalIdeal inferInstance

/-- Helper for Lemma 15.110.4: the maximal-ideal completion map induces a bijection on residue
fields. -/
private theorem maximalIdealCompletion_residueField_bijective
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Function.Bijective (ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
  let RCompletion := AdicCompletion (maximalIdeal R) R
  let φ : RCompletion →+* R ⧸ maximalIdeal R :=
    (AdicCompletion.evalOneₐ (maximalIdeal R)).toRingHom
  have hφ_surj : Function.Surjective φ :=
    AdicCompletion.evalOneₐ_surjective (maximalIdeal R)
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  letI : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R)) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  letI : IsLocalHom φ := Function.Surjective.isLocalHom _ hφ_surj
  have hquot :
      Function.Bijective (ResidueField.map (Ideal.Quotient.mk (maximalIdeal R))) :=
    residueField_bijective_of_surjective_localHom
      (f := Ideal.Quotient.mk (maximalIdeal R)) Ideal.Quotient.mk_surjective
  have hφ :
      Function.Bijective (ResidueField.map φ) :=
    residueField_bijective_of_surjective_localHom (f := φ) hφ_surj
  have hcomp :
      (ResidueField.map φ).comp (ResidueField.map (algebraMap R RCompletion)) =
        ResidueField.map (Ideal.Quotient.mk (maximalIdeal R)) := by
    -- Reducing the completion modulo its maximal ideal recovers the ordinary residue quotient.
    ext x
    simp [φ]
  constructor
  · intro x y hxy
    apply hquot.1
    simpa [Function.comp, hcomp] using congrArg (ResidueField.map φ) hxy
  · intro z
    obtain ⟨x, hx⟩ := hquot.2 ((ResidueField.map φ) z)
    refine ⟨x, ?_⟩
    apply hφ.1
    simpa [Function.comp, hcomp] using hx

/-- Helper for Lemma 15.110.4: the quotient completion map identifies the residue fields of
`A / p` and `A^∧ / pA^∧`. -/
noncomputable abbrev completion_quotient_residueField_equiv [IsFormallyCatenaryRing A]
    (p : minimalPrimes A) :
    ResidueField (A ⧸ p.1) ≃+*
      ResidueField (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1) :=
  let eSource : ResidueField (A ⧸ p.1) ≃+* ResidueField A :=
    residueField_equiv_of_quotient A p.1
  let eCompletion : ResidueField A ≃+* ResidueField ACompletion :=
    RingEquiv.ofBijective
      (ResidueField.map (algebraMap A ACompletion))
      (maximalIdealCompletion_residueField_bijective A)
  let eTarget :
      ResidueField
        (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1) ≃+*
          ResidueField ACompletion :=
    residueField_equiv_of_quotient ACompletion
      (Ideal.map (algebraMap A ACompletion) p.1)
  eSource.trans (eCompletion.trans eTarget.symm)

/-- Helper for Lemma 15.110.4: the quotient map
`A / p → A^∧ / p A^∧` is surjective on prime spectra. -/
lemma completion_quotient_algebraMap_comap_surjective [IsFormallyCatenaryRing A]
    (p : minimalPrimes A) :
    Function.Surjective
      (PrimeSpectrum.comap (quotientMapModIdeal (algebraMap A ACompletion) p.1)) := by
  let q := quotientMapModIdeal (algebraMap A ACompletion) p.1
  let πA : A →+* A ⧸ p.1 := Ideal.Quotient.mk p.1
  let πB :
      ACompletion →+*
        ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1 :=
    Ideal.Quotient.mk (Ideal.map (algebraMap A ACompletion) p.1)
  intro r
  let P : PrimeSpectrum A := PrimeSpectrum.comap πA r
  let hff : (algebraMap A ACompletion).FaithfullyFlat :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A
  letI : Module.FaithfullyFlat A ACompletion :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hff
  have hsurj :
      Function.Surjective (PrimeSpectrum.comap (algebraMap A ACompletion)) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  obtain ⟨Q, hQ⟩ := hsurj P
  have hp_le_P : p.1 ≤ P.asIdeal := by
    -- The quotient spectrum sits inside the zero locus of `p`.
    simpa [P, Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply] using
      (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.1 r).2
  have hp_le_Q : Ideal.map (algebraMap A ACompletion) p.1 ≤ Q.asIdeal := by
    -- Transport containment of `p` along the chosen lying-over prime `Q`.
    refine Ideal.map_le_iff_le_comap.mpr ?_
    have hQasIdeal :
        Ideal.comap (algebraMap A ACompletion) Q.asIdeal = P.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hQ
    calc
      p.1 ≤ P.asIdeal := hp_le_P
      _ = Ideal.comap (algebraMap A ACompletion) Q.asIdeal := hQasIdeal.symm
  let qbar : PrimeSpectrum (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1) :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus
      (Ideal.map (algebraMap A ACompletion) p.1)).symm ⟨Q, by simpa using hp_le_Q⟩
  refine ⟨qbar, ?_⟩
  apply (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.1).injective
  apply Subtype.ext
  change PrimeSpectrum.comap πA (PrimeSpectrum.comap q qbar) = PrimeSpectrum.comap πA r
  rw [← PrimeSpectrum.comap_comp_apply]
  have hcomp : q.comp πA = πB.comp (algebraMap A ACompletion) := by
    ext a
    rfl
  rw [hcomp, PrimeSpectrum.comap_comp_apply]
  have hqbar :
      PrimeSpectrum.comap πB qbar = Q := by
    change (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus
      (Ideal.map (algebraMap A ACompletion) p.1) qbar).1 = Q
    simpa [qbar] using congrArg Subtype.val
      ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus
        (Ideal.map (algebraMap A ACompletion) p.1)).apply_symm_apply
          ⟨Q, hp_le_Q⟩)
  simpa [P, hqbar] using hQ

/-- Helper for Lemma 15.110.4: the quotient map
`A / p → A^∧ / p A^∧` is faithfully flat. -/
lemma completion_quotient_algebraMap_faithfullyFlat [IsFormallyCatenaryRing A]
    (p : minimalPrimes A) :
    (quotientMapModIdeal (algebraMap A ACompletion) p.1).FaithfullyFlat := by
  -- Faithful flatness is the flat-plus-surjective-spectrum criterion.
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  exact
    ⟨completion_quotient_algebraMap_flat (A := A) p,
      completion_quotient_algebraMap_comap_surjective (A := A) p⟩

/-- Helper for Lemma 15.110.4: the polynomial coefficient-change map induced by
`A / p → A^∧ / pA^∧` is flat. -/
lemma mvPolynomial_map_flat_of_completion_quotient [IsFormallyCatenaryRing A]
    (p : minimalPrimes A) (n : ℕ) :
    (MvPolynomial.map (quotientMapModIdeal (algebraMap A ACompletion) p.1) :
      MvPolynomial (Fin n) (A ⧸ p.1) →+*
        MvPolynomial (Fin n)
          (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1)).Flat := by
  let R0 := A ⧸ p.1
  let Rhat := ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1
  let q : R0 →+* Rhat := quotientMapModIdeal (algebraMap A ACompletion) p.1
  let _ : Algebra R0 Rhat := q.toAlgebra
  let _ : Algebra (MvPolynomial (Fin n) R0) (MvPolynomial (Fin n) Rhat) :=
    MvPolynomial.algebraMvPolynomial
  -- This coefficient-change map is exactly the polynomial pushout of `q`.
  let _ : Algebra.IsPushout R0 Rhat (MvPolynomial (Fin n) R0) (MvPolynomial (Fin n) Rhat) :=
    inferInstance
  -- Flatness is stable under base change, so the polynomial pushout map is flat.
  simpa [R0, Rhat, q, RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_def] using
    (RingHom.Flat.isStableUnderBaseChange
      R0 Rhat (MvPolynomial (Fin n) R0) (MvPolynomial (Fin n) Rhat)
      (completion_quotient_algebraMap_flat (A := A) p))

/-- Helper for Lemma 15.110.4: once a maximal ideal `μ̂` above `μ` is chosen on the completed
polynomial side, the induced local map on the localizations is flat and local. -/
lemma localized_polynomial_completion_map_flat_local [IsFormallyCatenaryRing A]
    (p : minimalPrimes A) (n : ℕ)
    (μ : { m : MaximalSpectrum (MvPolynomial (Fin n) (A ⧸ p.1)) //
      Ideal.comap MvPolynomial.C m.asIdeal = maximalIdeal (A ⧸ p.1) })
    (μhat :
      { m :
          MaximalSpectrum
            (MvPolynomial (Fin n)
              (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1)) //
        Ideal.comap MvPolynomial.C m.asIdeal =
          maximalIdeal (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1) })
    (hcomap :
      μ.1.asIdeal =
        Ideal.comap (MvPolynomial.map (quotientMapModIdeal (algebraMap A ACompletion) p.1))
          μhat.1.asIdeal) :
    let f :=
      Localization.localRingHom μ.1.asIdeal μhat.1.asIdeal
        (MvPolynomial.map (quotientMapModIdeal (algebraMap A ACompletion) p.1)) hcomap
    f.Flat ∧ IsLocalHom f := by
  -- First localize the already-constructed flat coefficient-change map.
  dsimp
  constructor
  ·
    exact
      RingHom.Flat.localRingHom
        (mvPolynomial_map_flat_of_completion_quotient (A := A) p n)
        μhat.1.asIdeal μ.1.asIdeal hcomap
  ·
    -- Then use the canonical locality statement for `Localization.localRingHom`.
    exact
      Localization.isLocalHom_localRingHom
        μ.1.asIdeal μhat.1.asIdeal
        (MvPolynomial.map (quotientMapModIdeal (algebraMap A ACompletion) p.1))
        hcomap

/-- Helper for Lemma 15.110.4: every maximal localization of a polynomial ring over the completed
quotient is catenary. -/
lemma isCatenaryRing_completed_localized_polynomial [IsFormallyCatenaryRing A]
    (p : minimalPrimes A) (n : ℕ)
    (μhat :
      { m :
          MaximalSpectrum
            (MvPolynomial (Fin n)
              (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1)) //
        Ideal.comap MvPolynomial.C m.asIdeal =
          maximalIdeal (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1) }) :
    IsCatenaryRing (Localization.AtPrime μhat.1.asIdeal) := by
  let Rhat := ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1
  let _ : IsCompleteLocalRing Rhat := completion_quotient_isCompleteLocalRing (A := A) p
  let _ : IsNoetherianRing Rhat := inferInstance
  let hUC : UniversallyCatenaryRing Rhat := universallyCatenaryRing_of_isCompleteLocalRing Rhat
  let _ : UniversallyCatenaryRing Rhat := hUC
  -- First make the completed coefficient ring universally catenary via completeness.
  let _ : IsCatenaryRing (MvPolynomial (Fin n) Rhat) := hUC.catenary_of_finiteType
  -- Then localize the catenary polynomial ring at the chosen maximal ideal.
  infer_instance

/-- Helper for Lemma 15.110.4: the localized polynomial presentation over `A ⧸ p` is the unique
remaining catenary step in the source proof. -/
lemma catenary_localized_polynomial_of_completion_quotient [IsFormallyCatenaryRing A]
    (p : minimalPrimes A) (n : ℕ)
    (μ : { m : MaximalSpectrum (MvPolynomial (Fin n) (A ⧸ p.1)) //
      Ideal.comap MvPolynomial.C m.asIdeal = maximalIdeal (A ⧸ p.1) }) :
    IsCatenaryRing (Localization.AtPrime μ.1.asIdeal) := by
  -- Route correction: the proof is now reduced to the source's comparison
  -- `A[x]_μ → A^∧[x]_{μ̂}`, followed by Lemma `15.110.3` on the completed side.
  let q := quotientMapModIdeal (algebraMap A ACompletion) p.1
  have hq_flat : q.Flat := completion_quotient_algebraMap_flat (A := A) p
  have hq_local : IsLocalHom q := completion_quotient_algebraMap_local (A := A) p
  have hq_ff : q.FaithfullyFlat := completion_quotient_algebraMap_faithfullyFlat (A := A) p
  have hq_poly_flat :
      (MvPolynomial.map q :
        MvPolynomial (Fin n) (A ⧸ p.1) →+*
          MvPolynomial (Fin n)
            (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1)).Flat :=
    mvPolynomial_map_flat_of_completion_quotient (A := A) p n
  have hκ :
      ResidueField (A ⧸ p.1) ≃+*
        ResidueField (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1) :=
    completion_quotient_residueField_equiv (A := A) p
  -- TODO: use `hκ` to transport the closed point `μ` to a maximal ideal `μ̂` of the completed
  -- polynomial ring with the correct coefficient contraction, then apply
  -- `localized_polynomial_completion_map_flat_local` to obtain the flat local comparison
  -- `A[x]_μ → A^∧[x]_{μ̂}`. After that, the remaining source-faithful blocker is the
  -- equidimensionality proof for `Spec(A^∧[x]_{μ̂})`, via the minimal-prime analysis planned by
  -- Agent C; catenarity of the completed localization is already available from
  -- `isCatenaryRing_completed_localized_polynomial`.
  sorry

/-- Helper for Lemma 15.110.4: each quotient by a minimal prime of a formally catenary local ring
is universally catenary. -/
theorem universallyCatenaryRing_quotient_of_minimalPrime [IsFormallyCatenaryRing A]
    (p : minimalPrimes A) :
    UniversallyCatenaryRing.{u, u} (A ⧸ p.1) := by
  refine { catenary_of_finiteType := ?_ }
  intro S _ _ _
  let hlocalizations := isCatenaryRing_localization_tfae (R := S)
  -- Reduce catenarity of the finite-type algebra `S` to its maximal localizations.
  refine (hlocalizations.out 0 2).2 ?_
  intro m
  letI : Algebra.EssFiniteType S (Localization.AtPrime m.asIdeal) :=
    Algebra.EssFiniteType.of_isLocalization (Localization.AtPrime m.asIdeal) m.asIdeal.primeCompl
  letI : Algebra.EssFiniteType (A ⧸ p.1) (Localization.AtPrime m.asIdeal) :=
    Algebra.EssFiniteType.comp (A ⧸ p.1) S (Localization.AtPrime m.asIdeal)
  have hEssFiniteType :
      (algebraMap (A ⧸ p.1) (Localization.AtPrime m.asIdeal)).EssFiniteType :=
    (RingHom.essFiniteType_algebraMap).2 inferInstance
  -- Present the maximal localization as a localization of a quotient of a localized polynomial
  -- ring over `A ⧸ p`, and feed the polynomial-localization case into the quotient-localization
  -- transfer lemma.
  obtain ⟨n, μ, ψ, hψ, _hcomp⟩ :=
    exists_localized_polynomial_quotient_presentation
      (R := A ⧸ p.1) (S := Localization.AtPrime m.asIdeal)
      (algebraMap (A ⧸ p.1) (Localization.AtPrime m.asIdeal))
      hEssFiniteType
  let _ : IsCatenaryRing (Localization.AtPrime μ.1.asIdeal) :=
    catenary_localized_polynomial_of_completion_quotient (A := A) p n μ
  exact isCatenaryRing_of_isLocalizationOfQuotient ψ hψ

/-- Lemma 15.110.4: a formally catenary Noetherian local ring is universally catenary. -/
instance instUniversallyCatenaryRingOfIsFormallyCatenaryRing [IsFormallyCatenaryRing A] :
    UniversallyCatenaryRing.{u, u} A := by
  -- Reduce universal catenarity to the quotient rings by minimal primes.
  refine (universallyCatenaryRing_iff_forall_quotient_by_minimalPrime (R := A)).2 ?_
  intro p hp
  -- Package the minimal prime so the formal-catenary datum applies verbatim.
  exact universallyCatenaryRing_quotient_of_minimalPrime (A := A) ⟨p, hp⟩

end
