import Mathlib
import StacksProject_2024.Chap10.Lemma_10_154_6

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open RingHom

universe u

section

variable {R S S' K : Type u}
variable [CommRing R] [CommRing S] [CommRing S'] [Field K]
variable [Algebra R S] [Algebra R S'] [Algebra R K]
variable [Algebra S K] [Algebra S' K]
variable [IsScalarTower R S K] [IsScalarTower R S' K]
variable [HenselianLocalRing S] [HenselianLocalRing S']
variable [IsLocalHom (algebraMap S K)] [IsLocalHom (algebraMap S' K)]

/-!
The proof uses Lemma `10.154.6` in its residue-field-point form.  The auxiliary lemmas
below bridge the ordinary local-ring residue field `ResidueField A` used by `ResidueField.lift`
with the prime-residue-field model `(maximalIdeal A).ResidueField` used in that lifting theorem.
-/

/-- Helper for Chap10 Lemma 10 154 7: the residue field of the maximal ideal agrees with the
ordinary residue field of a local ring. -/
noncomputable def residueFieldEquivOfMaximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- Helper for Chap10 Lemma 10 154 7: the maximal-ideal residue-field comparison sends the
class of an element to its ordinary residue class. -/
lemma residueFieldEquivOfMaximalIdeal_apply_algebraMap
    (A : Type u) [CommRing A] [IsLocalRing A] (a : A) :
    residueFieldEquivOfMaximalIdeal A (algebraMap A (maximalIdeal A).ResidueField a) =
      residue A a := by
  -- Proof comment: the displayed element is the image of the ordinary residue class under the
  -- inverse equivalence, so applying the equivalence gives back that class.
  exact (residueFieldEquivOfMaximalIdeal A).apply_symm_apply (residue A a)

/-- Helper for Chap10 Lemma 10 154 7: the common-field map on the maximal-ideal residue field. -/
noncomputable abbrev maximalIdealLiftToCommonField
    (A K : Type u) [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
    [IsLocalHom (algebraMap A K)] :
    (maximalIdeal A).ResidueField →+* K :=
  (ResidueField.lift (algebraMap A K)).comp (residueFieldEquivOfMaximalIdeal A).toRingHom

/-- Helper for Chap10 Lemma 10 154 7: the common-field lift sends the class of an element to its
image in the common field. -/
lemma maximalIdealLiftToCommonField_apply_algebraMap
    (A K : Type u) [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
    [IsLocalHom (algebraMap A K)] (a : A) :
    maximalIdealLiftToCommonField A K (algebraMap A (maximalIdeal A).ResidueField a) =
      algebraMap A K a := by
  -- Proof comment: rewrite through the ordinary residue field and use the defining computation
  -- rule for `ResidueField.lift`.
  simp [maximalIdealLiftToCommonField, residueFieldEquivOfMaximalIdeal_apply_algebraMap]

/-- Helper for Chap10 Lemma 10 154 7: bijectivity of the ordinary residue-field lift transfers to
the maximal-ideal residue-field model. -/
lemma maximalIdealLiftToCommonField_bijective
    {A K : Type u} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
    [IsLocalHom (algebraMap A K)]
    (hκ : Function.Bijective (ResidueField.lift (algebraMap A K))) :
    Function.Bijective (maximalIdealLiftToCommonField A K) := by
  -- Proof comment: compose the given bijection with the residue-field equivalence.
  exact hκ.comp (residueFieldEquivOfMaximalIdeal A).bijective

/-- Helper for Chap10 Lemma 10 154 7: the equivalence with the common field has the expected
value on residue classes of elements. -/
lemma commonFieldEquivOfMaximalIdeal_apply_algebraMap
    {A K : Type u} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
    [IsLocalHom (algebraMap A K)]
    (hκ : Function.Bijective (ResidueField.lift (algebraMap A K))) (a : A) :
    (RingEquiv.ofBijective (maximalIdealLiftToCommonField A K)
      (maximalIdealLiftToCommonField_bijective (A := A) (K := K) hκ))
        (algebraMap A (maximalIdeal A).ResidueField a) = algebraMap A K a := by
  -- Proof comment: `RingEquiv.ofBijective` has the same forward map as the packaged lift.
  exact maximalIdealLiftToCommonField_apply_algebraMap A K a

/-- Helper for Chap10 Lemma 10 154 7: two local maps to a common field have the same contraction
of their maximal ideals to the base ring. -/
lemma maximalIdeal_under_eq_of_common_residueField
    {A T K R : Type u} [CommRing R] [CommRing A] [CommRing T] [Field K]
    [Algebra R A] [Algebra R T] [Algebra R K]
    [Algebra A K] [Algebra T K]
    [IsScalarTower R A K] [IsScalarTower R T K]
    [IsLocalRing A] [IsLocalRing T]
    [IsLocalHom (algebraMap A K)] [IsLocalHom (algebraMap T K)] :
    (maximalIdeal A).under R = (maximalIdeal T).under R := by
  -- Proof comment: membership in either contraction is membership in the pullback of the
  -- maximal ideal of the common field along the corresponding local map.
  ext r
  simp [Ideal.under, ← IsLocalRing.maximalIdeal_comap (algebraMap A K),
    ← IsLocalRing.maximalIdeal_comap (algebraMap T K)]

/-- Helper for Chap10 Lemma 10 154 7: the residue-field comparison through the common field is
compatible with the maps from the contracted base residue field. -/
lemma residueFieldComparison_comp_base_eq
    {A T K R : Type u} [CommRing R] [CommRing A] [CommRing T] [Field K]
    [Algebra R A] [Algebra R T] [Algebra R K]
    [Algebra A K] [Algebra T K]
    [IsScalarTower R A K] [IsScalarTower R T K]
    [IsLocalRing A] [IsLocalRing T]
    [IsLocalHom (algebraMap A K)] [IsLocalHom (algebraMap T K)]
    (hκT : Function.Bijective (ResidueField.lift (algebraMap T K))) :
    let hq : (maximalIdeal A).under R = (maximalIdeal T).under R :=
      maximalIdeal_under_eq_of_common_residueField (R := R) (A := A) (T := T) (K := K)
    let κTEquiv : (maximalIdeal T).ResidueField ≃+* K :=
      RingEquiv.ofBijective (maximalIdealLiftToCommonField T K)
        (maximalIdealLiftToCommonField_bijective (A := T) (K := K) hκT)
    let τ : (maximalIdeal A).ResidueField →+* (maximalIdeal T).ResidueField :=
      κTEquiv.symm.toRingHom.comp (maximalIdealLiftToCommonField A K)
    τ.comp (Ideal.ResidueField.map ((maximalIdeal A).under R) (maximalIdeal A)
        (algebraMap R A) rfl) =
      Ideal.ResidueField.map ((maximalIdeal A).under R) (maximalIdeal T)
        (algebraMap R T) hq := by
  intro hq κTEquiv τ
  -- Proof comment: after applying the bijective target comparison with `K`, both maps send a
  -- base element to its image in `K`.
  apply Ideal.ResidueField.ringHom_ext
  apply RingHom.ext
  intro r
  apply κTEquiv.injective
  simpa [τ, κTEquiv, Ideal.ResidueField.map_algebraMap,
    maximalIdealLiftToCommonField_apply_algebraMap,
    residueFieldEquivOfMaximalIdeal_apply_algebraMap] using
    (IsScalarTower.algebraMap_apply R A K r).symm.trans
      (IsScalarTower.algebraMap_apply R T K r)

/-- Helper for Chap10 Lemma 10 154 7: the residue-point condition in Lemma `10.154.6` is
equivalent to compatibility with the two maps to the common field. -/
lemma algHom_commonField_compat_iff_residuePoint
    {A T K R : Type u} [CommRing R] [CommRing A] [CommRing T] [Field K]
    [Algebra R A] [Algebra R T] [Algebra R K]
    [Algebra A K] [Algebra T K]
    [IsScalarTower R A K] [IsScalarTower R T K]
    [IsLocalRing A] [HenselianLocalRing T]
    [IsLocalHom (algebraMap A K)] [IsLocalHom (algebraMap T K)]
    (hκT : Function.Bijective (ResidueField.lift (algebraMap T K)))
    (f : A →ₐ[R] T) :
    let hq : (maximalIdeal A).under R = (maximalIdeal T).under R :=
      maximalIdeal_under_eq_of_common_residueField (R := R) (A := A) (T := T) (K := K)
    let κTEquiv : (maximalIdeal T).ResidueField ≃+* K :=
      RingEquiv.ofBijective (maximalIdealLiftToCommonField T K)
        (maximalIdealLiftToCommonField_bijective (A := T) (K := K) hκT)
    let τ : (maximalIdeal A).ResidueField →+* (maximalIdeal T).ResidueField :=
      κTEquiv.symm.toRingHom.comp (maximalIdealLiftToCommonField A K)
    ∀ hτ :
      τ.comp (Ideal.ResidueField.map ((maximalIdeal A).under R) (maximalIdeal A)
          (algebraMap R A) rfl) =
        Ideal.ResidueField.map ((maximalIdeal A).under R) (maximalIdeal T)
          (algebraMap R T) hq,
    (((Algebra.ofId T (maximalIdeal T).ResidueField).restrictScalars R).comp f =
        baseChangeResiduePoint (q := maximalIdeal A) hq τ hτ) ↔
      (algebraMap T K).comp (f : A →+* T) = algebraMap A K := by
  intro hq κTEquiv τ hτ
  constructor
  · intro hpoint
    -- Proof comment: push the residue-point equality to `K`; the chosen comparison turns both
    -- sides into the desired common-field maps.
    apply RingHom.ext
    intro a
    have hx := congrFun (congrArg DFunLike.coe hpoint) a
    have hxK := congrArg κTEquiv hx
    simpa [baseChangeResiduePoint, τ, κTEquiv, commonFieldEquivOfMaximalIdeal_apply_algebraMap,
      maximalIdealLiftToCommonField_apply_algebraMap,
      residueFieldEquivOfMaximalIdeal_apply_algebraMap]
      using hxK
  · intro hK
    -- Proof comment: pull the common-field equality back along the bijective target comparison to
    -- recover the residue-point equality.
    apply AlgHom.ext
    intro a
    apply κTEquiv.injective
    have hx := congrFun (congrArg DFunLike.coe hK) a
    simpa [baseChangeResiduePoint, τ, κTEquiv, commonFieldEquivOfMaximalIdeal_apply_algebraMap,
      maximalIdealLiftToCommonField_apply_algebraMap,
      residueFieldEquivOfMaximalIdeal_apply_algebraMap]
      using hx

/-- Helper for Chap10 Lemma 10 154 7: an ind-étale algebra over a henselian local target has a
unique algebra map compatible with a common residue field. -/
lemma existsUnique_algHom_of_filteredColimitOfEtale_of_common_residueField
    {A T K R : Type u} [CommRing R] [CommRing A] [CommRing T] [Field K]
    [Algebra R A] [Algebra R T] [Algebra R K]
    [Algebra A K] [Algebra T K]
    [IsScalarTower R A K] [IsScalarTower R T K]
    [IsLocalRing A] [HenselianLocalRing T]
    [IsLocalHom (algebraMap A K)] [IsLocalHom (algebraMap T K)]
    (hA : (algebraMap R A).IsFilteredColimitOfEtale)
    (hκT : Function.Bijective (ResidueField.lift (algebraMap T K))) :
    ∃! f : A →ₐ[R] T, (algebraMap T K).comp (f : A →+* T) = algebraMap A K := by
  let hq : (maximalIdeal A).under R = (maximalIdeal T).under R :=
    maximalIdeal_under_eq_of_common_residueField (R := R) (A := A) (T := T) (K := K)
  let κTEquiv : (maximalIdeal T).ResidueField ≃+* K :=
    RingEquiv.ofBijective (maximalIdealLiftToCommonField T K)
      (maximalIdealLiftToCommonField_bijective (A := T) (K := K) hκT)
  let τ : (maximalIdeal A).ResidueField →+* (maximalIdeal T).ResidueField :=
    κTEquiv.symm.toRingHom.comp (maximalIdealLiftToCommonField A K)
  have hτ :
      τ.comp (Ideal.ResidueField.map ((maximalIdeal A).under R) (maximalIdeal A)
          (algebraMap R A) rfl) =
        Ideal.ResidueField.map ((maximalIdeal A).under R) (maximalIdeal T)
          (algebraMap R T) hq := by
    -- Proof comment: package the comparison through `K` as the compatibility input required by
    -- the imported residue-point lifting theorem.
    simpa [hq, κTEquiv, τ] using
      (residueFieldComparison_comp_base_eq (R := R) (A := A) (T := T) (K := K) hκT)
  obtain ⟨f, hf, huniq⟩ :=
    existsUnique_algHom_of_filteredColimitOfEtale_residuePoint
      (R := R) (A := A) (S := T) (hA := hA) (q := maximalIdeal A) hq τ hτ
  refine ⟨f, ?_, ?_⟩
  · -- Proof comment: translate the residue-point property of the constructed lift to
    -- compatibility with the common field.
    exact ((algHom_commonField_compat_iff_residuePoint
      (R := R) (A := A) (T := T) (K := K) hκT f) hτ).mp hf
  · intro g hg
    -- Proof comment: translate a competing common-field-compatible map back to the residue-point
    -- predicate and apply the uniqueness from Lemma `10.154.6`.
    apply huniq
    exact ((algHom_commonField_compat_iff_residuePoint
      (R := R) (A := A) (T := T) (K := K) hκT g) hτ).mpr hg

/- Domain-style sampling:
- primary domain: henselian local rings, filtered colimits of étale algebras, and residue-field
  comparisons through maps to a common field;
- sampled owner declarations of the same kind:
  `HenselianLocalRing`,
  `RingHom.IsFilteredColimitOfEtale`,
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`,
  `ResidueField.lift`;
- best owner abstraction: the canonical owners here are `HenselianLocalRing`,
  `IsLocalHom`, and `RingHom.IsFilteredColimitOfEtale`; the present lemma stays
  `source-facing`, since it adds the extra mathematical content of comparing two henselian local
  `R`-algebras through a common residue field target `K`;
- primitive data vs. derived API:
  the primitive inputs are the two ind-étale `R`-algebra structures and the two bijective
  residue-field comparison maps to `K`;
  the derived API is the unique compatible `R`-algebra equivalence `S ≃ₐ[R] S'`.

Source/core/bridge triage:
- `source-facing`: the present uniqueness statement for two henselian local `R`-algebras with a
  common residue-field identification;
- `core/canonical`: `HenselianLocalRing`, `IsLocalHom`, `RingHom.IsFilteredColimitOfEtale`, and
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`;
- `bridge/view`: the chosen field `K` and the bijectivity of `ResidueField.lift` for the two
  structural maps.
-/

-- Proof sketch: apply Lemma `10.154.6` with `A = S` and target `S'`, using the map
-- `ResidueField.lift (algebraMap S K)` composed with the inverse of
-- `ResidueField.lift (algebraMap S' K)` to obtain a unique `R`-algebra map `S → S'`
-- compatible with the maps to `K`, and similarly a unique map `S' → S`. The two composites are
-- the unique endomorphisms compatible with the corresponding maps to `K`, so they are identities;
-- hence the two maps are inverse `R`-algebra isomorphisms, unique by the same compatibility
-- condition.
/-- Chap10 Lemma 10 154 7: given a commutative diagram `S → K ← S'` over `R` in which `S` and `S'` are
henselian local rings, both are filtered colimits of étale `R`-algebras, and the maps to the
field `K` identify `K` with the residue field of each source, there exists a unique
`R`-algebra isomorphism `S ≃ₐ[R] S'` compatible with the maps to `K`. -/
@[stacks 08HT]
lemma existsUnique_algEquiv_of_henselianLocal_of_filteredColimitOfEtale_of_common_residueField
    (hS : (algebraMap R S).IsFilteredColimitOfEtale)
    (hS' : (algebraMap R S').IsFilteredColimitOfEtale)
    (hκ : Function.Bijective (ResidueField.lift (algebraMap S K)))
    (hκ' : Function.Bijective (ResidueField.lift (algebraMap S' K))) :
    ∃! e : S ≃ₐ[R] S', (algebraMap S' K).comp (e : S →+* S') = algebraMap S K := by
  -- Proof comment: first obtain the unique compatible algebra homomorphisms in both directions.
  obtain ⟨f, hf, huniqF⟩ :=
    existsUnique_algHom_of_filteredColimitOfEtale_of_common_residueField
      (R := R) (A := S) (T := S') (K := K) hS hκ'
  obtain ⟨g, hg, _⟩ :=
    existsUnique_algHom_of_filteredColimitOfEtale_of_common_residueField
      (R := R) (A := S') (T := S) (K := K) hS' hκ
  -- Proof comment: uniqueness in the endomorphism cases identifies the two composites with the
  -- identity maps, which is stronger than equality after mapping to `K`.
  obtain ⟨_, _, huniqS⟩ :=
    existsUnique_algHom_of_filteredColimitOfEtale_of_common_residueField
      (R := R) (A := S) (T := S) (K := K) hS hκ
  obtain ⟨_, _, huniqS'⟩ :=
    existsUnique_algHom_of_filteredColimitOfEtale_of_common_residueField
      (R := R) (A := S') (T := S') (K := K) hS' hκ'
  have hcompS :
      (algebraMap S K).comp ((g.comp f : S →ₐ[R] S) : S →+* S) =
        algebraMap S K := by
    -- Proof comment: compose the two common-field compatibility equations.
    apply RingHom.ext
    intro x
    have hgx := congrFun (congrArg DFunLike.coe hg) (f x)
    have hfx := congrFun (congrArg DFunLike.coe hf) x
    simpa [RingHom.comp_apply, AlgHom.comp_apply] using hgx.trans hfx
  have hidS :
      (algebraMap S K).comp ((AlgHom.id R S : S →ₐ[R] S) : S →+* S) =
        algebraMap S K := by
    -- Proof comment: the identity endomorphism is visibly compatible with the map to `K`.
    simp
  have hgf : g.comp f = AlgHom.id R S := by
    -- Proof comment: both `g.comp f` and the identity are the unique compatible endomorphism of
    -- `S`.
    exact (huniqS (g.comp f) hcompS).trans ((huniqS (AlgHom.id R S) hidS).symm)
  have hcompS' :
      (algebraMap S' K).comp ((f.comp g : S' →ₐ[R] S') : S' →+* S') =
        algebraMap S' K := by
    -- Proof comment: the same compatibility calculation applies to the composite on `S'`.
    apply RingHom.ext
    intro x
    have hfx := congrFun (congrArg DFunLike.coe hf) (g x)
    have hgx := congrFun (congrArg DFunLike.coe hg) x
    simpa [RingHom.comp_apply, AlgHom.comp_apply] using hfx.trans hgx
  have hidS' :
      (algebraMap S' K).comp ((AlgHom.id R S' : S' →ₐ[R] S') : S' →+* S') =
        algebraMap S' K := by
    -- Proof comment: the identity endomorphism of `S'` is compatible with its map to `K`.
    simp
  have hfg : f.comp g = AlgHom.id R S' := by
    -- Proof comment: uniqueness gives the inverse law on `S'`.
    exact (huniqS' (f.comp g) hcompS').trans ((huniqS' (AlgHom.id R S') hidS').symm)
  let e : S ≃ₐ[R] S' := AlgEquiv.ofAlgHom f g hfg hgf
  refine ⟨e, ?_, ?_⟩
  · -- Proof comment: the constructed equivalence has underlying algebra homomorphism `f`.
    simpa [e] using hf
  · intro e' he'
    -- Proof comment: any compatible equivalence has the same underlying algebra homomorphism as
    -- the unique compatible map `f`, hence is equal to `e`.
    have heqAlg : (e' : S →ₐ[R] S') = f := huniqF (e' : S →ₐ[R] S') he'
    apply AlgEquiv.ext
    intro x
    simpa [e] using congrFun (congrArg DFunLike.coe heqAlg) x

end
