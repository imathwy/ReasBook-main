import Mathlib
import StacksProject_2024.Chap10.Lemma_10_45_3
import StacksProject_2024.Chap10.Definition_10_110_7
import StacksProject_2024.Chap10.Definition_10_137_10
import StacksProject_2024.Chap10.Lemma_10_118_3
import StacksProject_2024.Chap10.Lemma_10_137_2
import StacksProject_2024.Chap10.Lemma_10_140_9
import StacksProject_2024.Chap10.Lemma_10_163_10
import StacksProject_2024.Chap10.Lemma_10_164_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum
open GenericFlatness IsLocalization Localization
open scoped PrimeSpectrum
open scoped TensorProduct PerfectClosure

/- 
Domain-style sampling:
* primary domain: source-facing loci on `Spec R` defined by local properties of prime
  localizations;
* sampled owner declarations of the same kind:
  `PrimeSpectrum.normalLocus`,
  `PrimeSpectrum.dimensionStratum`,
  `PrimeSpectrum.cohenMacaulayFiberLocus`,
  `IsRegularLocalRing`;
* best owner abstraction: the regular locus should be owned by `PrimeSpectrum.regularLocus`,
  parallel to the other spectrum-locus owners already used in the project;
* primitive vs. derived: the primitive pointwise datum is
  `IsRegularLocalRing (Localization.AtPrime p.asIdeal)`, while the `J-0`/`J-1`/`J-2` conditions are
  derived chapter-level owners phrased in terms of openness properties of that locus.

Source/core/bridge triage:
* `source-facing`: `PrimeSpectrum.regularLocus R` and the chapter owners `IsJ0Ring`, `IsJ1Ring`,
  and `IsJ2Ring`;
* `core/canonical`: `Localization.AtPrime` and `IsRegularLocalRing`;
* `bridge/view`: the open-subset and openness criteria expressing the `J-*` conditions through the
  regular locus.
-/

namespace PrimeSpectrum

section

variable (R : Type u) [CommRing R]

/-- The regular locus of `Spec R` consists of the primes whose local rings are regular. -/
def regularLocus : Set (PrimeSpectrum R) :=
  { p | IsRegularLocalRing (Localization.AtPrime p.asIdeal) }

/- Textbook regular-locus notation on `Spec R`, attached to the owner
`PrimeSpectrum.regularLocus`. -/
scoped[PrimeSpectrum] notation "Reg(Spec " R ")" => regularLocus R

/-- Membership in `PrimeSpectrum.regularLocus R` means that the corresponding localization is a
regular local ring. -/
@[simp] theorem mem_regularLocus (p : PrimeSpectrum R) :
    p ∈ Reg(Spec R) ↔ IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
  Iff.rfl

-- The specialization relation `p ⤳ q` means `p ⊆ q`, so `R_p` is a localization of the
-- regular local ring `R_q`. Regularity is preserved by this second localization.
/-- Helper for Definition 15.47.1: if `p ⤳ q` and `R_q` is regular local, then `R_p` is regular
local. -/
theorem localizationAtPrime_isRegularLocalRing_of_specializes {p q : PrimeSpectrum R}
    (hpq : p ⤳ q) [IsRegularLocalRing (Localization.AtPrime q.asIdeal)] :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  have hp_le_q : p.asIdeal ≤ q.asIdeal := by
    exact (le_iff_specializes p q).2 hpq
  let p' : Ideal (Localization.AtPrime q.asIdeal) :=
    Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal
  have hdisj : Disjoint (q.asIdeal.primeCompl : Set R) p.asIdeal := by
    refine Set.disjoint_left.mpr fun x hx hxq ↦ ?_
    exact hx (hp_le_q hxq)
  have hp'_comap :
      Ideal.comap (algebraMap R (Localization.AtPrime q.asIdeal)) p' = p.asIdeal := by
    simpa [p'] using
      IsLocalization.comap_map_of_isPrime_disjoint
        q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) p.2 hdisj
  letI : p'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) p.asIdeal p.2 hdisj
  let pS : PrimeSpectrum (Localization.AtPrime q.asIdeal) := ⟨p', inferInstance⟩
  letI : IsLocalization.AtPrime (Localization.AtPrime p') p.asIdeal := by
    simpa [hp'_comap] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        q.asIdeal.primeCompl (Localization.AtPrime p') p')
  letI : IsRegularRing (Localization.AtPrime q.asIdeal) := inferInstance
  have hpS_reg : IsRegularLocalRing (Localization.AtPrime pS.asIdeal) :=
    IsRegularRing.isRegularLocalRing_atPrime pS
  letI : IsRegularLocalRing (Localization.AtPrime p') := hpS_reg
  let e : Localization.AtPrime p.asIdeal ≃ₐ[R] Localization.AtPrime p' :=
    IsLocalization.algEquiv p.asIdeal.primeCompl _ _
  exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm

-- Proof sketch: if `p ⤳ q`, then `p ⊆ q`, so the prime `p` defines a prime of the regular local
-- ring `R_q`. Localizing `R_q` at that prime recovers `R_p`, and localizations of a regular local
-- ring are regular local.
/-- The regular locus of `Spec R` is stable under generalization. -/
theorem regularLocus_stableUnderGeneralization (R : Type u) [CommRing R] :
    StableUnderGeneralization (Reg(Spec R)) := by
  intro p q hpq hq
  -- The helper turns regularity at the specialization `p` into regularity at the generalization
  -- `q`.
  have hp_reg : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
    simpa using hq
  letI : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := hp_reg
  simpa using
    (localizationAtPrime_isRegularLocalRing_of_specializes (R := R) (p := q) (q := p) hpq :
      IsRegularLocalRing (Localization.AtPrime q.asIdeal))

end

end PrimeSpectrum

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- A principal localization is regular exactly when the corresponding basic open subset of
`Spec A` lies in the regular locus. -/
theorem isRegularRing_localizationAway_iff_basicOpen_subset_regularLocus (a : A) :
    IsRegularRing (Localization.Away a) ↔
      (basicOpen a : Set (PrimeSpectrum A)) ⊆ Reg(Spec A) := by
  constructor
  · intro h
    letI : IsRegularRing (Localization.Away a) := h
    intro p hp
    rw [← localization_away_comap_range (Localization.Away a) a] at hp
    rcases hp with ⟨q, rfl⟩
    let e :
        Localization.AtPrime (comap (algebraMap A (Localization.Away a)) q).asIdeal ≃ₐ[A]
          Localization.AtPrime q.asIdeal :=
      IsLocalization.localizationLocalizationAtPrimeIsoLocalization (Submonoid.powers a) q.asIdeal
    letI : IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
      IsRegularRing.isRegularLocalRing_atPrime q
    simpa using
      (IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm :
        IsRegularLocalRing
          (Localization.AtPrime (comap (algebraMap A (Localization.Away a)) q).asIdeal))
  · intro ha
    refine
      { toIsNoetherian :=
          IsLocalization.isNoetherianRing (Submonoid.powers a) (Localization.Away a) inferInstance
        isRegularLocalRing_atPrime := fun q ↦ ?_ }
    let p : PrimeSpectrum A := comap (algebraMap A (Localization.Away a)) q
    have hp_basic : p ∈ basicOpen a := by
      change p ∈ (basicOpen a : Set (PrimeSpectrum A))
      rw [← localization_away_comap_range (Localization.Away a) a]
      exact ⟨q, rfl⟩
    have hp_reg : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
      simpa using ha hp_basic
    letI : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := hp_reg
    let e :
        Localization.AtPrime p.asIdeal ≃ₐ[A] Localization.AtPrime q.asIdeal :=
      IsLocalization.localizationLocalizationAtPrimeIsoLocalization (Submonoid.powers a) q.asIdeal
    exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

/-- Definition 15.47.1 (1): a Noetherian ring is `J-0` if the regular locus of `Spec R`
contains a nonempty open subset. -/
@[stacks 07P7]
class IsJ0Ring (R : Type u) [CommRing R] : Prop extends IsNoetherianRing R where
  /-- The regular locus of `Spec R` contains a nonempty open subset. -/
  exists_nonempty_open_subset_regularLocus :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ U.Nonempty ∧ U ⊆ Reg(Spec R)

variable {R : Type u} [CommRing R]

/-- The `J-0` condition is exactly the existence of a nonempty open subset of `Spec R` contained
in the regular locus. -/
theorem isJ0Ring_iff_exists_nonempty_open_subset_regularLocus {R : Type u} [CommRing R]
    [IsNoetherianRing R] :
    IsJ0Ring R ↔
      ∃ U : Set (PrimeSpectrum R),
        IsOpen U ∧ U.Nonempty ∧ U ⊆ Reg(Spec R) :=
  ⟨fun h ↦ h.exists_nonempty_open_subset_regularLocus,
    fun h ↦ { exists_nonempty_open_subset_regularLocus := h }⟩

/-- A regular ring is `J-0`. -/
theorem isJ0Ring_of_isRegularRing (R : Type u) [CommRing R] [Nontrivial R] [IsRegularRing R] :
    IsJ0Ring R := by
  refine (isJ0Ring_iff_exists_nonempty_open_subset_regularLocus).2
    ⟨Set.univ, isOpen_univ, Set.univ_nonempty, ?_⟩
  intro p _
  simpa using IsRegularRing.isRegularLocalRing_atPrime p

/-- Helper for Definition 15.47.1: the regular locus of a regular ring is all of its spectrum. -/
theorem regularLocus_eq_univ_of_isRegularRing (R : Type u) [CommRing R] [IsRegularRing R] :
    Reg(Spec R) = Set.univ := by
  -- Every localization at a prime of a regular ring is regular local by definition.
  ext p
  constructor
  · intro _
    simp
  · intro _
    simpa using IsRegularRing.isRegularLocalRing_atPrime p

/-- In a `J-0` domain, some nonzero principal localization is a regular ring. -/
theorem exists_nonzero_isRegularRing_localizationAway_of_isJ0Ring (A : Type u)
    [CommRing A] [IsDomain A] [IsJ0Ring A] :
    ∃ a : A, a ≠ 0 ∧ IsRegularRing (Localization.Away a) := by
  obtain ⟨U, hU_open, hU_nonempty, hU_reg⟩ :=
    (isJ0Ring_iff_exists_nonempty_open_subset_regularLocus).1 (inferInstance : IsJ0Ring A)
  rcases hU_nonempty with ⟨p, hpU⟩
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, hp_basic, hbasicU⟩ :=
    isBasis_basic_opens.exists_subset_of_mem_open hpU hU_open
  have ha : a ≠ 0 := by
    intro ha0
    exact (mem_basicOpen a p).1 hp_basic (ha0 ▸ Ideal.zero_mem _)
  exact ⟨a, ha,
    (isRegularRing_localizationAway_iff_basicOpen_subset_regularLocus a).2 (hbasicU.trans hU_reg)⟩

/-- Definition 15.47.1 (2): a Noetherian ring is `J-1` if the regular locus of `Spec R` is open. -/
@[stacks 07P7]
class IsJ1Ring (R : Type u) [CommRing R] : Prop extends IsNoetherianRing R where
  /-- The regular locus of `Spec R` is open. -/
  regularLocus_isOpen : IsOpen (Reg(Spec R))

/-- The `J-1` condition is exactly openness of the regular locus. -/
theorem isJ1Ring_iff_regularLocus_isOpen {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsJ1Ring R ↔ IsOpen (Reg(Spec R)) :=
  ⟨fun h ↦ h.regularLocus_isOpen, fun h ↦ { regularLocus_isOpen := h }⟩

/-- Definition 15.47.1 (3): a Noetherian ring is `J-2` if every finite type `R`-algebra is
`J-1`. -/
@[stacks 07P7]
class IsJ2Ring (R : Type u) [CommRing R] : Prop where
  /-- Every finite type `R`-algebra has open regular locus. -/
  isJ1Ring_of_finiteType {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    IsJ1Ring A

attribute [instance] IsJ2Ring.isJ1Ring_of_finiteType

/-- The `J-2` condition is exactly the requirement that every finite type `R`-algebra is `J-1`. -/
theorem isJ2Ring_iff_forall_finiteType_isJ1 {R : Type u} [CommRing R] :
    IsJ2Ring.{u, v} R ↔
      ∀ (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A], IsJ1Ring A :=
  ⟨fun h _ _ _ _ ↦ h.isJ1Ring_of_finiteType,
    fun h ↦
      { isJ1Ring_of_finiteType := fun {A} [_] [_] [_] ↦ h A }⟩

section

variable (K : Type u) [Field K]

-- Proof sketch: `Spec K` has the single regular point, so the regular locus contains the
-- nonempty open subset `univ`.
/-- A field is `J-0`. -/
instance : IsJ0Ring K := by
  -- A field is a regular ring, so the whole spectrum witnesses the `J-0` condition.
  exact isJ0Ring_of_isRegularRing K

-- Proof sketch: `Spec K` has a single point and its local ring is the field `K`, hence the
-- regular locus is all of `Spec K`, which is open.
/-- A field is `J-1`. -/
instance : IsJ1Ring K := by
  -- The regular locus is all of `Spec K`, so openness is immediate.
  rw [isJ1Ring_iff_regularLocus_isOpen]
  simpa [regularLocus_eq_univ_of_isRegularRing K] using
    (isOpen_univ : IsOpen (Set.univ : Set (PrimeSpectrum K)))

/-- Helper for Definition 15.47.1: `J-0` descends along an injective finite type map of
domains. -/
private theorem isJ0Ring_of_injective_finiteType_domain_local
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsDomain R] [IsDomain S] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) [IsJ0Ring S] :
    IsJ0Ring R := by
  -- Choose a regular principal localization upstairs from the `J-0` hypothesis on `S`.
  obtain ⟨g, hg, hSg_reg⟩ := exists_nonzero_isRegularRing_localizationAway_of_isJ0Ring S
  let Sg := Localization.Away g
  have hgPowers := powers_le_nonZeroDivisors_of_noZeroDivisors hg
  letI : IsRegularRing Sg := hSg_reg
  letI : IsNoetherianRing Sg := IsRegularRing.toIsNoetherian
  letI : IsDomain Sg := isDomain_of_le_nonZeroDivisors Sg hgPowers
  letI : Algebra.FiniteType R Sg :=
    Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType R S)
      (inferInstance : Algebra.FiniteType S Sg)
  have hinjSg : Function.Injective (algebraMap R Sg) := by
    -- Injectivity survives after localizing at a nonzerodivisor in the domain target.
    intro x y hxy
    exact hinj <| (IsLocalization.injective Sg hgPowers) <| by
      change algebraMap S Sg (algebraMap R S x) = algebraMap S Sg (algebraMap R S y)
      exact hxy
  obtain ⟨f, hf, hcond⟩ :
      ∃ f : R, f ≠ 0 ∧ LocalizationCondition R Sg Sg f :=
    exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType
  let Rf := Localization.Away f
  letI : LocalizationCondition R Sg Sg f := hcond
  have hfSg : algebraMap R Sg f ≠ 0 := by
    -- The chosen localization parameter stays nonzero after mapping into `S_g`.
    intro h0
    apply hf
    exact hinjSg <| by
      rw [map_zero]
      exact h0
  let Sgf := Localization.Away (algebraMap R Sg f)
  letI : Module.Free Rf Sgf := hcond.free_algebra
  have hfSgPowers := powers_le_nonZeroDivisors_of_noZeroDivisors hfSg
  letI : IsDomain Sgf := isDomain_of_le_nonZeroDivisors Sgf hfSgPowers
  have hRf_reg : IsRegularRing Rf := by
    -- Faithfully flat descent carries regularity from the iterated localization of `S`.
    letI : IsRegularRing Sgf :=
      (isRegularRing_localizationAway_iff_basicOpen_subset_regularLocus (algebraMap R Sg f)).2
        fun p _hp ↦ by
          simpa using IsRegularRing.isRegularLocalRing_atPrime p
    have hff : Module.FaithfullyFlat Rf Sgf := by infer_instance
    exact isRegularRing_of_faithfullyFlat
      (algebraMap Rf Sgf)
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)
  have hbasic_subset :
      (basicOpen f : Set (PrimeSpectrum R)) ⊆ Reg(Spec R) :=
    (isRegularRing_localizationAway_iff_basicOpen_subset_regularLocus f).1 hRf_reg
  have hbasic_nonempty : (basicOpen f : Set (PrimeSpectrum R)).Nonempty := by
    -- In a domain, the generic point belongs to every nonzero basic open subset.
    refine ⟨⟨⊥, inferInstance⟩, ?_⟩
    simpa using (mem_basicOpen f ⟨⊥, inferInstance⟩).2 hf
  exact (isJ0Ring_iff_exists_nonempty_open_subset_regularLocus).2
    ⟨basicOpen f, isOpen_basicOpen, hbasic_nonempty, hbasic_subset⟩

/-- Helper for Definition 15.47.1: a finite type domain over a field is `J-0` once its
fraction-field extension is separable in the Stacks sense. -/
private theorem isJ0Ring_of_field_domain_separableFrac_local
    {B : Type v} [CommRing B] [Algebra K B] [IsDomain B] [Algebra.FiniteType K B]
    (hinj : Function.Injective (algebraMap K B))
    (hsep : Algebra.fractionRingIsSeparableOver (R := K) (S := B) hinj) :
    IsJ0Ring B := by
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  letI : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  -- Rewrite separability of the fraction field extension as smoothness at the generic point.
  have hB0 : Algebra.IsSmoothAt K (⊥ : Ideal B) :=
    (Algebra.isSmoothAt_zero_iff_isSeparableOver_fractionRing hinj).2 hsep
  -- Shrink to a principal neighborhood on which the algebra is smooth over the field.
  obtain ⟨g, hg, hBg_smooth⟩ :=
    (Algebra.smoothAtPrime_iff_isSmoothAt K B (⊥ : PrimeSpectrum B)).2 hB0
  have hg0 : g ≠ 0 := by
    intro hg0
    exact hg (hg0 ▸ Ideal.zero_mem _)
  let Bg := Localization.Away g
  have hgPowers := powers_le_nonZeroDivisors_of_noZeroDivisors hg0
  letI : IsDomain Bg := isDomain_of_le_nonZeroDivisors Bg hgPowers
  letI : Algebra.Smooth K Bg := hBg_smooth
  -- Over a regular base field, smoothness makes the localized ring regular, hence `J-0`.
  letI : IsRegularRing Bg := isRegularRing_of_smooth (R := K) (S := Bg)
  letI : IsJ0Ring Bg := isJ0Ring_of_isRegularRing Bg
  -- Descend the `J-0` witness from the regular localization `B_g` back to `B`.
  exact
    isJ0Ring_of_injective_finiteType_domain_local
      (R := B) (S := Bg) (IsLocalization.injective Bg hgPowers)

/-- Helper for Definition 15.47.1: after lifting the fraction field, the tensor-image model is a
domain that is finite type over both `A` and the lifted base field `k'`, together with an
injective map into `L'`. -/
private theorem tensor_image_model_over_base_local
    {A : Type v} [CommRing A] [Algebra K A] [IsDomain A] [Algebra.FiniteType K A]
    {k' : Type v} [Field k'] [Algebra K k'] [FiniteDimensional K k']
    {L' : Type v} [Field L'] [Algebra K L'] [Algebra (FractionRing A) L']
    [Algebra k' L'] [IsScalarTower K (FractionRing A) L'] [IsScalarTower K k' L'] :
    ∃ (B : Type v) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B) (_ : Algebra k' B)
      (_ : Algebra.FiniteType A B) (_ : Algebra.FiniteType k' B) (j : B →ₐ[k'] L'),
        Function.Injective (algebraMap A B) ∧ Function.Injective j := by
  -- TODO: package the range of the tensor-product map
  -- `k' ⊗[K] A →ₐ[k'] L'` as a ring `B`, give it both `A`- and `k'`-algebra structures, prove
  -- finite-type over both bases via surjectivity of the range-restriction map, and identify the
  -- composite `A → B → L'` with the original injective map `A → L'`.
  sorry

/-- Helper for Definition 15.47.1: an injective `k'`-algebra map from the tensor-image model into
`L'` makes the model's fraction field separable over `k'`, hence satisfies the Stacks-project
fraction-field predicate. -/
private theorem fractionRingIsSeparableOver_of_tensor_image_embedding_local
    {k' : Type u} [Field k'] {B : Type v} [CommRing B] [IsDomain B] [Algebra k' B]
    {L' : Type v} [Field L'] [Algebra k' L']
    (hinjB : Function.Injective (algebraMap k' B))
    (j : B →ₐ[k'] L') (hj : Function.Injective j)
    (hsep : Algebra.IsSeparableOver k' L') :
    Algebra.fractionRingIsSeparableOver (R := k') (S := B) hinjB := by
  letI : Algebra B L' := j.toRingHom.toAlgebra
  letI : IsScalarTower k' B L' := IsScalarTower.of_algebraMap_eq' <| by
    ext x
    exact (j.commutes x).symm
  -- TODO: extend `j` to `FractionRing B →ₐ[k'] L'`, pass `hsep` to its field range by
  -- `Algebra.IsSeparableOver.of_intermediateField`, transport back with
  -- `AlgEquiv.ofInjectiveField`, and finally identify the resulting `k'`-separability statement
  -- with the exact wrapper `Algebra.fractionRingIsSeparableOver` for the field base `k'`.
  let _ := hinjB
  let _ := hj
  let _ := hsep
  sorry

/-- Helper for Definition 15.47.1: once every prime quotient is `J-0`, the regular locus is
open. -/
private theorem isJ1Ring_of_primeQuotients_isJ0_local
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hquot : ∀ p : PrimeSpectrum R, IsJ0Ring (R ⧸ p.asIdeal)) :
    IsJ1Ring R := by
  -- TODO: apply the Noetherian irreducible-closed openness criterion to `Reg(Spec R)`, transport
  -- a nonempty regular open from `Spec (R ⧸ p)` across `Spec (R ⧸ p) ≃ V(p)`, and then use the
  -- regular-local quotient/regular-sequence bridge along `V(p)` to upgrade regularity upstairs.
  sorry

/-- Helper for Definition 15.47.1: a finite type domain over a field is `J-0`. -/
private theorem finiteType_domain_over_field_isJ0_local
    {A : Type v} [CommRing A] [Algebra K A] [IsDomain A] [Algebra.FiniteType K A] :
    IsJ0Ring A := by
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  -- First build the purely inseparable lift promised by Lemma `10.45.3`.
  obtain ⟨k', _, _, L', _, _, _, _, _, _, _, _, _, _, hsep⟩ :=
    exists_purelyInseparable_lift_with_separable_over
      (k := K) (K := FractionRing A)
  -- Then package the image of the lifted tensor map as an injective finite type `A`-algebra.
  obtain ⟨B, _, _, _, _, _, _, j, hABinj, hj⟩ :=
    tensor_image_model_over_base_local
      (K := K) (A := A) (k' := k') (L' := L')
  have hkB_inj : Function.Injective (algebraMap k' B) := by
    intro x y hxy
    have hxy' : j (algebraMap k' B x) = j (algebraMap k' B y) := congrArg j hxy
    simpa using hxy'
  have hsepB :
      Algebra.fractionRingIsSeparableOver (R := k') (S := B) hkB_inj :=
    fractionRingIsSeparableOver_of_tensor_image_embedding_local
      (hinjB := hkB_inj) j hj hsep
  letI : IsJ0Ring B :=
    isJ0Ring_of_field_domain_separableFrac_local
      (K := k') (B := B) hkB_inj hsepB
  -- Descend the `J-0` witness from the tensor-image model back to the original domain `A`.
  exact isJ0Ring_of_injective_finiteType_domain_local
    (R := A) (S := B) hABinj

/-- Helper for Definition 15.47.1: a finite type algebra over a field is `J-1`. -/
theorem finiteType_algebra_isJ1_of_field {A : Type v} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] : IsJ1Ring A := by
  -- Route correction: the previous perfect-closure plan is not just incomplete; its key bridge is
  -- false for purely inseparable field extensions. If `A / K` is a finite purely inseparable
  -- field extension, then `Reg(Spec A) = Set.univ` but `K^{perf} ⊗[K] A` can be nonreduced, so
  -- its smooth locus over `K^{perf}` need not match the pullback of the downstairs regular locus.
  -- The source-faithful closure is now reduced to the two isolated bridge lemmas above.
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  refine isJ1Ring_of_primeQuotients_isJ0_local ?_
  intro p
  -- Each prime quotient is again a finite type `K`-algebra domain, so the domain case applies.
  letI : Algebra K (A ⧸ p.asIdeal) := by infer_instance
  letI : Algebra.FiniteType K (A ⧸ p.asIdeal) := by infer_instance
  letI : IsDomain (A ⧸ p.asIdeal) := Ideal.Quotient.isDomain p.asIdeal
  exact finiteType_domain_over_field_isJ0_local (K := K) (A := A ⧸ p.asIdeal)

/-- Helper for Definition 15.47.1: a primewise equivalence identifies the pullback of the regular
locus with the smooth locus after tensor base change along a field extension. -/
theorem regularLocus_preimage_eq_smoothLocus_of_pointwise_iff
    {k : Type u} {K' : Type v} {A : Type v} [Field k] [Field K'] [CommRing A]
    [Algebra k K'] [Algebra k A]
    (hpoint :
      ∀ qK : PrimeSpectrum (K' ⊗[k] A),
        let q :=
          PrimeSpectrum.comap
            ((Algebra.TensorProduct.includeRight : A →ₐ[k] K' ⊗[k] A).toRingHom) qK
        IsRegularLocalRing (Localization.AtPrime q.asIdeal) ↔
          Algebra.IsSmoothAt K' qK.asIdeal) :
    PrimeSpectrum.comap
        ((Algebra.TensorProduct.includeRight : A →ₐ[k] K' ⊗[k] A).toRingHom) ⁻¹'
          Reg(Spec A) =
      Algebra.smoothLocus K' (K' ⊗[k] A) := by
  -- The locus equality is just the set-level reformulation of the pointwise regular/smooth bridge.
  ext qK
  let q :=
    PrimeSpectrum.comap
      ((Algebra.TensorProduct.includeRight : A →ₐ[k] K' ⊗[k] A).toRingHom) qK
  change IsRegularLocalRing (Localization.AtPrime q.asIdeal) ↔ Algebra.IsSmoothAt K' qK.asIdeal
  simpa [q] using hpoint qK

/-- Helper for Definition 15.47.1: once a tensor-base-change homeomorphism identifies the pullback
of the regular locus with an upstairs smooth locus, openness descends to the downstairs regular
locus. -/
theorem isJ1Ring_of_isHomeomorph_and_regularLocus_preimage_eq_smoothLocus
    {k : Type u} {K' : Type v} {A : Type v} [Field k] [Field K'] [CommRing A]
    [Algebra k K'] [Algebra k A] [Algebra.FiniteType k A]
    (hhomeo :
      IsHomeomorph
        (PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight : A →ₐ[k] K' ⊗[k] A).toRingHom)))
    (hpreimage :
      PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight : A →ₐ[k] K' ⊗[k] A).toRingHom) ⁻¹'
            Reg(Spec A) =
        Algebra.smoothLocus K' (K' ⊗[k] A)) :
    IsJ1Ring A := by
  let i : A →+* K' ⊗[k] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[k] K' ⊗[k] A).toRingHom
  let e : PrimeSpectrum (K' ⊗[k] A) ≃ₜ PrimeSpectrum A :=
    hhomeo.homeomorph (PrimeSpectrum.comap i)
  letI : IsNoetherianRing A :=
    Algebra.FiniteType.isNoetherianRing k A
  letI : Algebra.FiniteType K' (K' ⊗[k] A) :=
    Algebra.FiniteType.baseChange K'
  letI : Algebra.FinitePresentation K' (K' ⊗[k] A) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rw [isJ1Ring_iff_regularLocus_isOpen]
  -- The upstairs smooth locus is open, and the homeomorphism turns its pullback description into
  -- openness of the downstairs regular locus.
  have hsmoothOpen : IsOpen (Algebra.smoothLocus K' (K' ⊗[k] A)) :=
    Algebra.isOpen_smoothLocus
  have hiPreimageOpen : IsOpen ((PrimeSpectrum.comap i) ⁻¹' Reg(Spec A)) := by
    rw [hpreimage]
    exact hsmoothOpen
  have hpreimageOpen : IsOpen (e ⁻¹' Reg(Spec A)) := by
    change IsOpen ((PrimeSpectrum.comap i) ⁻¹' Reg(Spec A))
    exact hiPreimageOpen
  exact (e.isOpen_preimage).1 hpreimageOpen

-- Proof sketch: any finite type algebra over a field has open regular locus, so every such
-- algebra is `J-1`.
/-- A field is `J-2`. -/
instance : IsJ2Ring K := by
  -- Reduce the `J-2` claim to the `J-1` statement for an arbitrary finite type `K`-algebra.
  rw [isJ2Ring_iff_forall_finiteType_isJ1]
  intro A _ _ _
  exact finiteType_algebra_isJ1_of_field (K := K) (A := A)

end

end
