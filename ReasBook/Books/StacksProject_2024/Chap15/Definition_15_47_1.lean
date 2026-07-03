import Mathlib
import StacksProject_2024.Chap10.Definition_10_110_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum
open scoped PrimeSpectrum

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

-- Proof sketch: if `p ⤳ q`, then there is a canonical local map `R_p → R_q`. This map is flat,
-- local, and has regular target whenever `q` is in the regular locus, so Lemma `10.110.9`
-- descends regularity from `R_q` to `R_p`.
/-- The regular locus of `Spec R` is stable under generalization. -/
theorem regularLocus_stableUnderGeneralization (R : Type u) [CommRing R] :
    StableUnderGeneralization (Reg(Spec R)) := by
  intro p q hpq hq
  sorry

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
class IsJ1Ring (R : Type u) [CommRing R] : Prop extends IsNoetherianRing R where
  /-- The regular locus of `Spec R` is open. -/
  regularLocus_isOpen : IsOpen (Reg(Spec R))

/-- The `J-1` condition is exactly openness of the regular locus. -/
theorem isJ1Ring_iff_regularLocus_isOpen {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsJ1Ring R ↔ IsOpen (Reg(Spec R)) :=
  ⟨fun h ↦ h.regularLocus_isOpen, fun h ↦ { regularLocus_isOpen := h }⟩

/-- Definition 15.47.1 (3): a Noetherian ring is `J-2` if every finite type `R`-algebra is
`J-1`. -/
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
instance : IsJ0Ring K := sorry

-- Proof sketch: `Spec K` has a single point and its local ring is the field `K`, hence the
-- regular locus is all of `Spec K`, which is open.
/-- A field is `J-1`. -/
instance : IsJ1Ring K := sorry

-- Proof sketch: any finite type algebra over a field has open regular locus, so every such
-- algebra is `J-1`.
/-- A field is `J-2`. -/
instance : IsJ2Ring K := sorry

end

end
