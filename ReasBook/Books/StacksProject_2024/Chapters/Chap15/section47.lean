import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_47_1 (from Chap15) -/
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

/-! ### Lemma_15_47_2 (from Chap15) -/
universe u

open PrimeSpectrum
open scoped PrimeSpectrum

section

variable {R : Type u} [CommRing R]

variable [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: the Zariski topology on `PrimeSpectrum R`, the regular locus, and the chapter
  owners `IsJ0Ring`/`IsJ1Ring`;
- sampled owner declarations:
  `PrimeSpectrum.regularLocus`,
  `PrimeSpectrum.regularLocus_stableUnderGeneralization`,
  `isJ1Ring_iff_regularLocus_isOpen`,
  `PrimeSpectrum.pointsEquivIrreducibleCloseds`,
  `isOpen_iff_forall_irreducibleCloseds_inter_empty_or_contains_nonempty_open`;
- owner abstraction: the main statement should stay source-facing on `PrimeSpectrum R`, with
  `IsJ1Ring R` as the canonical owner and `V(p)` expressed by `zeroLocus p.asIdeal`;
- primitive vs. derived: the primitive data here is the existence of a nonempty open trace on the
  closed subset `V(p)`. The quotient-spectrum reformulation `IsJ0Ring (R ⧸ p.asIdeal)` is a
  bridge/view statement and should not replace the source-facing theorem.

Source/core/bridge triage:
- `source-facing`: the criterion on regular primes `p` and the closed subsets `V(p)`;
- `core/canonical`: `PrimeSpectrum.regularLocus`, `IsJ1Ring`, and the Noetherian openness
  criterion on irreducible closed subsets;
- `bridge/view`: `pointsEquivIrreducibleCloseds` identifies irreducible closed subsets with
  `zeroLocus p.asIdeal`, so the file should reuse that bridge instead of introducing a parallel
  wrapper around irreducible closed subsets.
-/

namespace PrimeSpectrum

-- Proof sketch: apply the Noetherian irreducible-closed openness criterion to `E`, identify each
-- irreducible closed subset of `Spec R` with `V(p)` via `PrimeSpectrum.pointsEquivIrreducibleCloseds`,
-- use the given hypothesis when `p ∈ E`, and use stability under generalization to obtain the
-- empty alternative when `p ∉ E`.
/-- For a subset `E` of `Spec R` that is stable under generalization, openness of `E` is
equivalent to the requirement that every point `p ∈ E` has a nonempty open trace on its closure
`V(p)` contained in `E`. -/
theorem isOpen_iff_forall_mem_zeroLocus_contains_nonempty_open_subset
    (E : Set (PrimeSpectrum R)) (hE_gen : StableUnderGeneralization E) :
    IsOpen E ↔
      ∀ p ∈ E,
        ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ (U ∩ zeroLocus p.asIdeal).Nonempty ∧
          U ∩ zeroLocus p.asIdeal ⊆ E := by
  constructor
  · intro hE p hp
    refine ⟨E, hE, ?_, Set.inter_subset_left⟩
    exact ⟨p, hp, by simpa [mem_zeroLocus]⟩
  · intro h
    exact
      (isOpen_iff_forall_irreducibleCloseds_inter_empty_or_contains_nonempty_open E).2
        fun Y ↦ by
          let p := (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm Y
          have hY : (Y : Set (PrimeSpectrum R)) = zeroLocus p.asIdeal := by
            calc
              (Y : Set (PrimeSpectrum R)) =
                  ((show TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) from
                    PrimeSpectrum.pointsEquivIrreducibleCloseds R p :
                    TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R)) :
                    Set (PrimeSpectrum R)) := by
                      simpa [p] using
                        congrArg
                          (fun Z : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) ↦
                            (Z : Set (PrimeSpectrum R)))
                          ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).apply_symm_apply Y).symm
              _ = zeroLocus p.asIdeal := by
                change closure ({p} : Set (PrimeSpectrum R)) = zeroLocus p.asIdeal
                simpa using closure_singleton p
          by_cases hp : p ∈ E
          · rcases h p hp with ⟨U, hU_open, hU_nonempty, hU_subset⟩
            right
            refine ⟨⟨Subtype.val ⁻¹' U, hU_open.preimage continuous_subtype_val⟩, ?_, ?_⟩
            · rcases hU_nonempty with ⟨x, hx⟩
              refine ⟨⟨x, ?_⟩, hx.1⟩
              change x ∈ (Y : Set (PrimeSpectrum R))
              rw [hY]
              exact hx.2
            · intro x hx
              have hxY : (x : PrimeSpectrum R) ∈ zeroLocus p.asIdeal := by
                rw [← hY]
                exact x.2
              exact hU_subset ⟨hx, hxY⟩
          · left
            ext x
            constructor
            · intro hx
              have hp_specializes_x : p ⤳ (x : PrimeSpectrum R) := by
                rw [← le_iff_specializes]
                simpa [hY, mem_zeroLocus] using x.2
              exact (hp <| hE_gen hp_specializes_x (by simpa using hx)).elim
            · intro hx
              simpa using hx

end PrimeSpectrum

-- Proof sketch: if the regular locus is open, take `U = Reg(Spec R)`. Conversely, apply the
-- Noetherian irreducible-closed openness criterion to `Reg(Spec R)`, identify each irreducible
-- closed subset of `Spec R` with `V(p)` via `PrimeSpectrum.pointsEquivIrreducibleCloseds`, use the
-- given hypothesis when `p` is regular, and use stability of the regular locus under
-- generalization to obtain the empty alternative when `p` is not regular.
/-- Lemma 15.47.2: for a Noetherian ring `R`, the ring is `J-1` if and only if for every regular
prime `p` of `Spec(R)`, the intersection `V(p) ∩ Reg(Spec(R))` contains a nonempty open subset of
`V(p)`, written as `U ∩ V(p)` for some open subset `U ⊆ Spec(R)`. -/
theorem isJ1Ring_iff_forall_regularPoint_zeroLocus_contains_nonempty_open_regular_subset :
    IsJ1Ring R ↔
      ∀ p ∈ Reg(Spec R),
        ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ (U ∩ zeroLocus p.asIdeal).Nonempty ∧
          U ∩ zeroLocus p.asIdeal ⊆ Reg(Spec R) := by
  rw [isJ1Ring_iff_regularLocus_isOpen]
  exact
    isOpen_iff_forall_mem_zeroLocus_contains_nonempty_open_subset
      (Reg(Spec R)) (regularLocus_stableUnderGeneralization R)

end

/-! ### Lemma_15_47_3 (from Chap15) -/
universe u

open PrimeSpectrum
open scoped PrimeSpectrum

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: the regular locus on `PrimeSpectrum R` and the chapter owners `IsJ0Ring` and
  `IsJ1Ring`;
- sampled owner declarations of the same kind:
  `PrimeSpectrum.regularLocus`,
  `isJ0Ring_iff_exists_nonempty_open_subset_regularLocus`,
  `isJ1Ring_iff_forall_regularPoint_zeroLocus_contains_nonempty_open_regular_subset`,
  `Ideal.primeSpectrum_quotient_homeomorph_zeroLocus`;
- best owner abstraction: the source-facing criterion from Lemma `15.47.2` is the canonical owner
  bridge for proving `IsJ1Ring R`, while the hypotheses `IsJ0Ring (R ⧸ p.asIdeal)` are derived
  input on the quotient spectra `Spec (R ⧸ p) ≃ V(p)`;
- primitive vs. derived: the primitive public data are just the ring `R` and the owner hypothesis
  that each prime quotient is `J-0`. The required open subsets of `V(p)` are derived via the
  quotient-spectrum owner bridge, so they should not be packaged as a separate local wrapper API.

Source/core/bridge triage:
- `source-facing`: the chapter lemma asserting that `J-0` prime quotients force `R` to be `J-1`;
- `core/canonical`: `Reg(Spec R)`, `IsJ0Ring`, and `IsJ1Ring`;
- `bridge/view`: the homeomorphism `Spec (R ⧸ p) ≃ V(p)` transporting the quotient regular locus
  back to the closed subset `V(p)`.
-/

-- Proof sketch: apply the criterion of Lemma `15.47.2`. For a regular prime `p`, choose a
-- regular sequence generating `p` after localizing and then after shrinking to a principal open.
-- For any prime `q ⊇ p` whose image in `Spec (R ⧸ p)` is regular, the quotient local ring
-- `R_q / p R_q` is regular; the regular-sequence criterion for regular local rings then implies
-- that `R_q` is regular. Since `R ⧸ p` is `J-0`, this yields the required nonempty open subset of
-- `V(p)` contained in the regular locus, so Lemma `15.47.2` gives that `R` is `J-1`.
/-- Lemma 15.47.3: if `R` is a Noetherian ring and for every prime `p` of `R` the quotient
ring `R ⧸ p` is `J-0`, then `R` is `J-1`. -/
theorem isJ1Ring_of_isJ0Ring_quotient_by_prime
    (hquot : ∀ p : PrimeSpectrum R, IsJ0Ring (R ⧸ p.asIdeal)) :
    IsJ1Ring R := by
  rw [isJ1Ring_iff_forall_regularPoint_zeroLocus_contains_nonempty_open_regular_subset]
  intro p hp
  obtain ⟨V, hV_open, hV_nonempty, hV_reg⟩ :=
    (isJ0Ring_iff_exists_nonempty_open_subset_regularLocus).mp (hquot p)
  let e := Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p.asIdeal
  have hV_reg_zeroLocus :
      ∀ x ∈ V, IsRegularLocalRing (Localization.AtPrime x.asIdeal) := by
    intro x hx
    simpa using hV_reg hx
  -- Transport the nonempty open subset `V ⊆ Reg(Spec (R ⧸ p.asIdeal))` across the canonical
  -- quotient-spectrum homeomorphism `e : Spec (R ⧸ p) ≃ V(p)`, then use the regular-sequence
  -- argument from the proof sketch to upgrade regularity from the quotient local rings to the
  -- ambient local rings along `V(p)`.
  sorry

end

/-! ### Lemma_15_47_4 (from Chap15) -/
namespace Algebra

universe u v

open GenericFlatness IsLocalization
open PrimeSpectrum
open scoped PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsDomain R] [IsDomain S] [Algebra.FiniteType R S]

/- Domain-style sampling:
* primary domain: `J-0` descent for finite type maps of domains, organized around the regular locus
  on `Spec`;
* sampled owner and bridge declarations of the same kind:
  `IsJ0Ring`,
  `isJ0Ring_iff_exists_nonempty_open_subset_regularLocus`,
  `exists_nonzero_isRegularRing_localizationAway_of_isJ0Ring`,
  `isRegularRing_of_faithfullyFlat`;
* best owner abstraction: the public statement should stay on the chapter owner `IsJ0Ring`;
  the nonzero principal-localization witness is reused from owner-derived API in
  `Definition_15_47_1`, and regularity descent remains derived bridge data inside the proof;
* primitive vs. derived: the primitive public data are the injective finite type domain map
  `R → S` and the owner hypothesis that `S` is `J-0`. A witness `f ≠ 0` with
  `Localization.Away f` regular belongs to the domain-localization bridge and should not appear as
  parallel public data.

Source/core/bridge triage:
* source-facing: the descent statement for `IsJ0Ring` along an injective finite type map of
  domains;
* core/canonical: the owner `IsJ0Ring`;
* bridge/view: principal localizations `Localization.Away f` and faithful-flat descent of
  `IsRegularRing`.
-/

-- Proof sketch: choose `g : S` with `S[1 / g]` regular from the `J-0` hypothesis on `S`, and
-- replace `S` by this localization. Generic flatness then gives a nonzero `f : R` such that the
-- induced map `R[1 / f] → S[1 / f]` is faithfully flat. Apply faithful-flat descent of regularity
-- to conclude that `R[1 / f]` is regular.
/-- Lemma 15.47.4: for an injective finite type map `R → S` from a Noetherian domain to a domain,
if `S` is `J-0`, then `R` is `J-0`. -/
theorem isJ0Ring_of_injective_finiteType
    (hinj : Function.Injective (algebraMap R S)) [IsJ0Ring S] :
    IsJ0Ring R := by
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
    refine ⟨⟨⊥, inferInstance⟩, ?_⟩
    simpa using (mem_basicOpen f ⟨⊥, inferInstance⟩).2 hf
  exact (isJ0Ring_iff_exists_nonempty_open_subset_regularLocus).2
    ⟨basicOpen f, isOpen_basicOpen, hbasic_nonempty, hbasic_subset⟩

end

end Algebra

/-! ### Lemma_15_47_5 (from Chap15) -/
namespace Algebra

universe u v

open Localization IsLocalization

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain R] [IsDomain S] [Algebra.FiniteType R S] [IsJ0Ring R]

/- Source/core/bridge triage:
* source-facing: ascent of the `J-0` condition along an injective finite type map of domains with
  separable fraction-field extension;
* core/canonical: the chapter owner `IsJ0Ring`;
* bridge/view: in the domain case, a nonempty regular open can be represented by a nonzero
  principal localization that is regular, and the induced fraction-field extension of an
  injective domain map is measured by the canonical owner predicate
  `fractionRingIsSeparableOver hinj`.

The primitive data are the `J-0` owner and the separability condition on fraction fields. The
principal-localization witness is derived chapter API via
`exists_nonzero_isRegularRing_localizationAway_of_isJ0Ring`, so this file should state the main
result using `IsJ0Ring` rather than a parallel existential interface.
-/

-- Proof sketch: choose a nonzero `f : R` with `R[1 / f]` regular from the `J-0` hypothesis on
-- `R`. By Lemma `10.140.9`, the generic point `(0) ∈ Spec S` is `IsSmoothAt` over `R`, and the
-- bridge `smoothAtPrime_iff_isSmoothAt` then yields a principal localization `S[1 / g]` with
-- `g ≠ 0` that is smooth over `R`. Localizing once more away from the image of `f` gives a
-- smooth `R[1 / f]`-algebra, so Lemma `10.163.10` makes that iterated localization regular.
-- Regular rings are `J-0`, and Lemma `15.47.4` then descends `J-0` twice: first from the iterated
-- localization to `S[1 / g]`, then from `S[1 / g]` to `S`.
/-- Lemma 15.47.5: for an injective finite type ring map `R → S` from a Noetherian domain to a
domain, if `R` is `J-0` and the induced extension of fraction fields `FractionRing S /
FractionRing R` is separable in the Stacks Project sense, then `S` is `J-0`. -/
theorem isJ0Ring_of_injective_finiteType_of_separable_fractionRingExtension
    (hinj : Function.Injective (algebraMap R S))
    (hsep : fractionRingIsSeparableOver hinj) :
    IsJ0Ring S := by
  let hR : IsJ0Ring R := inferInstance
  obtain ⟨f, hf, hRf_reg⟩ := exists_nonzero_isRegularRing_localizationAway_of_isJ0Ring R
  let Rf := Localization.Away f
  letI : IsNoetherianRing R := hR.toIsNoetherian
  letI : IsRegularRing Rf := hRf_reg
  letI : FinitePresentation R S := FinitePresentation.of_finiteType.mp inferInstance
  have hS0 : IsSmoothAt R (⊥ : Ideal S) :=
    (isSmoothAt_zero_iff_isSeparableOver_fractionRing hinj).2 hsep
  obtain ⟨g, hg, hSg_smooth⟩ :=
    (smoothAtPrime_iff_isSmoothAt R S (⊥ : PrimeSpectrum S)).2 hS0
  have hg0 : g ≠ 0 := by
    intro h0
    exact hg (h0 ▸ Ideal.zero_mem _)
  let Sg := Localization.Away g
  letI : Smooth R Sg := hSg_smooth
  have hgPowers := powers_le_nonZeroDivisors_of_noZeroDivisors hg0
  letI : IsDomain Sg := isDomain_of_le_nonZeroDivisors Sg hgPowers
  have hinjSg : Function.Injective (algebraMap S Sg) := IsLocalization.injective Sg hgPowers
  have hinjRSg : Function.Injective (algebraMap R Sg) := by
    simpa [IsScalarTower.algebraMap_eq R S Sg] using hinjSg.comp hinj
  have hfSg : algebraMap R Sg f ≠ 0 := (map_ne_zero_iff (algebraMap R Sg) hinjRSg).2 hf
  let Sgf := Localization.Away (algebraMap R Sg f)
  have hfSgPowers := powers_le_nonZeroDivisors_of_noZeroDivisors hfSg
  letI : IsDomain Sgf := isDomain_of_le_nonZeroDivisors Sgf hfSgPowers
  have hfSgf_unit : IsUnit (algebraMap R Sgf f) := by
    change IsUnit (algebraMap Sg Sgf (algebraMap R Sg f))
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R Sg f)
  letI : Algebra Rf Sgf := (Localization.awayLift (algebraMap R Sgf) f hfSgf_unit).toAlgebra
  have hRfSgf : RingHom.Smooth (Localization.awayLift (algebraMap R Sgf) f hfSgf_unit) :=
    by
      letI : Smooth R Sgf := smooth_localization_away_target R Sg (algebraMap R Sg f)
      exact smooth_away_lift_of_isUnit R Sgf f hfSgf_unit
  letI : Smooth Rf Sgf := hRfSgf.toAlgebra
  have hSgf_reg : IsRegularRing Sgf := by
    letI : IsNoetherianRing Sgf := Algebra.FiniteType.isNoetherianRing Rf Sgf
    let _ : RingHom.IsRegularRingMap (algebraMap Rf Sgf) := by
      exact
        { toFlat := RingHom.flat_algebraMap_iff.mpr inferInstance
          isGeometricallyRegular_fiber := fun p ↦ by
            letI : Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber Sgf) := inferInstance
            letI :
                Algebra.IsGeometricallyRegular p.asIdeal.ResidueField p.asIdeal.ResidueField :=
              inferInstance
            infer_instance }
    exact Algebra.isRegularRing_of_regularRingMap Rf
  letI : IsRegularRing Sgf := hSgf_reg
  letI : IsJ0Ring Sgf := isJ0Ring_of_isRegularRing Sgf
  have hinjSgf : Function.Injective (algebraMap Sg Sgf) := IsLocalization.injective Sgf hfSgPowers
  letI : IsNoetherianRing Sg := Algebra.FiniteType.isNoetherianRing R Sg
  letI : IsJ0Ring Sg := isJ0Ring_of_injective_finiteType hinjSgf
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  exact isJ0Ring_of_injective_finiteType hinjSg

end

end Algebra

/-! ### Lemma_15_47_6 (from Chap15) -/
universe u v

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: the chapter's `J-0`/`J-1`/`J-2` hierarchy for Noetherian rings and its
  fraction-field / residue-field bridge criteria;
- sampled owner declarations of the same kind:
  `IsJ0Ring`,
  `IsJ1Ring`,
  `IsJ2Ring`,
  `isJ2Ring_iff_forall_finiteType_isJ1`;
- best owner abstraction: this file is `source-facing`, but its public API should still be
  organized around the existing owners `IsJ0Ring`, `IsJ1Ring`, and `IsJ2Ring` from
  `Definition_15_47_1`, while the residue-field clause should use the canonical prime-ideal owner
  `p : Ideal R` with `[p.IsPrime]` and `p.ResidueField` rather than a `PrimeSpectrum` wrapper;
- primitive vs. derived: the primitive data in conditions `(2)` and `(3)` are the finite type /
  finite `R`-algebra structures together with the domain hypothesis in `(2)`. Noetherianity of
  those target rings is derived from the owner conclusions `IsJ0Ring A` and `IsJ1Ring A`, so it
  should not remain primitive public data in this `TFAE` statement. Likewise, the prime-spectrum
  presentation of condition `(4)` is derived from the prime ideal and should not stay as the
  algebra-facing owner surface. The `R`-algebra structure on a residue-field extension
  `L / p.ResidueField` is derived internal data coming from `R → p.ResidueField → L`, so it should
  not be exposed as a primitive binder in the public clause. For the witness algebra in `(4)`,
  the source-faithful primitive witness data are that `A` is a finite `R`-algebra domain with
  `IsFractionRing A L` and `IsJ0Ring A`; the domain hypothesis is not derivable from
  `IsFractionRing A L` in mathlib, so it must remain explicit in the public clause.
-/

-- Proof sketch: `(1) → (2)` and `(1) → (3)` follow by applying the defining `J-2` property to
-- finite type and finite `R`-algebras, with the domain case giving `J-0` because a domain that is
-- `J-1` is `J-0`. For `(2) → (1)`, apply Lemma `15.47.3` to each prime quotient of a finite type
-- `R`-algebra. The implication `(3) → (4)` is obtained by applying `(3)` to the finite
-- `R`-algebra whose fraction field is the given purely inseparable residue-field extension, while
-- `(4) → (2)` follows by replacing the fraction field of a finite type domain algebra by a finite
-- purely inseparable/separable tower as in Lemma `10.42.4`, choosing a `J-0` model over the
-- residue field, and descending `J-0` back along Lemmas `15.47.5` and `15.47.4`.
/-- Lemma 15.47.6: for a Noetherian ring `R`, the following are equivalent: `R` is `J-2`; every
finite type `R`-algebra that is a domain is `J-0`; every finite `R`-algebra is `J-1`; and for
every prime `p` and every finite purely inseparable extension `L / κ(p)`, there exists a finite
`R`-algebra domain that is `J-0` and has fraction field `L`. -/
theorem isJ2Ring_tfae_finiteType_domain_isJ0_finite_algebra_isJ1_purelyInseparable_residueField_extension
    : List.TFAE
        [ IsJ2Ring R,
          ∀ (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [IsDomain A],
            IsJ0Ring A,
          ∀ (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A],
            IsJ1Ring A,
          ∀ (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
            [FiniteDimensional p.ResidueField L] [IsPurelyInseparable p.ResidueField L],
            let _ : Algebra R L :=
              RingHom.toAlgebra
                ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField))
            let _ : IsScalarTower R p.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
            ∃ (A : Type v) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
              (_ : IsDomain A) (_ : Algebra A L) (_ : IsScalarTower R A L)
              (_ : IsFractionRing A L),
              IsJ0Ring A
        ] := sorry

end
