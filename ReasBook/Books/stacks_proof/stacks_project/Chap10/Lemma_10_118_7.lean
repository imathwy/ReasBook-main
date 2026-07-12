import StacksProject_2024.Chap10.Lemma_10_118_3
import StacksProject_2024.Chap10.«10_118_3_2»
import StacksProject_2024.Chap10.Lemma_10_118_5
import StacksProject_2024.Chap10.Lemma_10_30_2
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.StacksAttribute

open scoped TensorProduct

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/-- Helper for Lemma 10.118.7: over a domain, the generic-flatness good locus contains a dense
basic open coming from the nonzero witness of Lemma `10.118.3`. -/
private theorem dense_goodLocus_of_isDomain
    [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] :
    Dense (goodLocus R S M) := by
  obtain ⟨f, hf, hcond⟩ :
      ∃ f : R, f ≠ 0 ∧ LocalizationCondition R S M f :=
    exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType
  have hsubset : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ goodLocus R S M := by
    -- The witness `f` contributes its basic open directly to the defining union of the good locus.
    intro p hp
    rw [goodLocus_eq_iUnion]
    exact Set.mem_iUnion.mpr ⟨⟨f, hcond⟩, hp⟩
  -- A nonzero basic open is dense over a domain, so the larger good locus is dense as well.
  exact Dense.mono hsubset (basicOpen_dense_of_nonzero_of_isDomain f hf)

/-- Helper for Lemma 10.118.7: localizing a finite-type `R`-algebra at a prime of `R` preserves
finite type over the localized base ring. -/
private theorem finiteType_localizationAtPrime
    [Algebra.FiniteType R S] (p : PrimeSpectrum R) :
    let Rp := Localization.AtPrime p.asIdeal
    let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    Algebra.FiniteType Rp Sp := by
  -- Identify the target localization with the tensor base change `R_𝔭 ⊗[R] S`.
  dsimp
  have hbase : Algebra.FiniteType (Localization.AtPrime p.asIdeal)
      ((Localization.AtPrime p.asIdeal) ⊗[R] S) :=
    Algebra.FiniteType.baseChange (R := R) (A := S)
      (B := Localization.AtPrime p.asIdeal)
  -- Transport finite generation across the canonical tensor-localization equivalence.
  exact Algebra.FiniteType.equiv hbase
    (Localization.tensorRightAlgEquiv p.asIdeal.primeCompl S)

/-- Helper for Lemma 10.118.7: if `𝔭` is minimal, then `Spec(R_𝔭) → Spec(R)` has image `{𝔭}`. -/
private theorem localizationAtPrime_comap_range_eq_singleton_of_mem_minimalPrimes
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R) :
    Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal))) =
      ({p} : Set (PrimeSpectrum R)) := by
  have hpmin : IsMin p := PrimeSpectrum.isMin_iff.mpr hp
  rw [PrimeSpectrum.localization_comap_range
    (S := Localization.AtPrime p.asIdeal) (M := p.asIdeal.primeCompl)]
  ext q
  constructor
  · intro hq
    have hleIdeal : q.asIdeal ≤ p.asIdeal := by
      intro r hrq
      by_contra hrp
      exact (Set.disjoint_left.mp hq) hrp hrq
    have hle : q ≤ p := (PrimeSpectrum.asIdeal_le_asIdeal q p).mp hleIdeal
    exact Set.mem_singleton_iff.mpr (le_antisymm hle (hpmin hle))
  · rintro rfl
    exact Set.disjoint_left.2 fun r hrp hrq ↦ hrp hrq

/-- Helper for Lemma 10.118.7: a subset of `Spec(R)` is dense once its closure contains every
minimal prime. -/
private theorem dense_of_minimalPrimes_mem_closure
    {U : Set (PrimeSpectrum R)}
    (hmin : ∀ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R → p ∈ closure U) :
    Dense U := by
  rw [dense_iff_closure_eq]
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le
      (J := x.asIdeal) (show (⊥ : Ideal R) ≤ x.asIdeal from bot_le)
    let q' : PrimeSpectrum R := ⟨q, Ideal.minimalPrimes_isPrime hq⟩
    have hq_mem : q' ∈ closure U := hmin q' hq
    have hq_le : q' ≤ x := (PrimeSpectrum.asIdeal_le_asIdeal q' x).mp hqx
    have hq_spec : q' ⤳ x := (PrimeSpectrum.le_iff_specializes q' x).mp hq_le
    -- A closed set containing every minimal prime contains all their specializations, hence every
    -- point of the spectrum.
    exact hq_spec.mem_closed isClosed_closure hq_mem

/-- Helper for Chap10 Lemma 10 118 7: finite presentation of the localized algebra at a unit
parameter descends back to the original algebra. -/
private theorem algebraFinitePresentation_of_localizationCondition_isUnit
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B] [Algebra A B]
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    {u : A} (h : LocalizationCondition A B N u) (hu : IsUnit u) :
    Algebra.FinitePresentation A B := by
  -- First view the target unit-localization as finitely presented over `A`, then transport it
  -- across the target-ring unit equivalence.
  let t : B := algebraMap A B u
  have ht : IsUnit t := hu.map (algebraMap A B)
  let eB := IsLocalization.atUnit B (Localization.Away t) t ht
  have hfpLocalizedTarget : Algebra.FinitePresentation A (Localization.Away t) := by
    letI : Algebra.FinitePresentation (Localization.Away u) (Localization.Away t) :=
      h.finitePresentation_algebra
    letI : IsScalarTower A (Localization.Away u) (Localization.Away t) :=
      IsScalarTower.of_algebraMap_eq fun a ↦ by
        symm
        simpa [t, Algebra.ofId_apply] using
          DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) u).comp_algebraMap a
    exact Algebra.FinitePresentation.trans A (Localization.Away u) (Localization.Away t)
  letI : Algebra.FinitePresentation A (Localization.Away t) := hfpLocalizedTarget
  exact Algebra.FinitePresentation.equiv (eB.symm.restrictScalars A)

/-- Helper for Chap10 Lemma 10 118 7: freeness of the localized algebra at a unit parameter
descends back to the original algebra. -/
private theorem algebraFree_of_localizationCondition_isUnit
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B] [Algebra A B]
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    {u : A} (h : LocalizationCondition A B N u) (hu : IsUnit u) :
    Module.Free A B := by
  -- Freeness descends by transitivity through the source unit-localization and then across the
  -- target unit-localization equivalence.
  let t : B := algebraMap A B u
  have ht : IsUnit t := hu.map (algebraMap A B)
  let eA := IsLocalization.atUnit A (Localization.Away u) u hu
  let eB := IsLocalization.atUnit B (Localization.Away t) t ht
  have hfreeSourceLocalization : Module.Free A (Localization.Away u) :=
    Module.Free.of_equiv' (inferInstance : Module.Free A A) eA.toLinearEquiv
  have hfreeTargetLocalization : Module.Free A (Localization.Away t) := by
    letI : Module.Free (Localization.Away u) (Localization.Away t) := h.free_algebra
    letI : Module.Free A (Localization.Away u) := hfreeSourceLocalization
    letI : IsScalarTower A (Localization.Away u) (Localization.Away t) :=
      IsScalarTower.of_algebraMap_eq fun a ↦ by
        symm
        simpa [t, Algebra.ofId_apply] using
          DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) u).comp_algebraMap a
    exact Module.Free.trans (R := A) (S := Localization.Away u) (M := Localization.Away t)
  exact Module.Free.of_equiv' hfreeTargetLocalization
    (eB.symm.restrictScalars A).toLinearEquiv

/-- Helper for Chap10 Lemma 10 118 7: finite presentation of the localized module at a unit
parameter descends back to the original target ring. -/
private theorem moduleFinitePresentation_of_localizationCondition_isUnit
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B] [Algebra A B]
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    {u : A} (h : LocalizationCondition A B N u) (hu : IsUnit u) :
    Module.FinitePresentation B N := by
  -- Collapse the target localization at the unit `algebraMap A B u`, then transport finite
  -- presentation first along the ring equivalence and then along the localized-module equivalence.
  let t : B := algebraMap A B u
  have ht : IsUnit t := hu.map (algebraMap A B)
  let eB := IsLocalization.atUnit B (Localization.Away t) t ht
  letI : IsLocalization.Away t B :=
    IsLocalization.away_of_isUnit_of_bijective B ht Function.bijective_id
  let idN : N →ₗ[B] N := LinearMap.id
  letI : IsLocalizedModule (.powers t) idN :=
    isLocalizedModule_id (.powers t) N B
  let eN : LocalizedModule.Away t N ≃ₗ[B] N :=
    IsLocalizedModule.linearEquiv (.powers t)
      (LocalizedModule.mkLinearMap (.powers t) N) idN
  have hfpLocalizedModule : Module.FinitePresentation B (LocalizedModule.Away t N) := by
    have hfpBase : Module.FinitePresentation B (Localization.Away t) :=
      Module.FinitePresentation.of_equiv eB.toLinearEquiv
    letI : Module.FinitePresentation B (Localization.Away t) := hfpBase
    letI : Module.FinitePresentation (Localization.Away t) (LocalizedModule.Away t N) :=
      h.finitePresentation_module
    exact Module.FinitePresentation.trans B (LocalizedModule.Away t N) (Localization.Away t)
  letI : Module.FinitePresentation B (LocalizedModule.Away t N) := hfpLocalizedModule
  exact Module.FinitePresentation.of_equiv eN

/-- Helper for Chap10 Lemma 10 118 7: freeness of the localized module at a unit parameter
descends back to the original base ring. -/
private theorem moduleFree_of_localizationCondition_isUnit
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B] [Algebra A B]
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    {u : A} (h : LocalizationCondition A B N u) (hu : IsUnit u) :
    Module.Free A N := by
  -- First make the localized module free over `A` by transitivity through the source
  -- unit-localization.  The existing `A`-action is the one induced from `A_u`.
  let t : B := algebraMap A B u
  have ht : IsUnit t := hu.map (algebraMap A B)
  letI : IsLocalization.Away t B :=
    IsLocalization.away_of_isUnit_of_bijective B ht Function.bijective_id
  let idN : N →ₗ[B] N := LinearMap.id
  letI : IsLocalizedModule (.powers t) idN :=
    isLocalizedModule_id (.powers t) N B
  let eN : LocalizedModule.Away t N ≃ₗ[B] N :=
    IsLocalizedModule.linearEquiv (.powers t)
      (LocalizedModule.mkLinearMap (.powers t) N) idN
  have hfreeSourceLocalization : Module.Free A (Localization.Away u) := by
    let eA := IsLocalization.atUnit A (Localization.Away u) u hu
    exact Module.Free.of_equiv' (inferInstance : Module.Free A A) eA.toLinearEquiv
  have hfreeLocalizedModule : Module.Free A (LocalizedModule.Away t N) := by
    letI : Module.Free (Localization.Away u) (LocalizedModule.Away t N) := h.free_module
    letI : Module.Free A (Localization.Away u) := hfreeSourceLocalization
    letI : IsScalarTower A (Localization.Away u) (LocalizedModule.Away t N) :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        -- The `A`-action obtained through `A_u` agrees with the canonical action through
        -- `B_{algebraMap u}` because the away map commutes with the original algebra map.
        change (algebraMap (Localization.Away u) (Localization.Away t)
            (algebraMap A (Localization.Away u) a)) • x = a • x
        rw [show algebraMap (Localization.Away u) (Localization.Away t)
            (algebraMap A (Localization.Away u) a) =
              algebraMap A (Localization.Away t) a by
          simpa [t, Algebra.ofId_apply] using
            DFunLike.congr_fun
              (Localization.awayMapₐ (Algebra.ofId A B) u).comp_algebraMap a]
        exact IsScalarTower.algebraMap_smul (Localization.Away t) a x
    exact Module.Free.trans (R := A) (S := Localization.Away u) (M := LocalizedModule.Away t N)
  -- The target localization is at a unit, so `LocalizedModule.Away t N` is linearly equivalent to
  -- `N`; restricting that equivalence to `A` transports the free basis back to `N`.
  exact Module.Free.of_equiv' hfreeLocalizedModule (eN.restrictScalars A)

/-- Helper for Chap10 Lemma 10 118 7: a `LocalizationCondition` at a unit parameter is equivalent
to the four direct finite-presentation and freeness fields over the unlocalized rings. -/
private theorem localizationCondition_fields_of_isUnit
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B] [Algebra A B]
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    {u : A} (h : LocalizationCondition A B N u) (hu : IsUnit u) :
    Algebra.FinitePresentation A B ∧
      Module.FinitePresentation B N ∧ Module.Free A B ∧ Module.Free A N := by
    -- Package the four fieldwise unit-normalization facts for the prime-local spreading step.
    exact
      ⟨algebraFinitePresentation_of_localizationCondition_isUnit h hu,
        moduleFinitePresentation_of_localizationCondition_isUnit h hu,
        algebraFree_of_localizationCondition_isUnit h hu,
        moduleFree_of_localizationCondition_isUnit h hu⟩

/-- Helper for Chap10 Lemma 10 118 7: direct finite-presentation and freeness data over `A`, `B`,
and `N` assemble into the generic-flatness localization condition after localizing at any element
of the base. -/
private theorem localizationCondition_of_fields
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B] [Algebra A B]
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (u : A) [Algebra.FinitePresentation A B] [Module.FinitePresentation B N]
    [Module.Free A B] [Module.Free A N] :
    LocalizationCondition A B N u := by
  let t : B := algebraMap A B u
  -- Finite-presentation fields are stable under the canonical away localization.
  have hfpAlg : Algebra.FinitePresentation (Localization.Away u) (Localization.Away t) := by
    simpa [t] using awayAlgebraFinitePresentationOverBase (A := A) (B := B) u
  have hfpModule :
      Module.FinitePresentation (Localization.Away t) (LocalizedModule.Away t N) := by
    simpa [t] using awayModuleFinitePresentation (A := B) (N := N) t
  have hfreeAlg : Module.Free (Localization.Away u) (Localization.Away t) := by
    letI : IsScalarTower A (Localization.Away u) (Localization.Away t) :=
      IsScalarTower.of_algebraMap_eq fun a ↦ by
        symm
        simpa [t, Algebra.ofId_apply] using
          DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) u).comp_algebraMap a
    -- View the target ring localization as an `A`-module localization of the free `A`-module `B`.
    let locB : B →ₗ[B] Localization.Away t := Algebra.linearMap B (Localization.Away t)
    let locA : B →ₗ[A] Localization.Away t := locB.restrictScalars A
    have hloc : IsLocalizedModule (Submonoid.powers u) locA := by
      exact isLocalizedModuleRestrictScalarsPowersAlgebraMap (A := A) (B := B) (N := B)
        (N' := Localization.Away t) u locB
    exact @Module.free_of_isLocalizedModule A B _ _ _ (Localization.Away u)
      (Localization.Away t) _ _ _ _ _ _ (Submonoid.powers u) locA inferInstance hloc
      inferInstance
  have hfreeModule : Module.Free (Localization.Away u) (LocalizedModule.Away t N) := by
    letI : IsScalarTower A (Localization.Away u) (LocalizedModule.Away t N) :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change (algebraMap (Localization.Away u) (Localization.Away t)
            (algebraMap A (Localization.Away u) a)) • x = a • x
        rw [show algebraMap (Localization.Away u) (Localization.Away t)
            (algebraMap A (Localization.Away u) a) =
              algebraMap A (Localization.Away t) a by
          simpa [t, Algebra.ofId_apply] using
            DFunLike.congr_fun
              (Localization.awayMapₐ (Algebra.ofId A B) u).comp_algebraMap a]
        exact IsScalarTower.algebraMap_smul (Localization.Away t) a x
    -- The localized module is likewise the `A`-localization of the free `A`-module `N`.
    let locB : N →ₗ[B] LocalizedModule.Away t N :=
      LocalizedModule.mkLinearMap (Submonoid.powers t) N
    let locA : N →ₗ[A] LocalizedModule.Away t N := locB.restrictScalars A
    have hloc : IsLocalizedModule (Submonoid.powers u) locA := by
      exact isLocalizedModuleRestrictScalarsPowersAlgebraMap (A := A) (B := B) (N := N)
        (N' := LocalizedModule.Away t N) u locB
    exact @Module.free_of_isLocalizedModule A N _ _ _ (Localization.Away u)
      (LocalizedModule.Away t N) _ _ _ _ _ _ (Submonoid.powers u) locA inferInstance hloc
      inferInstance
  exact
    { finitePresentation_algebra := hfpAlg
      finitePresentation_module := hfpModule
      free_algebra := hfreeAlg
      free_module := hfreeModule }

/-- Helper for Chap10 Lemma 10 118 7: a localization condition remains true after multiplying
the denominator by an arbitrary base-ring element. -/
private theorem localizationCondition_mul_left (f g : R) (hg : LocalizationCondition R S M g) :
    LocalizationCondition R S M (f * g) := by
  -- Localize the existing `g`-condition once more on the `f`-chart, then read the result as the
  -- direct condition for the product denominator.
  exact
    (localizationCondition_product_iff_iteratedAway (R := R) (S := S) (M := M) f g).mpr
      (localizationCondition_map_away (R := R) (S := S) (M := M) f g hg)

/-- Helper for Chap10 Lemma 10 118 7: a localization condition remains true after multiplying
the denominator on the right by an arbitrary base-ring element. -/
private theorem localizationCondition_mul_right (f g : R) (hf : LocalizationCondition R S M f) :
    LocalizationCondition R S M (f * g) := by
  -- Commute the product so the left-multiplication enlargement lemma applies directly.
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    localizationCondition_mul_left (R := R) (S := S) (M := M) g f hf

/-- Helper for Chap10 Lemma 10 118 7: an away-localized module carries the scalar tower from the
localized base through the localized target algebra. -/
private instance localizedAwayModuleTarget_isScalarTower
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B] [Algebra A B]
    {N : Type w} [AddCommGroup N] [Module B N] (u : A) :
    IsScalarTower (Localization.Away u) (Localization.Away (algebraMap A B u))
      (LocalizedModule.Away (algebraMap A B u) N) := by
  -- The module localization action is induced through the localized target algebra, so the tower
  -- condition is the ordinary associativity of scalar multiplication.
  refine ⟨?_⟩
  intro r s x
  change ((algebraMap (Localization.Away u)
      (Localization.Away (algebraMap A B u)) r) * s) • x =
    (algebraMap (Localization.Away u)
      (Localization.Away (algebraMap A B u)) r) • (s • x)
  simpa using
    (mul_smul
      (algebraMap (Localization.Away u) (Localization.Away (algebraMap A B u)) r)
      s x)

/-- Helper for Chap10 Lemma 10 118 7: a subsingleton module is finitely generated. -/
private theorem moduleFinite_of_subsingleton
    {A : Type*} [Semiring A] {N : Type*} [AddCommMonoid N] [Module A N]
    [Subsingleton N] :
    Module.Finite A N := by
  -- The singleton `{0}` spans a subsingleton module.
  refine ⟨⟨{0}, ?_⟩⟩
  ext x
  simp [Subsingleton.elim x 0]

/-- Helper for Chap10 Lemma 10 118 7: a subsingleton module is finitely presented. -/
private theorem moduleFinitePresentation_of_subsingleton
    {A : Type*} [Ring A] {N : Type*} [AddCommGroup N] [Module A N]
    [Subsingleton N] :
    Module.FinitePresentation A N := by
  -- Combine finite generation of a subsingleton module with its canonical free structure.
  letI : Module.Finite A N := moduleFinite_of_subsingleton (A := A) (N := N)
  letI : Module.Free A N := Module.Free.of_subsingleton A N
  exact Module.finitePresentation_of_projective A N

/-- Helper for Chap10 Lemma 10 118 7: the condition at the zero parameter is automatic because
all objects are localized at the zero submonoid. -/
private theorem localizationCondition_zero :
    LocalizationCondition R S M 0 := by
  have hA0 : Subsingleton (Localization.Away (0 : R)) := by
    exact IsLocalization.subsingleton
      (M := Submonoid.powers (0 : R)) (S := Localization.Away (0 : R))
      (Submonoid.mem_powers (0 : R))
  have hB0 : Subsingleton (Localization.Away (algebraMap R S 0)) := by
    exact IsLocalization.subsingleton
      (M := Submonoid.powers (algebraMap R S 0))
      (S := Localization.Away (algebraMap R S 0))
      (by simpa using Submonoid.mem_powers (algebraMap R S 0))
  have hN0 : Subsingleton (LocalizedModule.Away (algebraMap R S 0) M) := by
    exact LocalizedModule.subsingleton
      (S := Submonoid.powers (algebraMap R S 0)) (M := M)
      (by simpa using Submonoid.mem_powers (algebraMap R S 0))
  letI : Subsingleton (Localization.Away (0 : R)) := hA0
  letI : Subsingleton (Localization.Away (algebraMap R S 0)) := hB0
  letI : Subsingleton (LocalizedModule.Away (algebraMap R S 0) M) := hN0
  -- The zero localizations are subsingleton, hence finite, finitely presented, and free.
  have hfinB :
      Module.Finite (Localization.Away (0 : R))
        (Localization.Away (algebraMap R S 0)) :=
    moduleFinite_of_subsingleton
  letI : Module.Finite (Localization.Away (0 : R))
      (Localization.Away (algebraMap R S 0)) := hfinB
  have hfpBModule :
      Module.FinitePresentation (Localization.Away (0 : R))
        (Localization.Away (algebraMap R S 0)) :=
    moduleFinitePresentation_of_subsingleton
  have hfpAlg :
      Algebra.FinitePresentation (Localization.Away (0 : R))
        (Localization.Away (algebraMap R S 0)) := by
    exact
      (Module.FinitePresentation.iff_finitePresentation_of_finite
        (R := Localization.Away (0 : R))
        (S := Localization.Away (algebraMap R S 0))).mp hfpBModule
  have hfpMod :
      Module.FinitePresentation (Localization.Away (algebraMap R S 0))
        (LocalizedModule.Away (algebraMap R S 0) M) :=
    moduleFinitePresentation_of_subsingleton
  have hfreeAlg :
      Module.Free (Localization.Away (0 : R))
        (Localization.Away (algebraMap R S 0)) := by
    exact Module.Free.of_subsingleton
      (Localization.Away (0 : R)) (Localization.Away (algebraMap R S 0))
  have hfreeMod :
      Module.Free (Localization.Away (0 : R))
        (LocalizedModule.Away (algebraMap R S 0) M) := by
    exact Module.Free.of_subsingleton
      (Localization.Away (0 : R)) (LocalizedModule.Away (algebraMap R S 0) M)
  exact
    { finitePresentation_algebra := hfpAlg
      finitePresentation_module := hfpMod
      free_algebra := hfreeAlg
      free_module := hfreeMod }

/-- Helper for Chap10 Lemma 10 118 7: if a submonoid localization of the base is trivial, then
some denominator from the submonoid already gives the zero localization condition downstairs. -/
private theorem exists_submonoidDenominator_localizationCondition_of_subsingleton
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B] [Algebra A B]
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (U : Submonoid A) (htriv : Subsingleton (Localization U)) :
    ∃ u : U, LocalizationCondition A B N u.1 := by
  -- Equality of `1` and `0` in `U⁻¹A` clears to a denominator of `U` which is zero in `A`.
  letI : Subsingleton (Localization U) := htriv
  have hEq : algebraMap A (Localization U) (1 : A) =
      algebraMap A (Localization U) (0 : A) :=
    Subsingleton.elim _ _
  obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists U (Localization U)).mp hEq
  rw [mul_one, mul_zero] at hu
  refine ⟨u, ?_⟩
  -- The denominator is zero, so the cached zero-parameter condition is exactly the needed one.
  simpa [hu] using (localizationCondition_zero (R := A) (S := B) (M := N))

/-- Helper for Chap10 Lemma 10 118 7: if the principal localization at an element is
subsingleton, then that element is nilpotent. -/
private theorem isNilpotent_of_localizationAway_subsingleton
    {A : Type*} [CommRing A] {x : A} (h : Subsingleton (Localization.Away x)) :
    IsNilpotent x := by
  -- Equality of `1` and `0` in the away localization clears to a zero power of `x`.
  letI : Subsingleton (Localization.Away x) := h
  have hEq :
      algebraMap A (Localization.Away x) (1 : A) =
        algebraMap A (Localization.Away x) (0 : A) :=
    Subsingleton.elim _ _
  obtain ⟨c, hc⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers x) (Localization.Away x)).mp hEq
  rw [mul_one, mul_zero] at hc
  exact (isNilpotent_iff_zero_mem_powers).mpr (by simpa [← hc] using c.2)

/-- Helper for Chap10 Lemma 10 118 7: nilpotent localization parameters satisfy the generic
flatness localization condition because their away localizations are zero localizations. -/
private theorem localizationCondition_of_nilpotent {f : R} (hf : IsNilpotent f) :
    LocalizationCondition R S M f := by
  -- A nilpotent element has zero in its power submonoid, so all localized rings and modules are
  -- subsingleton and the four required fields follow from the subsingleton finite/free helpers.
  have hf0 : (0 : R) ∈ Submonoid.powers f :=
    isNilpotent_iff_zero_mem_powers.mp hf
  have hSf0 : (0 : S) ∈ Submonoid.powers (algebraMap R S f) :=
    isNilpotent_iff_zero_mem_powers.mp (hf.map (algebraMap R S))
  have hA0 : Subsingleton (Localization.Away f) :=
    IsLocalization.subsingleton
      (M := Submonoid.powers f) (S := Localization.Away f) hf0
  have hB0 : Subsingleton (Localization.Away (algebraMap R S f)) :=
    IsLocalization.subsingleton
      (M := Submonoid.powers (algebraMap R S f))
      (S := Localization.Away (algebraMap R S f)) hSf0
  have hN0 : Subsingleton (LocalizedModule.Away (algebraMap R S f) M) :=
    LocalizedModule.subsingleton
      (S := Submonoid.powers (algebraMap R S f)) (M := M) hSf0
  letI : Subsingleton (Localization.Away f) := hA0
  letI : Subsingleton (Localization.Away (algebraMap R S f)) := hB0
  letI : Subsingleton (LocalizedModule.Away (algebraMap R S f) M) := hN0
  have hfinB :
      Module.Finite (Localization.Away f)
        (Localization.Away (algebraMap R S f)) :=
    moduleFinite_of_subsingleton
  letI : Module.Finite (Localization.Away f)
      (Localization.Away (algebraMap R S f)) := hfinB
  have hfpBModule :
      Module.FinitePresentation (Localization.Away f)
        (Localization.Away (algebraMap R S f)) :=
    moduleFinitePresentation_of_subsingleton
  have hfpAlg :
      Algebra.FinitePresentation (Localization.Away f)
        (Localization.Away (algebraMap R S f)) := by
    exact
      (Module.FinitePresentation.iff_finitePresentation_of_finite
        (R := Localization.Away f)
        (S := Localization.Away (algebraMap R S f))).mp hfpBModule
  have hfpMod :
      Module.FinitePresentation (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) :=
    moduleFinitePresentation_of_subsingleton
  have hfreeAlg :
      Module.Free (Localization.Away f)
        (Localization.Away (algebraMap R S f)) := by
    exact Module.Free.of_subsingleton
      (Localization.Away f) (Localization.Away (algebraMap R S f))
  have hfreeMod :
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (algebraMap R S f) M) := by
    exact Module.Free.of_subsingleton
      (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M)
  exact
    { finitePresentation_algebra := hfpAlg
      finitePresentation_module := hfpMod
      free_algebra := hfreeAlg
      free_module := hfreeMod }

/-- Helper for Chap10 Lemma 10 118 7: if the further localization of `R_T` away from the image of
`a` is subsingleton, then multiplying `a` by one denominator from `T` makes it nilpotent in `R`. -/
private theorem exists_submonoid_mul_nilpotent_of_mappedAway_subsingleton
    (T : Submonoid R) (a : R)
    (h : Subsingleton (Localization.Away (algebraMap R (Localization T) a))) :
    ∃ c : T, IsNilpotent (a * c.1) := by
  -- First detect nilpotence of `a / 1` in `R_T`, then clear the remaining `T`-denominator.
  have hnilLocal : IsNilpotent (algebraMap R (Localization T) a) :=
    isNilpotent_of_localizationAway_subsingleton h
  rcases hnilLocal with ⟨n, hn⟩
  have hmap :
      algebraMap R (Localization T) (a ^ n) = algebraMap R (Localization T) 0 := by
    simpa [map_pow] using hn
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists T (Localization T)).mp hmap
  have hc0 : c.1 * a ^ n = 0 := by
    simpa using hc
  refine ⟨c, IsNilpotent.mk (a * c.1) (n + 1) ?_⟩
  calc
    (a * c.1) ^ (n + 1) = (c.1 * a ^ n) * (a * c.1 ^ n) := by
      ring_nf
    _ = 0 := by simp [hc0]

/-- Helper for Chap10 Lemma 10 118 7: if a prime-local witness avoids a point upstairs, then the
chosen numerator avoids the image prime downstairs. -/
private theorem atPrimeSecNumerator_notMem_of_witness_notMem
    (p : PrimeSpectrum R) (q : PrimeSpectrum (Localization.AtPrime p.asIdeal))
    {u : Localization.AtPrime p.asIdeal}
    (hu : u ∉ q.asIdeal)
    (hqImage : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q = p) :
    (IsLocalization.sec p.asIdeal.primeCompl u).1 ∉ p.asIdeal := by
  -- Pull membership of the chosen numerator through the comap equality, then use the section
  -- identity to turn it into membership of the original local witness.
  intro ha
  have haComap :
      (IsLocalization.sec p.asIdeal.primeCompl u).1 ∈
        (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q).asIdeal := by
    simpa [hqImage] using ha
  have haq :
      algebraMap R (Localization.AtPrime p.asIdeal)
          (IsLocalization.sec p.asIdeal.primeCompl u).1 ∈ q.asIdeal := by
    simpa [PrimeSpectrum.comap, Ideal.mem_comap] using haComap
  have hsec :
      algebraMap R (Localization.AtPrime p.asIdeal)
          (IsLocalization.sec p.asIdeal.primeCompl u).1 =
        algebraMap R (Localization.AtPrime p.asIdeal)
          (IsLocalization.sec p.asIdeal.primeCompl u).2 * u :=
    IsLocalization.sec_spec' p.asIdeal.primeCompl u
  have hprod :
      algebraMap R (Localization.AtPrime p.asIdeal)
          (IsLocalization.sec p.asIdeal.primeCompl u).2 * u ∈ q.asIdeal := by
    simpa [hsec] using haq
  have hunit :
      IsUnit (algebraMap R (Localization.AtPrime p.asIdeal)
        (IsLocalization.sec p.asIdeal.primeCompl u).2) :=
    IsLocalization.map_units (Localization.AtPrime p.asIdeal)
      (IsLocalization.sec p.asIdeal.primeCompl u).2
  rcases hunit with ⟨e, he⟩
  have huMem : u ∈ q.asIdeal := by
    have hmul := q.asIdeal.mul_mem_left (↑e⁻¹) hprod
    simpa [← he, mul_assoc] using hmul
  exact hu huMem

/-- Helper for Chap10 Lemma 10 118 7: replacing a localized element by the numerator of its
section preserves the localization condition over an arbitrary submonoid localization. -/
private theorem localizationCondition_associated_sec
    (T : Submonoid R) (u : Localization T)
    (hucond : LocalizationCondition (Localization T)
      (Localization (Algebra.algebraMapSubmonoid S T))
      (LocalizedModule (Algebra.algebraMapSubmonoid S T) M) u) :
    LocalizationCondition (Localization T)
      (Localization (Algebra.algebraMapSubmonoid S T))
      (LocalizedModule (Algebra.algebraMapSubmonoid S T) M)
      (algebraMap R (Localization T) (IsLocalization.sec T u).1) := by
  -- The section identity writes the numerator image as a unit denominator times the original
  -- parameter, so the two parameters are associated in the localized base ring.
  have hunit :
      IsUnit (algebraMap R (Localization T) (IsLocalization.sec T u).2) :=
    IsLocalization.map_units (Localization T) (IsLocalization.sec T u).2
  have hassoc :
      Associated (algebraMap R (Localization T) (IsLocalization.sec T u).1) u := by
    rw [IsLocalization.sec_spec' T u]
    simpa [mul_comm] using
      associated_mul_unit_left u
        (algebraMap R (Localization T) (IsLocalization.sec T u).2) hunit
  -- Associated parameters give the same four fields of `LocalizationCondition`.
  exact
    (localizationCondition_associatedParameter_iff
      (A := Localization T)
      (B := Localization (Algebra.algebraMapSubmonoid S T))
      (N := LocalizedModule (Algebra.algebraMapSubmonoid S T) M)
      hassoc).mpr hucond

/-- Helper for Chap10 Lemma 10 118 7: an away-first principal witness over `R_a` can be read in
the target chart over `R_c` by commuting the product denominator. -/
private theorem localizationCondition_principalChart_of_awayFirstDenominator
    (T : Submonoid R) (a : R) (c : T)
    (hc : LocalizationCondition (Localization.Away a)
      (Localization.Away (algebraMap R S a))
      (LocalizedModule.Away (algebraMap R S a) M)
      (algebraMap R (Localization.Away a) c.1)) :
    LocalizationCondition (Localization.Away c.1)
      (Localization.Away (algebraMap R S c.1))
      (LocalizedModule.Away (algebraMap R S c.1) M)
      (algebraMap R (Localization.Away c.1) a) := by
  -- Convert the away-first chart to the product condition at `a * c`, then commute the product
  -- before returning to the requested `c`-first chart.
  have hProductAC : LocalizationCondition R S M (a * c.1) :=
    (localizationCondition_product_iff_iteratedAway
      (R := R) (S := S) (M := M) a c.1).mpr hc
  have hProductCA : LocalizationCondition R S M (c.1 * a) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hProductAC
  exact
    (localizationCondition_product_iff_iteratedAway
      (R := R) (S := S) (M := M) c.1 a).mp hProductCA

/-- Helper for Chap10 Lemma 10 118 7: an existential away-first denominator witness gives the
principal-chart existential needed by the submonoid spreading step. -/
private theorem exists_principalChart_localizationCondition_of_awayFirstDenominator
    (T : Submonoid R) (a : R)
    (h : ∃ c : T,
      LocalizationCondition (Localization.Away a)
        (Localization.Away (algebraMap R S a))
        (LocalizedModule.Away (algebraMap R S a) M)
        (algebraMap R (Localization.Away a) c.1)) :
    ∃ c : T,
      LocalizationCondition (Localization.Away c.1)
        (Localization.Away (algebraMap R S c.1))
        (LocalizedModule.Away (algebraMap R S c.1) M)
        (algebraMap R (Localization.Away c.1) a) := by
  -- Apply the chart-order adapter to the selected denominator.
  obtain ⟨c, hc⟩ := h
  exact ⟨c, localizationCondition_principalChart_of_awayFirstDenominator
    (R := R) (S := S) (M := M) T a c hc⟩

/-- Helper for Chap10 Lemma 10 118 7: the away-first image-submonoid target localization is an
algebra over the corresponding away-first source localization. -/
private noncomputable instance awayFirstImageSubmonoid_localizedTarget_algebra
    (T : Submonoid R) (a : R) :
    Algebra (Localization (T.map (algebraMap R (Localization.Away a))))
      (Localization
        (Algebra.algebraMapSubmonoid (Localization.Away (algebraMap R S a))
          (T.map (algebraMap R (Localization.Away a))))) := by
  let A' := Localization (T.map (algebraMap R (Localization.Away a)))
  let B' := Localization
    (Algebra.algebraMapSubmonoid (Localization.Away (algebraMap R S a))
      (T.map (algebraMap R (Localization.Away a))))
  -- Naming the two chart rings lets instance search use the canonical localization algebra once.
  exact inferInstanceAs (Algebra A' B')

/-- Helper for Chap10 Lemma 10 118 7: the away-first image-submonoid source acts on the target
localization through the cached algebra structure. -/
private noncomputable instance awayFirstImageSubmonoid_localizedTarget_smul
    (T : Submonoid R) (a : R) :
    SMul (Localization (T.map (algebraMap R (Localization.Away a))))
      (Localization
        (Algebra.algebraMapSubmonoid (Localization.Away (algebraMap R S a))
          (T.map (algebraMap R (Localization.Away a))))) :=
  (awayFirstImageSubmonoid_localizedTarget_algebra (R := R) (S := S) T a).toSMul

/-- Helper for Chap10 Lemma 10 118 7: the away-first image-submonoid localized module is a
module over the away-first localized base by restriction through the localized target ring. -/
private noncomputable instance awayFirstImageSubmonoid_localizedModule_module
    (T : Submonoid R) (a : R) :
    Module (Localization (T.map (algebraMap R (Localization.Away a))))
      (LocalizedModule
        (Algebra.algebraMapSubmonoid (Localization.Away (algebraMap R S a))
          (T.map (algebraMap R (Localization.Away a))))
        (LocalizedModule.Away (algebraMap R S a) M)) := by
  let A' := Localization (T.map (algebraMap R (Localization.Away a)))
  let B' := Localization
    (Algebra.algebraMapSubmonoid (Localization.Away (algebraMap R S a))
      (T.map (algebraMap R (Localization.Away a))))
  let N' := LocalizedModule
    (Algebra.algebraMapSubmonoid (Localization.Away (algebraMap R S a))
      (T.map (algebraMap R (Localization.Away a))))
    (LocalizedModule.Away (algebraMap R S a) M)
  -- The module is already defined over the localized target; restrict scalars along the canonical
  -- algebra map from the away-first localized base.
  exact Module.compHom N' (algebraMap A' B')

/-- Helper for Chap10 Lemma 10 118 7: the away-first localized base acts on the localized module
through the cached restricted module structure. -/
private noncomputable instance awayFirstImageSubmonoid_localizedModule_smul
    (T : Submonoid R) (a : R) :
    SMul (Localization (T.map (algebraMap R (Localization.Away a))))
      (LocalizedModule
        (Algebra.algebraMapSubmonoid (Localization.Away (algebraMap R S a))
          (T.map (algebraMap R (Localization.Away a))))
        (LocalizedModule.Away (algebraMap R S a) M)) :=
  (awayFirstImageSubmonoid_localizedModule_module (R := R) (S := S) (M := M) T a).toSMul

/-- Helper for Chap10 Lemma 10 118 7: the away-first image-submonoid chart has the scalar tower
from localized base to localized target to localized module. -/
private noncomputable instance awayFirstImageSubmonoid_isScalarTower
    (T : Submonoid R) (a : R) :
    IsScalarTower (Localization (T.map (algebraMap R (Localization.Away a))))
      (Localization
        (Algebra.algebraMapSubmonoid (Localization.Away (algebraMap R S a))
          (T.map (algebraMap R (Localization.Away a)))))
      (LocalizedModule
        (Algebra.algebraMapSubmonoid (Localization.Away (algebraMap R S a))
          (T.map (algebraMap R (Localization.Away a))))
        (LocalizedModule.Away (algebraMap R S a) M)) := by
  -- Both actions were cached from the same target-ring restriction, so scalar-tower compatibility
  -- reduces to the definition of `Module.compHom`.
  refine IsScalarTower.of_algebraMap_smul ?_
  intro r x
  rfl

/-- Helper for Chap10 Lemma 10 118 7: denominators in the common localization submonoid
generated by `T` and a numerator avoiding a prime also avoid that prime. -/
private theorem notMem_prime_of_mem_localizationLocalizationSubmodule
    (p : Ideal R) [p.IsPrime] (T : Submonoid R) (a x : R)
    (hT : ∀ t : T, (t : R) ∉ p) (ha : a ∉ p)
    (hx : x ∈ IsLocalization.localizationLocalizationSubmodule T
      (Submonoid.powers (algebraMap R (Localization T) a))) :
    x ∉ p := by
  -- Unpack the common-submonoid membership, then clear the equality in `T⁻¹R` back to `R`.
  intro hxmem
  rcases IsLocalization.mem_localizationLocalizationSubmodule.mp hx with ⟨y, z, hxyz⟩
  rcases (Submonoid.mem_powers_iff (y : Localization T)
      (algebraMap R (Localization T) a)).mp y.2 with ⟨n, hyn⟩
  have hmapEq :
      algebraMap R (Localization T) x =
        algebraMap R (Localization T) (a ^ n * z.1) := by
    calc
      algebraMap R (Localization T) x =
          y * algebraMap R (Localization T) z.1 := hxyz
      _ = (algebraMap R (Localization T) a) ^ n *
          algebraMap R (Localization T) z.1 := by
            rw [hyn]
      _ = algebraMap R (Localization T) (a ^ n * z.1) := by
            simp [map_mul, map_pow]
  obtain ⟨d, hd⟩ := (IsLocalization.eq_iff_exists T (Localization T)).mp hmapEq
  have hprod_mem : d.1 * (a ^ n * z.1) ∈ p := by
    rw [← hd]
    exact p.mul_mem_left d.1 hxmem
  have hd_not : (d : R) ∉ p := hT d
  have hz_not : (z : R) ∉ p := hT z
  -- Primality excludes every factor on the right: first powers of `a`, then the `T`-denominator.
  have ha_pow_not : a ^ n ∉ p := fun hpow ↦
    ha ((show p.IsPrime from inferInstance).mem_of_pow_mem n hpow)
  have hright : a ^ n * z.1 ∈ p :=
    ((Ideal.IsPrime.mem_or_mem (I := p) (x := d.1) (y := a ^ n * z.1)
      inferInstance) hprod_mem).resolve_left hd_not
  have hz_or :=
    (Ideal.IsPrime.mem_or_mem (I := p) (x := a ^ n) (y := z.1) inferInstance) hright
  exact hz_or.elim ha_pow_not hz_not

/-- Helper for Chap10 Lemma 10 118 7: the four direct stalk fields assemble to the unit
localization condition over `R_𝔭`. -/
private theorem atPrimeLocalizationCondition_one_of_fields
    [Algebra.FiniteType R S] [Module.Finite S M] (p : PrimeSpectrum R)
    [Module (Localization.AtPrime p.asIdeal)
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M)]
    [IsScalarTower (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M)]
    (hfpAlg : Algebra.FinitePresentation (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
    (hfpMod : Module.FinitePresentation
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M))
    (hfreeAlg : Module.Free (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
    (hfreeMod : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M)) :
    LocalizationCondition (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M) 1 := by
  -- Install the four stalk fields as instances and use the general fieldwise constructor at the
  -- unit parameter.
  letI : Algebra.FinitePresentation (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) := hfpAlg
  letI : Module.FinitePresentation
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M) := hfpMod
  letI : Module.Free (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) := hfreeAlg
  letI : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M) := hfreeMod
  -- The four stalk fields now have the same scalar-tower spelling expected by the fieldwise
  -- constructor.
  exact localizationCondition_of_fields
    (A := Localization.AtPrime p.asIdeal)
    (B := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
    (N := LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M) 1

/-- Helper for Chap10 Lemma 10 118 7: a prime-complement localization condition is exactly a
good-locus witness at the chosen prime. -/
private theorem mem_goodLocus_of_primeCompl_localizationCondition
    (p : PrimeSpectrum R) {t : p.asIdeal.primeCompl}
    (htcond : LocalizationCondition R S M t.1) :
    p ∈ goodLocus R S M := by
  -- The denominator avoids `p`, so the corresponding basic open contains `p`.
  rw [mem_goodLocus_iff]
  exact ⟨t.1, htcond, t.2⟩

/-- Helper for Chap10 Lemma 10 118 7: membership in the good locus gives a denominator in the
prime complement. -/
private theorem exists_primeCompl_localizationCondition_of_mem_goodLocus
    (p : PrimeSpectrum R) (hp : p ∈ goodLocus R S M) :
    ∃ t : p.asIdeal.primeCompl, LocalizationCondition R S M t.1 := by
  -- Unpack the defining basic-open witness and bundle its nonmembership proof.
  obtain ⟨t, htcond, htNotMem⟩ := (mem_goodLocus_iff (R := R) (S := S) (M := M) p).mp hp
  exact ⟨⟨t, htNotMem⟩, htcond⟩

/-- Helper for Chap10 Lemma 10 118 7: direct finite-presentation and freeness fields over the
stalk make every prime of the stalk lie in the localized good locus. -/
private theorem all_primes_mem_atPrime_goodLocus_of_fields
    [Algebra.FiniteType R S] [Module.Finite S M] (p : PrimeSpectrum R)
    [Module (Localization.AtPrime p.asIdeal)
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M)]
    [IsScalarTower (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M)]
    (hfpAlg : Algebra.FinitePresentation (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
    (hfpMod : Module.FinitePresentation
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M))
    (hfreeAlg : Module.Free (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
    (hfreeMod : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M)) :
    ∀ q : PrimeSpectrum (Localization.AtPrime p.asIdeal),
      q ∈ goodLocus (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
        (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M) := by
  -- Assemble the four stalk fields once, then use the unit denominator at every stalk prime.
  have hunitCondition :
      LocalizationCondition (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
        (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M) 1 :=
    atPrimeLocalizationCondition_one_of_fields
      (R := R) (S := S) (M := M) p hfpAlg hfpMod hfreeAlg hfreeMod
  intro q
  rw [mem_goodLocus_iff]
  refine ⟨1, hunitCondition, ?_⟩
  exact q.isPrime.one_notMem

/-- Helper for Chap10 Lemma 10 118 7: direct finite-presentation and freeness fields at
`R_𝔭` spread to one principal open around `𝔭`. -/
private theorem exists_primeCompl_localizationCondition_of_atPrime_fields
    [Algebra.FiniteType R S] [Module.Finite S M] (p : PrimeSpectrum R)
    [Module (Localization.AtPrime p.asIdeal)
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M)]
    [IsScalarTower (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M)]
    (hfpAlg : Algebra.FinitePresentation (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
    (hfpMod : Module.FinitePresentation
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M))
    (hfreeAlg : Module.Free (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
    (hfreeMod : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M)) :
    ∃ t : p.asIdeal.primeCompl, LocalizationCondition R S M t.1 := by
  have hlocalizedGood :
      ∀ q : PrimeSpectrum (Localization.AtPrime p.asIdeal),
        q ∈ goodLocus (Localization.AtPrime p.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
          (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M) :=
    all_primes_mem_atPrime_goodLocus_of_fields
      (R := R) (S := S) (M := M) p hfpAlg hfpMod hfreeAlg hfreeMod
  have hpGood : p ∈ goodLocus R S M := by
    -- TODO: prove the localization-at-prime good-locus descent.  The verified prefix above shows
    -- that the whole stalk spectrum lies in the localized good locus; the remaining theorem should
    -- turn this, for a prime lying over `p`, into one denominator `t ∉ p` with
    -- `LocalizationCondition R S M t`.
    sorry
  -- Convert membership in the downstairs good locus into the requested prime-complement witness.
  exact exists_primeCompl_localizationCondition_of_mem_goodLocus (R := R) (S := S) (M := M) p hpGood

/-- Helper for Chap10 Lemma 10 118 7: a unit-parameter local witness over `R_𝔭` gives one
principal-open witness in `R`. -/
private theorem exists_primeCompl_localizationCondition_of_atPrime_unit
    [Algebra.FiniteType R S] [Module.Finite S M] (p : PrimeSpectrum R)
    {u : Localization.AtPrime p.asIdeal}
    (hucond : LocalizationCondition (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M) u)
    (huunit : IsUnit u) :
    ∃ t : p.asIdeal.primeCompl, LocalizationCondition R S M t.1 := by
  -- Normalize the unit-parameter condition to direct fields over the stalk, then leave only the
  -- stalk-to-basic-open spreading step for the dedicated helper above.
  let moduleLocalized : Module (Localization.AtPrime p.asIdeal)
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M) :=
    Module.compHom
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M)
      (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
  letI : Module (Localization.AtPrime p.asIdeal)
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M) :=
    moduleLocalized
  letI : IsScalarTower (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M) :=
    IsScalarTower.of_compHom (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M)
  obtain ⟨hfpAlg, hfpMod, hfreeAlg, hfreeMod⟩ :=
    localizationCondition_fields_of_isUnit hucond huunit
  exact exists_primeCompl_localizationCondition_of_atPrime_fields
    (R := R) (S := S) (M := M) p hfpAlg hfpMod hfreeAlg hfreeMod

/-- Helper for Chap10 Lemma 10 118 7: a good-locus point over `R_𝔭` descends to one principal
open around `𝔭` in `Spec R`. -/
private theorem exists_primeCompl_localizationCondition_of_atPrime_goodLocus
    [Algebra.FiniteType R S] [Module.Finite S M] (p : PrimeSpectrum R)
    (hfield : IsField (Localization.AtPrime p.asIdeal))
    (q : PrimeSpectrum (Localization.AtPrime p.asIdeal))
    (hqGood : q ∈ goodLocus (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M)) :
    ∃ t : p.asIdeal.primeCompl, LocalizationCondition R S M t.1 := by
  -- Route correction: avoid the obsolete arbitrary-submonoid/common-chart denominator clearing.
  -- Since this helper is only consumed after `R_𝔭` has been shown to be a field, a witness
  -- avoiding any prime of `R_𝔭` is a unit, reducing the descent to direct stalk fields.
  letI : IsField (Localization.AtPrime p.asIdeal) := hfield
  rw [mem_goodLocus_iff] at hqGood
  obtain ⟨u, hucond, huq⟩ := hqGood
  have hu_ne_zero : u ≠ 0 := by
    intro hu_zero
    exact huq (by simpa [hu_zero] using (q.asIdeal.zero_mem : (0 :
      Localization.AtPrime p.asIdeal) ∈ q.asIdeal))
  have huunit : IsUnit u := by
    obtain ⟨v, hv⟩ := hfield.mul_inv_cancel hu_ne_zero
    exact ⟨⟨u, v, hv, by simpa [hfield.mul_comm v u] using hv⟩, rfl⟩
  exact exists_primeCompl_localizationCondition_of_atPrime_unit
    (R := R) (S := S) (M := M) p hucond huunit

/-- Helper for Lemma 10.118.7: the remaining reduced-case density argument is to show that every
minimal prime lies in the closure of the good locus by passing to `Localization.AtPrime`. -/
private theorem minimalPrime_mem_closure_goodLocus
    [Algebra.FiniteType R S] [Module.Finite S M] [IsReduced R]
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R) :
    p ∈ closure (goodLocus R S M) := by
  -- Route correction: avoid the obsolete full preimage equality for arbitrary prime
  -- localization.  The useful prefix is the field/domain argument at `R_𝔭`; the remaining
  -- missing API is the one-way spreading of a unit-parameter local witness back to one
  -- principal open in `Spec R`.
  let Rp := Localization.AtPrime p.asIdeal
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let Mp := LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M
  have hsubsingleton : Subsingleton (PrimeSpectrum Rp) := by
    -- Minimality of `p` makes the prime spectrum of `R_𝔭` a singleton.
    simpa [Rp] using
      (IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes p.asIdeal hp Rp)
  have hfield : IsField Rp := by
    -- A reduced ring with singleton spectrum is a field.
    letI : Subsingleton (PrimeSpectrum Rp) := hsubsingleton
    exact (PrimeSpectrum.subsingleton_iff_isField_of_isReduced (R := Rp)).mp inferInstance
  letI : IsField Rp := hfield
  letI : IsDomain Rp := hfield.isDomain
  letI : Algebra Rp Sp := inferInstance
  letI : Algebra.FiniteType Rp Sp := finiteType_localizationAtPrime (R := R) (S := S) p
  letI : Module.Finite Sp Mp := inferInstance
  have hDenseLoc : Dense (goodLocus Rp Sp Mp) := by
    -- After localizing at the minimal prime, the domain case applies to the localized pair.
    exact dense_goodLocus_of_isDomain (R := Rp) (S := Sp) (M := Mp)
  let q : PrimeSpectrum Rp := ⟨⊥, Ideal.isPrime_bot⟩
  have hqMem : q ∈ closure (goodLocus Rp Sp Mp) := hDenseLoc q
  have hqGood : q ∈ goodLocus Rp Sp Mp := by
    -- Since `Spec(Rp)` is a singleton, density gives an actual local good-locus point and that
    -- point must be the chosen prime `q`.
    have hnonempty : (goodLocus Rp Sp Mp).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hqMem
      simpa only [closure_empty] using hqMem
    obtain ⟨q', hq'⟩ := hnonempty
    simpa [Subsingleton.elim q' q] using hq'
  obtain ⟨t, htcond⟩ :=
    exists_primeCompl_localizationCondition_of_atPrime_goodLocus
      (R := R) (S := S) (M := M) p hfield q hqGood
  have hpGood : p ∈ goodLocus R S M := by
    -- The spread denominator avoids `p`, so its basic open contains `p` and is one of the
    -- standard opens in the defining union of the good locus.
    exact mem_goodLocus_of_primeCompl_localizationCondition
      (R := R) (S := S) (M := M) p htcond
  -- Membership in the good locus immediately gives membership in its closure.
  exact subset_closure hpGood

/-- Lemma 10.118.7: if `R → S` is of finite type, `M` is a finite `S`-module, and `R` is
reduced, then the generic-flatness good locus `U(R → S, M)` is dense in `Spec(R)`. This is the
canonical reformulation of the textbook statement asserting the existence of an open dense subset
on which, Zariski-locally, `S_f` is a finitely presented free `R_f`-algebra and `M_f` is a
finitely presented free `S_f`-module over `R_f`. -/
-- Proof sketch: this is the density statement proved in the text for the good locus
-- `U(R → S, M)`, first for polynomial algebras by induction and Noether normalization and then in
-- general by passing to a polynomial presentation of `S`.
@[stacks 051Z]
theorem dense_goodLocus_of_finiteType_finiteModule_reduced
    [Algebra.FiniteType R S] [Module.Finite S M] [IsReduced R] :
    Dense (goodLocus R S M) := by
  -- Reduce density to a pointwise closure statement on minimal primes.
  exact dense_of_minimalPrimes_mem_closure (R := R) (U := goodLocus R S M) fun p hp ↦
    minimalPrime_mem_closure_goodLocus (R := R) (S := S) (M := M) p hp

end GenericFlatness

end
