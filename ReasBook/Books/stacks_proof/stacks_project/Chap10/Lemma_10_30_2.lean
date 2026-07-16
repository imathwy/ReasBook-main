import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Finiteness.Quotient
import stacks_proof.stacks_project.Chap05.Lemma_5_15_15
import stacks_proof.stacks_project.Chap10.Lemma_10_17_6
import stacks_proof.stacks_project.Chap10.Lemma_10_17_7
import stacks_proof.stacks_project.Chap10.Lemma_10_29_2
import stacks_proof.stacks_project.Chap10.Lemma_10_30_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set Topology PrimeSpectrum TopologicalSpace
open scoped Set.Notation

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}
variable {E : Set (PrimeSpectrum S)} {ξ : PrimeSpectrum R}

local notation "Zξ" => closure (Set.singleton ξ : Set (PrimeSpectrum R))
local notation "traceOnClosure" =>
  (((Subtype.val : Zξ → PrimeSpectrum R) ⁻¹' (PrimeSpectrum.comap f '' E)))

/- Layering for this item:
* source-facing: the existence of an open dense subset in the trace of `comap f '' E` on
  `closure {ξ}` for a finite type map;
* core/canonical owner: `PrimeSpectrum.comap`, `IsConstructible`, and the generic-point space
  `closure ({ξ} : Set (PrimeSpectrum R))`;
* bridge/view: the finite-presentation constructible-image theorem
  `PrimeSpectrum.isConstructible_comap_image`, the generic-point package `isGenericPoint_closure`,
  and the Chapter 5 dense-trace criteria
  `IsIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed`
  and `IsGenericPoint.dense_preimage_iff_mem_of_isFiniteUnionOfLocallyClosed`.
-/

/-- Helper for Lemma 10.30.2: the spectrum of the quotient `R / x` identifies with the closure of
`x` via the quotient map on prime spectra. -/
lemma quotient_range_comap_eq_closure_singleton (x : PrimeSpectrum R) :
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk x.asIdeal)) =
      closure ({x} : Set (PrimeSpectrum R)) := by
  -- The quotient-spectrum image is the zero locus of the quotient ideal, which is exactly
  -- `closure {x}`.
  rw [range_comap_of_surjective (R ⧸ x.asIdeal) (Ideal.Quotient.mk x.asIdeal)
      Ideal.Quotient.mk_surjective]
  rw [Ideal.mk_ker]
  rw [PrimeSpectrum.closure_singleton]

/-- Helper for Lemma 10.30.2: a dense open subset of a dense open subspace extends to an open
dense subset of the ambient space, and intersecting back with the ambient open recovers the
original subspace-open set. -/
lemma image_open_dense_of_dense_open_subspace
    {X : Type u} [TopologicalSpace X] {U : Set X} (hU_open : IsOpen U) (hU_dense : Dense U)
    {W : Set U} (hW_open : IsOpen W) (hW_dense : Dense W) :
    ∃ V : Opens X,
      Dense (V : Set X) ∧ (V : Set X) ⊆ U ∧ ((Subtype.val : U → X) ⁻¹' (V : Set X)) = W := by
  obtain ⟨V₀, hV₀_open, hV₀_dense, hV₀_preimage⟩ :=
    exists_open_dense_of_open_dense_subtype (s := U) hU_dense hW_open hW_dense
  let V : Opens X := ⟨V₀ ∩ U, hV₀_open.inter hU_open⟩
  have hU_subset_closure : U ⊆ closure (V₀ ∩ U) := by
    -- Density in the subtype means the image of `W` is dense in `U`.
    rw [Subtype.dense_iff] at hW_dense
    have hW_image : ((↑) : U → X) '' W = U ∩ V₀ := by
      calc
        ((↑) : U → X) '' W = ((↑) : U → X) '' (((↑) : U → X) ⁻¹' V₀) := by
          rw [hV₀_preimage]
        _ = U ∩ V₀ := Subtype.image_preimage_coe U V₀
    simpa [hW_image, Set.inter_comm] using hW_dense
  have hV_dense : Dense (V : Set X) := by
    -- Since `U` is already dense in `X`, density of `V₀ ∩ U` inside `U` makes it dense in `X`.
    intro x
    exact by
      simpa [V, closure_closure, Set.inter_comm] using closure_mono hU_subset_closure (hU_dense x)
  have hV_preimage : ((Subtype.val : U → X) ⁻¹' (V : Set X)) = W := by
    -- Intersecting the ambient open with `U` does not change its trace on the subtype.
    ext x
    simp [V, hV₀_preimage]
  refine ⟨V, hV_dense, ?_, hV_preimage⟩
  -- By construction, the ambient open lies inside `U`.
  intro x hx
  exact hx.2

/-- Helper for Lemma 10.30.2: in the spectrum of a domain, a constructible subset containing the
generic point contains an open dense subset. -/
lemma exists_open_dense_subset_of_constructible_generic_mem
    {A : Type u} [CommRing A] [IsDomain A] {C : Set (PrimeSpectrum A)}
    (hC : IsConstructible C) (hgeneric : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ C) :
    ∃ U : Opens (PrimeSpectrum A), Dense (U : Set (PrimeSpectrum A)) ∧ (U : Set _) ⊆ C := by
  let ξ0 : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hξ0 : IsGenericPoint ξ0 (Set.univ : Set (PrimeSpectrum A)) := by
    -- In a domain, the zero prime is the generic point of the whole spectrum.
    simpa [ξ0, PrimeSpectrum.closure_singleton, PrimeSpectrum.zeroLocus_singleton_zero] using
      (isGenericPoint_closure :
        IsGenericPoint ξ0 (closure ({ξ0} : Set (PrimeSpectrum A))))
  let X0 : Set (PrimeSpectrum A) := Set.univ
  have hDenseTrace :
      Dense (((Subtype.val : X0 → PrimeSpectrum A) ⁻¹' C)) := by
    -- The generic-point criterion upgrades membership of `ξ0` to density on the whole-space
    -- subtype.
    simpa using
      (IsGenericPoint.dense_preimage_iff_mem_of_isFiniteUnionOfLocallyClosed
        (hξ := hξ0) hC.isFiniteUnionOfLocallyClosed).2 hgeneric
  obtain ⟨W, hW_dense, hW_subset⟩ :=
    (hξ0.isIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed
      hC.isFiniteUnionOfLocallyClosed).2 hDenseTrace
  have hX0_open : IsOpen X0 := by
    simpa [X0] using (isOpen_univ : IsOpen (Set.univ : Set (PrimeSpectrum A)))
  have hX0_dense : Dense X0 := by
    simpa [X0] using (dense_univ : Dense (Set.univ : Set (PrimeSpectrum A)))
  obtain ⟨U, hU_dense, -, hU_preimage⟩ :=
    image_open_dense_of_dense_open_subspace
      (U := X0) hX0_open hX0_dense W.2 hW_dense
  refine ⟨U, hU_dense, ?_⟩
  -- Membership in the transported open subset pulls back to `W`, hence to `C`.
  intro x hxU
  have hxPre :
      (⟨x, by simp [X0]⟩ : X0) ∈
        ((Subtype.val : X0 → PrimeSpectrum A) ⁻¹' (U : Set (PrimeSpectrum A))) := by
    simpa [X0] using hxU
  have hxW : (⟨x, by simp [X0]⟩ : X0) ∈ (W : Set X0) := by
    simpa [hU_preimage] using hxPre
  simpa [X0] using hW_subset hxW

/-- Helper for Lemma 10.30.2: in the spectrum of a domain, every basic open defined by a nonzero
element is dense. -/
lemma basicOpen_dense_of_nonzero_of_isDomain
    {A : Type u} [CommRing A] [IsDomain A] (a : A) (ha : a ≠ 0) :
    Dense (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
  let ξ0 : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hξ0_mem : ξ0 ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
    -- The generic prime is disjoint from every nonzero basic-open parameter.
    exact (PrimeSpectrum.mem_basicOpen a ξ0).2 <| by simpa [ξ0] using ha
  obtain ⟨U, hU_dense, hU_subset⟩ :=
    exists_open_dense_subset_of_constructible_generic_mem
      (A := A) PrimeSpectrum.isConstructible_basicOpen hξ0_mem
  -- A dense subset of `D(a)` forces `D(a)` itself to be dense.
  exact Dense.mono hU_subset hU_dense

/-- Helper for Lemma 10.30.2: localizing a constructible subset that already contains the generic
point preserves both constructibility and generic-point membership. -/
lemma localized_preimage_constructible_generic_mem
    {B : Type u} [CommRing B] [IsDomain B] (c : B) (hc : c ≠ 0)
    {C : Set (PrimeSpectrum B)} (hC : IsConstructible C)
    (hgeneric : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ C) :
    letI : IsDomain (Localization.Away c) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away c)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hc)
    IsConstructible
        (PrimeSpectrum.comap (algebraMap B (Localization.Away c)) ⁻¹' C) ∧
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.Away c)) ∈
        PrimeSpectrum.comap (algebraMap B (Localization.Away c)) ⁻¹' C := by
  letI : IsDomain (Localization.Away c) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away c)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hc)
  constructor
  · -- Constructible sets stay constructible after pulling back along the localization chart.
    exact primeSpectrum_comap_preimage_isConstructible (algebraMap B (Localization.Away c)) hC
  · -- The generic point of the localized domain contracts back to the generic point of `Spec B`.
    have hinj : Function.Injective (algebraMap B (Localization.Away c)) := by
      exact IsLocalization.injective (Localization.Away c)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hc)
    have hgeneric_comap :
        PrimeSpectrum.comap (algebraMap B (Localization.Away c))
            (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.Away c)) =
          (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) := by
      apply PrimeSpectrum.ext
      rw [PrimeSpectrum.comap_asIdeal, Ideal.comap_bot_of_injective _ hinj]
    change PrimeSpectrum.comap (algebraMap B (Localization.Away c))
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.Away c)) ∈ C
    rw [hgeneric_comap]
    exact hgeneric

/-- Helper for Lemma 10.30.2: contracting `η` along `f` recovers the ideal of `ξ`. -/
lemma quotient_comap_eq_of_comap_eq
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ) :
    ξ.asIdeal = Ideal.comap f η.asIdeal := by
  -- This is the ideal-level form of the hypothesis `PrimeSpectrum.comap f η = ξ`.
  simpa [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hηξ).symm

/-- Helper for Lemma 10.30.2: the map `f` descends to the quotient rings at `ξ` and `η`. -/
def quotient_map_of_comap_eq
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ) :
    R ⧸ ξ.asIdeal →+* S ⧸ η.asIdeal :=
  Ideal.quotientMap η.asIdeal f
    (le_of_eq (quotient_comap_eq_of_comap_eq (f := f) (ξ := ξ) hηξ))

/-- Helper for Lemma 10.30.2: the descended quotient map commutes with the original map after
precomposing with the quotient map at `ξ`. -/
lemma quotient_map_of_comap_eq_comp_quotient_mk
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ) :
    (quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ).comp (Ideal.Quotient.mk ξ.asIdeal) =
      (Ideal.Quotient.mk η.asIdeal).comp f := by
  -- Both ring homomorphisms send `r : R` to its class in `S / η`.
  ext r
  rfl

/-- Helper for Lemma 10.30.2: the descended quotient map is injective because its source ideal is
exactly the contracted target ideal. -/
lemma quotient_map_of_comap_eq_injective
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ) :
    Function.Injective (quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ) := by
  let hηξIdeal : ξ.asIdeal = Ideal.comap f η.asIdeal :=
    quotient_comap_eq_of_comap_eq (f := f) (ξ := ξ) hηξ
  -- Once the contracted ideal agrees with `ξ.asIdeal`, the owner quotient-map criterion applies.
  simpa [quotient_map_of_comap_eq, hηξIdeal] using
    (Ideal.quotientMap_injective' (f := f) (I := η.asIdeal) (J := ξ.asIdeal)
      (h := le_of_eq hηξIdeal.symm))

/-- Helper for Lemma 10.30.2: after choosing a point `η` above `ξ`, the quotient map
`R / ξ → S / η` satisfies the domain and finite-type hypotheses needed to apply
Lemma `10.30.1`. -/
lemma quotient_localization_data_of_comap_eq
    (hf : f.FiniteType) {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ) :
    let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
    ∃ (a : R ⧸ ξ.asIdeal) (_ : a ≠ 0) (b : S ⧸ η.asIdeal) (_ : b ≠ 0),
      (((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
        (Localization.awayMap fbar a)) :
          Localization.Away a →+* Localization.Away ((fbar a) * b)).FinitePresentation := by
  letI : Algebra R S := f.toAlgebra
  let hηξIdeal : ξ.asIdeal = Ideal.comap f η.asIdeal :=
    quotient_comap_eq_of_comap_eq (f := f) (ξ := ξ) hηξ
  letI : η.asIdeal.LiesOver ξ.asIdeal := by
    -- The chosen point `η` lies over `ξ` exactly because it contracts to `ξ`.
    refine ⟨?_⟩
    exact hηξIdeal
  letI : Algebra (R ⧸ ξ.asIdeal) (S ⧸ η.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq hηξIdeal)
  letI : Algebra.FiniteType R S := by
    -- Reinterpret finite type for the ring map `f` as finite type for the induced algebra.
    rw [← RingHom.finiteType_algebraMap]
    simpa using hf
  letI : IsDomain (R ⧸ ξ.asIdeal) := (Ideal.Quotient.isDomain_iff_prime (I := ξ.asIdeal)).2 ξ.isPrime
  letI : IsDomain (S ⧸ η.asIdeal) := (Ideal.Quotient.isDomain_iff_prime (I := η.asIdeal)).2 η.isPrime
  letI : FaithfulSMul (R ⧸ ξ.asIdeal) (S ⧸ η.asIdeal) := inferInstance
  letI : Algebra.FiniteType (R ⧸ ξ.asIdeal) (S ⧸ η.asIdeal) := inferInstance
  -- Lemma `10.30.1` now applies directly to the quotient-domain map.
  simpa [quotient_map_of_comap_eq, quotient_comap_eq_of_comap_eq] using
    (exists_nonzero_localizationAwayProductMap_finitePresentation
      (R := R ⧸ ξ.asIdeal) (S := S ⧸ η.asIdeal))

/-- Helper for Lemma 10.30.2: the pullback of `E` to `Spec(S / η)` is constructible and contains
the generic point of the quotient domain. -/
lemma quotient_preimage_constructible_generic_mem
    {η : PrimeSpectrum S} (hE : IsConstructible E) (hηE : η ∈ E) :
    IsConstructible (PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E) ∧
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (S ⧸ η.asIdeal)) ∈
        PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E := by
  constructor
  · -- Constructible sets stay constructible after pulling back along any `Spec` map.
    exact primeSpectrum_comap_preimage_isConstructible (Ideal.Quotient.mk η.asIdeal) hE
  · -- The generic point of `Spec(S / η)` maps back to the chosen prime `η`.
    have hgeneric :
        PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal)
            (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (S ⧸ η.asIdeal)) = η := by
      apply PrimeSpectrum.ext
      rw [PrimeSpectrum.comap_asIdeal, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    change PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal)
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (S ⧸ η.asIdeal)) ∈ E
    rw [hgeneric]
    exact hηE

/-- Helper for Lemma 10.30.2: in the localized finite-presentation chart, the localization map has
trivial kernel, so the zero prime contracts to the zero prime. -/
lemma localized_chart_comap_bot_eq_bot
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {a : R ⧸ ξ.asIdeal} (ha : a ≠ 0) {b : S ⧸ η.asIdeal} (hb : b ≠ 0) :
    let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
    let g : Localization.Away a →+* Localization.Away ((fbar a) * b) :=
      ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
        (Localization.awayMap fbar a))
    Ideal.comap g (⊥ : Ideal (Localization.Away ((fbar a) * b))) =
      (⊥ : Ideal (Localization.Away a)) := by
  let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
  let g : Localization.Away a →+* Localization.Away ((fbar a) * b) :=
    ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
      (Localization.awayMap fbar a))
  letI : IsDomain (Localization.Away a) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away a)
      (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  have hfbar_inj : Function.Injective fbar :=
    quotient_map_of_comap_eq_injective (f := f) (ξ := ξ) hηξ
  have hfa : fbar a ≠ 0 := by
    intro hzero
    exact ha (hfbar_inj <| by simpa using hzero)
  have hab : (fbar a) * b ≠ 0 := mul_ne_zero hfa hb
  letI : IsDomain (Localization.Away ((fbar a) * b)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      (Localization.Away ((fbar a) * b))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hab)
  let qmap : R ⧸ ξ.asIdeal →+* Localization.Away ((fbar a) * b) :=
    (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))).comp fbar
  have hqmap_inj : Function.Injective qmap := by
    intro x y hxy
    apply hfbar_inj
    exact (IsLocalization.injective (Localization.Away ((fbar a) * b))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hab)) hxy
  have hqmapa_unit : IsUnit (qmap a) := by
    -- Inverting `(fbar a) * b` also makes `fbar a` invertible in the target localization.
    change IsUnit
      (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b)) (fbar a))
    exact IsLocalization.Away.isUnit_of_dvd (S := Localization.Away ((fbar a) * b))
      (x := (fbar a) * b) (dvd_mul_right _ _)
  letI : IsLocalization.Away (qmap a) (Localization.Away ((fbar a) * b)) :=
    IsLocalization.away_of_isUnit_of_bijective _ hqmapa_unit Function.bijective_id
  have hg_eq :
      g =
        IsLocalization.Away.map
          (Localization.Away a) (Localization.Away ((fbar a) * b)) qmap a := by
    refine (IsLocalization.map_unique
      (M := Submonoid.powers a)
      (T := Submonoid.powers (qmap a))
      (S := Localization.Away a)
      (P := Localization.Away ((fbar a) * b))
      (Q := Localization.Away ((fbar a) * b))
      (g := qmap)
      (hy := by
        rintro y ⟨n, rfl⟩
        exact ⟨n, by simp⟩)
      g ?_).symm
    intro x
    -- Both maps agree on the image of `R / ξ`, so the localization universal property identifies
    -- them.
    change g (algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a) x) = qmap x
    change
      (IsLocalization.Away.awayToAwayRight (fbar a) b)
        ((Localization.awayMap fbar a)
          (algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a) x)) = qmap x
    have hawayMap_eq :
        (Localization.awayMap fbar a)
          (algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a) x) =
            algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a)) (fbar x) := by
      simpa [Localization.awayMap] using
        (IsLocalization.map_eq
          (S := Localization.Away a)
          (Q := Localization.Away (fbar a))
          (g := fbar)
          (hy := by
            rintro y ⟨n, rfl⟩
            exact ⟨n, by simp⟩)
          x)
    rw [hawayMap_eq]
    simpa [qmap] using
      (IsLocalization.Away.awayToAwayRight_eq
        (S := Localization.Away (fbar a))
        (P := Localization.Away ((fbar a) * b))
        (x := fbar a) (y := b) (fbar x))
  have hg_inj : Function.Injective g := by
    rw [hg_eq]
    exact IsLocalization.map_injective_of_injective _ _ _ hqmap_inj
  -- Route correction: instead of unfolding the localization chart directly, identify `g` with the
  -- universal localization map and use injectivity to contract the zero prime.
  exact Ideal.comap_bot_of_injective _ hg_inj

/-- Helper for Lemma 10.30.2: a witness in the localized chart image contracts to a witness in the
quotient-spectrum image. -/
lemma localized_chart_pointwise_to_quotient_image
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {a : R ⧸ ξ.asIdeal} {b : S ⧸ η.asIdeal}
    {xloc : PrimeSpectrum (Localization.Away a)}
    (hxloc :
      let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
      let g : Localization.Away a →+* Localization.Away ((fbar a) * b) :=
        ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
          (Localization.awayMap fbar a))
      let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
        PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
      let Eloc : Set (PrimeSpectrum (Localization.Away ((fbar a) * b))) :=
        PrimeSpectrum.comap
          (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη
      xloc ∈ PrimeSpectrum.comap g '' Eloc) :
    let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
    let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
      PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
    PrimeSpectrum.comap (algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a)) xloc ∈
      PrimeSpectrum.comap fbar '' Eη := by
  let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
  let g : Localization.Away a →+* Localization.Away ((fbar a) * b) :=
    ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
      (Localization.awayMap fbar a))
  let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
    PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
  let Eloc : Set (PrimeSpectrum (Localization.Away ((fbar a) * b))) :=
    PrimeSpectrum.comap
      (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη
  change xloc ∈ PrimeSpectrum.comap g '' Eloc at hxloc
  change PrimeSpectrum.comap (algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a)) xloc ∈
      PrimeSpectrum.comap fbar '' Eη
  rcases hxloc with ⟨yloc, hyloc, rfl⟩
  refine ⟨PrimeSpectrum.comap
      (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) yloc, hyloc, ?_⟩
  -- Compare the two contractions by rewriting both as a single contraction from the localized
  -- target chart.
  rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
  congr 1
  ext r
  -- The localization chart map agrees with the original quotient map on elements from `R / ξ`.
  change (algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a * b)))
      (((quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ).comp
          (Ideal.Quotient.mk ξ.asIdeal)) r) =
    (IsLocalization.Away.awayToAwayRight (fbar a) b)
      ((Localization.awayMap fbar a)
        ((algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a))
          ((Ideal.Quotient.mk ξ.asIdeal) r)))
  rw [quotient_map_of_comap_eq_comp_quotient_mk (f := f) (ξ := ξ) hηξ]
  calc
    (algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a * b)))
        (((Ideal.Quotient.mk η.asIdeal).comp f) r)
      = (algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a * b)))
          ((Ideal.Quotient.mk η.asIdeal) (f r)) := by
          rfl
    _ = (IsLocalization.Away.awayToAwayRight (fbar a) b)
          (algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a))
            (((Ideal.Quotient.mk η.asIdeal).comp f) r)) := by
          simpa using
            (IsLocalization.Away.awayToAwayRight_eq
              (S := Localization.Away (fbar a))
              (P := Localization.Away (fbar a * b))
              (x := fbar a) (y := b) (((Ideal.Quotient.mk η.asIdeal).comp f) r)).symm
    _ = (IsLocalization.Away.awayToAwayRight (fbar a) b)
          (algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a))
            (fbar ((Ideal.Quotient.mk ξ.asIdeal) r))) := by
          exact congrArg
            (fun z : S ⧸ η.asIdeal =>
              (IsLocalization.Away.awayToAwayRight (fbar a) b)
                (algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a)) z))
            (show ((Ideal.Quotient.mk η.asIdeal).comp f) r =
                fbar ((Ideal.Quotient.mk ξ.asIdeal) r) by
              rw [← quotient_map_of_comap_eq_comp_quotient_mk
                (f := f) (ξ := ξ) hηξ]
              rfl)
    _ = (IsLocalization.Away.awayToAwayRight (fbar a) b)
          ((Localization.awayMap fbar a)
            ((algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a))
              ((Ideal.Quotient.mk ξ.asIdeal) r))) := by
          congr 1
          symm
          simpa [Localization.awayMap] using
            (IsLocalization.map_eq
              (S := Localization.Away a)
              (Q := Localization.Away (fbar a))
              (g := fbar)
              (hy := by
                rintro x ⟨n, rfl⟩
                exact ⟨n, by simp⟩)
              ((Ideal.Quotient.mk ξ.asIdeal) r))

/-- Helper for Lemma 10.30.2: a witness in the localized chart image descends to the trace of the
quotient-image set on the basic open `D(a)`. -/
lemma localized_chart_homeomorph_pointwise_to_basicOpen_trace
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {a : R ⧸ ξ.asIdeal} {b : S ⧸ η.asIdeal}
    {xloc : PrimeSpectrum (Localization.Away a)}
    (hxloc :
      let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
      let g : Localization.Away a →+* Localization.Away ((fbar a) * b) :=
        ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
          (Localization.awayMap fbar a))
      let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
        PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
      let Eloc : Set (PrimeSpectrum (Localization.Away ((fbar a) * b))) :=
        PrimeSpectrum.comap
          (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη
      xloc ∈ PrimeSpectrum.comap g '' Eloc) :
    let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
    let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
      PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
    let e : PrimeSpectrum (Localization.Away a) ≃ₜ PrimeSpectrum.basicOpen a :=
      primeSpectrum_localizationAway_homeomorph_D a
    e xloc ∈
      ((Subtype.val : PrimeSpectrum.basicOpen a → PrimeSpectrum (R ⧸ ξ.asIdeal)) ⁻¹'
        (PrimeSpectrum.comap fbar '' Eη)) := by
  intro fbar Eη e
  -- Rewrite the target point through the canonical localization-basic-open homeomorphism and then
  -- apply the already established localized-chart pointwise transport.
  change (e xloc).1 ∈ PrimeSpectrum.comap fbar '' Eη
  have hxquotient :
      PrimeSpectrum.comap (algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a)) xloc ∈
        PrimeSpectrum.comap fbar '' Eη := by
    simpa using
      localized_chart_pointwise_to_quotient_image
        (f := f) (E := E) (ξ := ξ) (η := η) (a := a) (b := b) (xloc := xloc) hηξ hxloc
  simpa [e, primeSpectrum_localizationAway_homeomorph_D_apply] using hxquotient

/-- Helper for Lemma 10.30.2: transporting a dense open subset of the localized chart across the
homeomorphism `Spec((R / ξ)_a) ≃ D(a)` yields a dense open subset of `D(a)` inside the quotient
trace. -/
lemma localized_chart_dense_open_in_basicOpen_trace
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {a : R ⧸ ξ.asIdeal} {b : S ⧸ η.asIdeal}
    {Wloc : Opens (PrimeSpectrum (Localization.Away a))}
    (hWloc_dense : Dense (Wloc : Set (PrimeSpectrum (Localization.Away a))))
    (hWloc_subset :
      let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
      let g : Localization.Away a →+* Localization.Away ((fbar a) * b) :=
        ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
          (Localization.awayMap fbar a))
      let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
        PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
      let Eloc : Set (PrimeSpectrum (Localization.Away ((fbar a) * b))) :=
        PrimeSpectrum.comap
          (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη
      (Wloc : Set (PrimeSpectrum (Localization.Away a))) ⊆ PrimeSpectrum.comap g '' Eloc) :
    let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
    let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
      PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
    ∃ Wd : Opens (PrimeSpectrum.basicOpen a),
      Dense (Wd : Set (PrimeSpectrum.basicOpen a)) ∧
        (Wd : Set (PrimeSpectrum.basicOpen a)) ⊆
          ((Subtype.val : PrimeSpectrum.basicOpen a → PrimeSpectrum (R ⧸ ξ.asIdeal)) ⁻¹'
            (PrimeSpectrum.comap fbar '' Eη)) := by
  intro fbar Eη
  let e : PrimeSpectrum (Localization.Away a) ≃ₜ PrimeSpectrum.basicOpen a :=
    primeSpectrum_localizationAway_homeomorph_D a
  let Wd : Opens (PrimeSpectrum.basicOpen a) :=
    ⟨e '' (Wloc : Set (PrimeSpectrum (Localization.Away a))), e.isOpenMap _ Wloc.2⟩
  have hWd_dense : Dense (Wd : Set (PrimeSpectrum.basicOpen a)) := by
    have hpre :
        e.symm ⁻¹' (Wloc : Set (PrimeSpectrum (Localization.Away a))) =
          (Wd : Set (PrimeSpectrum.basicOpen a)) := by
      ext z
      constructor
      · intro hz
        exact ⟨e.symm z, hz, by simp [e]⟩
      · rintro ⟨w, hw, rfl⟩
        simpa [e] using hw
    -- Density is preserved across the localization-basic-open homeomorphism.
    rw [← hpre]
    exact Dense.preimage hWloc_dense e.symm.isOpenMap
  have hWd_subset :
      (Wd : Set (PrimeSpectrum.basicOpen a)) ⊆
        ((Subtype.val : PrimeSpectrum.basicOpen a → PrimeSpectrum (R ⧸ ξ.asIdeal)) ⁻¹'
          (PrimeSpectrum.comap fbar '' Eη)) := by
    intro x hx
    rcases hx with ⟨xloc, hxlocW, rfl⟩
    -- The pointwise adapter turns every localized witness into a witness on `D(a)`.
    exact localized_chart_homeomorph_pointwise_to_basicOpen_trace
      (f := f) (E := E) (ξ := ξ) (η := η) (a := a) (b := b) (xloc := xloc) hηξ
      (hWloc_subset hxlocW)
  exact ⟨Wd, hWd_dense, hWd_subset⟩

/-- Helper for Lemma 10.30.2: a dense open subset of the basic open `D(a)` inside the quotient
trace extends to a dense open subset of the whole quotient spectrum inside the same image. -/
lemma basicOpen_trace_open_dense_to_quotient_image
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {a : R ⧸ ξ.asIdeal} (ha : a ≠ 0)
    {Wd : Opens (PrimeSpectrum.basicOpen a)}
    (hWd_dense : Dense (Wd : Set (PrimeSpectrum.basicOpen a)))
    (hWd_subset :
      let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
      let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
        PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
      (Wd : Set (PrimeSpectrum.basicOpen a)) ⊆
        ((Subtype.val : PrimeSpectrum.basicOpen a → PrimeSpectrum (R ⧸ ξ.asIdeal)) ⁻¹'
          (PrimeSpectrum.comap fbar '' Eη))) :
    let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
    let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
      PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
    ∃ W : Opens (PrimeSpectrum (R ⧸ ξ.asIdeal)),
      Dense (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) ∧
        (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) ⊆
          PrimeSpectrum.comap fbar '' Eη := by
  intro fbar Eη
  have hU_open :
      IsOpen (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) :=
    PrimeSpectrum.isOpen_basicOpen
  have hU_dense :
      Dense (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) :=
    basicOpen_dense_of_nonzero_of_isDomain a ha
  obtain ⟨W, hW_dense, hW_subset_basic, hW_preimage⟩ :=
    image_open_dense_of_dense_open_subspace
      (U := (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))))
      hU_open hU_dense Wd.2 hWd_dense
  refine ⟨W, hW_dense, ?_⟩
  intro x hxW
  have hxU : x ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) :=
    hW_subset_basic hxW
  have hxPre :
      (⟨x, hxU⟩ : PrimeSpectrum.basicOpen a) ∈
        ((Subtype.val : PrimeSpectrum.basicOpen a → PrimeSpectrum (R ⧸ ξ.asIdeal)) ⁻¹'
          (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal)))) := by
    simpa using hxW
  have hxWd : (⟨x, hxU⟩ : PrimeSpectrum.basicOpen a) ∈ (Wd : Set (PrimeSpectrum.basicOpen a)) := by
    change (⟨x, hxU⟩ : PrimeSpectrum.basicOpen a) ∈ Wd.carrier
    exact hW_preimage ▸ hxPre
  -- Returning from the dense basic-open chart does not change the image witness.
  simpa using hWd_subset hxWd

/-- Helper for Lemma 10.30.2: a quotient-spectrum witness in the descended image maps to the
trace of `comap f '' E` on `closure {ξ}` under the quotient-spectrum homeomorphism. -/
lemma quotient_homeomorph_trace_pointwise
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {w : PrimeSpectrum (R ⧸ ξ.asIdeal)} {y : PrimeSpectrum (S ⧸ η.asIdeal)}
    (hy :
      y ∈ PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E)
    (hw :
      PrimeSpectrum.comap (quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ) y = w) :
    let e : PrimeSpectrum (R ⧸ ξ.asIdeal) ≃ₜ Zξ :=
      (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus ξ.asIdeal).trans
        (Homeomorph.setCongr <| (PrimeSpectrum.closure_singleton ξ).symm)
    e w ∈ traceOnClosure := by
  intro e
  change ((e w : Zξ) : PrimeSpectrum R) ∈ PrimeSpectrum.comap f '' E
  refine ⟨PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) y, hy, ?_⟩
  -- Rewrite the witness through the descended quotient map, then identify the quotient-spectrum
  -- point with its image in `closure {ξ}`.
  change PrimeSpectrum.comap f (PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) y) =
    ((e w : Zξ) : PrimeSpectrum R)
  rw [← PrimeSpectrum.comap_comp_apply]
  rw [← quotient_map_of_comap_eq_comp_quotient_mk (f := f) (ξ := ξ) hηξ]
  rw [PrimeSpectrum.comap_comp_apply, hw]
  change PrimeSpectrum.comap (Ideal.Quotient.mk ξ.asIdeal) w =
    ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus ξ.asIdeal w :
      V((ξ.asIdeal : Set R))) : PrimeSpectrum R)
  simpa using
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply ξ.asIdeal w).symm

/-- Helper for Lemma 10.30.2: a dense open subset of `Spec(R / ξ)` contained in the quotient
image transports to a dense open subset of `closure {ξ}` contained in the original trace. -/
lemma closure_open_dense_of_quotient_image_subset
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {W : Opens (PrimeSpectrum (R ⧸ ξ.asIdeal))}
    (hW_dense : Dense (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))))
    (hW_subset :
      (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) ⊆
        PrimeSpectrum.comap (quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ) ''
          (PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E)) :
    ∃ U : Opens Zξ, Dense (U : Set Zξ) ∧ (U : Set Zξ) ⊆ traceOnClosure := by
  let e : PrimeSpectrum (R ⧸ ξ.asIdeal) ≃ₜ Zξ :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus ξ.asIdeal).trans
      (Homeomorph.setCongr <| (PrimeSpectrum.closure_singleton ξ).symm)
  let U : Opens Zξ := ⟨e '' (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))), e.isOpenMap _ W.2⟩
  have hU_dense : Dense (U : Set Zξ) := by
    have hpre : e.symm ⁻¹' (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) = (U : Set Zξ) := by
      ext z
      constructor
      · intro hz
        exact ⟨e.symm z, hz, by simp⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    -- A homeomorphism preserves density by turning the target set into a preimage.
    simpa [hpre] using Dense.preimage hW_dense e.symm.isOpenMap
  refine ⟨U, hU_dense, ?_⟩
  intro z hz
  rcases hz with ⟨w, hwW, rfl⟩
  rcases hW_subset hwW with ⟨y, hy, hw⟩
  -- The quotient-spectrum witness `y` already lands in the original trace after transporting the
  -- target point across the quotient homeomorphism.
  simpa [e] using
    quotient_homeomorph_trace_pointwise (f := f) (E := E) (ξ := ξ) hηξ hy hw

-- Proof sketch: replace `Spec R` by the irreducible closed subset `closure {ξ}` and the source by
-- the closure of a point of `E` above `ξ`, so that `ξ` becomes a generic point. Lemma `10.30.1`
-- gives dense opens on which the finite type map is finitely presented, Chevalley's theorem makes
-- the corresponding image constructible, and the generic-point criterion for constructible subsets
-- then yields an open dense subset of `closure {ξ}` contained in the image.
/-- Lemma 10.30.2: for a finite type ring map `f : R →+* S` and a constructible subset
`E ⊆ Spec(S)`, if `ξ ∈ Spec(R)` lies in the image of `E` under `Spec(S) → Spec(R)`, then the
trace of that image on `closure {ξ}` contains an open dense subset of `closure {ξ}`. -/
@[stacks 00FH]
lemma exists_open_dense_subset_closure_singleton_of_mem_comap_image_constructible
    (f : R →+* S) (hf : f.FiniteType) (hE : IsConstructible E) (hξ : ξ ∈ comap f '' E) :
    ∃ U : Opens Zξ,
      Dense (U : Set Zξ) ∧
        (U : Set Zξ) ⊆
          ((Subtype.val : Zξ → PrimeSpectrum R) ⁻¹' (PrimeSpectrum.comap f '' E)) := by
  let f₀ : R →+* S := f
  rcases hξ with ⟨η, hηE, hηξ⟩
  letI : IsDomain (R ⧸ ξ.asIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime (I := ξ.asIdeal)).2 ξ.isPrime
  letI : IsDomain (S ⧸ η.asIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime (I := η.asIdeal)).2 η.isPrime
  let fbar := quotient_map_of_comap_eq (f := f₀) (ξ := ξ) hηξ
  let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
    PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
  have hquotientLoc :=
    quotient_localization_data_of_comap_eq (f := f₀) (ξ := ξ) hf hηξ
  have hquotientE :=
    quotient_preimage_constructible_generic_mem (E := E) hE hηE
  rcases hquotientLoc with ⟨a, ha, b, hb, hfp⟩
  let g :
      Localization.Away a →+* Localization.Away ((fbar a) * b) :=
    ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
      (Localization.awayMap fbar a))
  let Eloc : Set (PrimeSpectrum (Localization.Away ((fbar a) * b))) :=
    PrimeSpectrum.comap
        (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη
  have hquotientTarget :
      ∃ W : Opens (PrimeSpectrum (R ⧸ ξ.asIdeal)),
        Dense (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) ∧
          (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) ⊆
            PrimeSpectrum.comap fbar '' Eη := by
    have hfbar_inj : Function.Injective fbar :=
      quotient_map_of_comap_eq_injective (f := f₀) (ξ := ξ) hηξ
    have hfa : fbar a ≠ 0 := by
      -- The localized chart has to stay away from a nonzero element of the quotient domain.
      intro hzero
      exact ha (hfbar_inj <| by simpa using hzero)
    have hab : (fbar a) * b ≠ 0 := mul_ne_zero hfa hb
    letI : IsDomain (Localization.Away a) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away a)
        (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
    letI : IsDomain (Localization.Away ((fbar a) * b)) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors
        (Localization.Away ((fbar a) * b))
        (powers_le_nonZeroDivisors_of_noZeroDivisors hab)
    have hEloc :
        IsConstructible Eloc ∧
          (⟨⊥, Ideal.isPrime_bot⟩ :
              PrimeSpectrum (Localization.Away ((fbar a) * b))) ∈ Eloc := by
      have hEloc' :=
        localized_preimage_constructible_generic_mem
          (B := S ⧸ η.asIdeal) (c := (fbar a) * b) (C := Eη) hab hquotientE.1 hquotientE.2
      -- Pull the quotient constructible set containing the generic point to the localized chart.
      change IsConstructible
          (PrimeSpectrum.comap
            (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη) ∧
            (⟨⊥, Ideal.isPrime_bot⟩ :
                PrimeSpectrum (Localization.Away ((fbar a) * b))) ∈
              PrimeSpectrum.comap
                (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη
      exact hEloc'
    have hImageConstructible :
        IsConstructible (PrimeSpectrum.comap g '' Eloc) := by
      -- Chevalley on the finite-presentation localized chart gives constructibility of its image.
      simpa [g] using PrimeSpectrum.isConstructible_comap_image hfp hEloc.1
    have hgenericImage :
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.Away a)) ∈
          PrimeSpectrum.comap g '' Eloc := by
      -- The localized generic point of `Eloc` contracts to the generic point of `Spec((R / ξ)_a)`.
      refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ :
        PrimeSpectrum (Localization.Away ((fbar a) * b))), hEloc.2, ?_⟩
      apply PrimeSpectrum.ext
      exact localized_chart_comap_bot_eq_bot
        (f := f₀) (ξ := ξ) hηξ ha hb
    obtain ⟨Wloc, hWloc_dense, hWloc_subset⟩ :=
      exists_open_dense_subset_of_constructible_generic_mem hImageConstructible hgenericImage
    obtain ⟨Wd, hWd_dense, hWd_subset⟩ :=
      localized_chart_dense_open_in_basicOpen_trace
        (f := f₀) (E := E) (ξ := ξ) (η := η) (a := a) (b := b) hηξ hWloc_dense hWloc_subset
    -- Transport the localized dense open to `D(a)`, then extend it to the whole quotient
    -- spectrum using that `D(a)` is dense because `a ≠ 0`.
    exact basicOpen_trace_open_dense_to_quotient_image
      (f := f₀) (E := E) (ξ := ξ) (η := η) (a := a) hηξ ha hWd_dense hWd_subset
  -- Route correction: the direct Chevalley route stops here because mathlib only gives
  -- constructibility of `comap f '' E` for finite-presentation maps. The source-proof reduction
  -- must therefore pass to quotient domains at `ξ` and `η`, use Lemma `10.30.1` on the localized
  -- chart `g : Spec(S_(fbar(a)b)) → Spec(R_a)`, produce `hquotientTarget`, and only then return
  -- from `Spec(R / ξ)` to `closure {ξ}` via
  -- `closure_open_dense_of_quotient_image_subset`, which is now proved above.
  rcases hquotientTarget with ⟨W, hW_dense, hW_subset⟩
  have hfinal :
      ∃ U : Opens Zξ,
        Dense (U : Set Zξ) ∧
          (U : Set Zξ) ⊆
            ((Subtype.val : Zξ → PrimeSpectrum R) ⁻¹' (PrimeSpectrum.comap f₀ '' E)) := by
    -- The quotient-spectrum dense open returns to `closure {ξ}` through the canonical
    -- homeomorphism and lands in the explicit theorem-local trace set.
    simpa [f₀] using
      closure_open_dense_of_quotient_image_subset
        (f := f₀) (E := E) (ξ := ξ) hηξ hW_dense hW_subset
  simpa [f₀] using hfinal

end
