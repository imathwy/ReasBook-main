import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_103_6 (from Chap10) -/
open IsLocalRing RingTheory Sequence
open scoped ENat

universe u v w

section

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

namespace Module

/-
Source/core/bridge triage:
* source-facing: `cohenMacaulay_iff_restrictScalars_of_surjective`, the textbook invariance of the
  Cohen-Macaulay condition under a surjective local map;
* core/canonical: the owner class `Module.CohenMacaulay`;
* bridge/view: `Module.CohenMacaulay.of_surjective`, the forward transport used when the owner
  instance over `S` is already available.

Primitive data are the surjective algebra map and the owner class itself. Finiteness over `R`
belongs to the derived API, obtained canonically from finiteness over `S` by restricting scalars,
rather than being packaged as separate primitive data in this file.
-/

/-- Helper for Lemma 10.103.6: mapping a regular sequence along `algebraMap R S` does not change
its regularity on `N`. -/
private theorem isRegular_map_algebraMap_iff (rs : List R) :
    IsRegular N (rs.map (algebraMap R S)) ↔ IsRegular N rs := by
  -- The additive identity on `N` intertwines the two scalar actions via `algebraMap`.
  exact
    (AddEquiv.refl N).isRegular_congr <|
      List.forall₂_map_left_iff.mpr <|
        List.forall₂_same.mpr fun r _ => algebraMap_smul S r

/-- Helper for Lemma 10.103.6: a list of elements of `maximalIdeal S` lifts to a list of elements
of `maximalIdeal R` with the same image under `algebraMap R S`. -/
private theorem exists_preimage_list_in_maximalIdeal
    (hsurj : Function.Surjective (algebraMap R S)) (rs : List S)
    (hI : Ideal.ofList rs ≤ maximalIdeal S) :
    ∃ rs' : List R,
      rs'.map (algebraMap R S) = rs ∧ Ideal.ofList rs' ≤ maximalIdeal R := by
  have hmap :
      Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) hsurj
  induction rs with
  | nil =>
      have hnil : Ideal.ofList ([] : List R) ≤ maximalIdeal R := by
        simpa using (bot_le : (⊥ : Ideal R) ≤ maximalIdeal R)
      exact ⟨[], rfl, hnil⟩
  | cons s rs ih =>
      have hs_mem : s ∈ maximalIdeal S := by
        apply hI
        exact Ideal.subset_span (by simp)
      have hs_map : s ∈ Ideal.map (algebraMap R S) (maximalIdeal R) := by
        simpa [hmap] using hs_mem
      rcases (Ideal.mem_map_iff_of_surjective (f := algebraMap R S) hsurj).1 hs_map with
        ⟨r, hr, hrs⟩
      have htail_aux : Ideal.ofList rs ≤ Ideal.ofList (s :: rs) := by
        rw [Ideal.ofList_cons]
        exact le_sup_of_le_right le_rfl
      have htail : Ideal.ofList rs ≤ maximalIdeal S := by
        exact htail_aux.trans hI
      rcases ih htail with ⟨rs', hrs', hI'⟩
      have hr_le : Ideal.span ({r} : Set R) ≤ maximalIdeal R := by
        refine Ideal.span_le.mpr ?_
        intro x hx
        simp at hx
        simpa [hx] using hr
      have hcons : Ideal.ofList (r :: rs') ≤ maximalIdeal R := by
        rw [Ideal.ofList_cons]
        exact sup_le hr_le hI'
      exact ⟨r :: rs', by simp [hrs, hrs'], hcons⟩

/-- Helper for Lemma 10.103.6: the support dimension of `N` is unchanged after restricting scalars
along a surjective map `R → S`. -/
private theorem supportDim_eq_of_surjective
    (hsurj : Function.Surjective (algebraMap R S)) [Module.Finite R N] [Module.Finite S N] :
    Module.supportDim R N = Module.supportDim S N := by
  have hann :
      Ideal.comap (algebraMap R S) (Module.annihilator S N) = Module.annihilator R N :=
    Module.comap_annihilator (R₀ := R) (R := S) (M := N)
  have hann_le :
      Module.annihilator R N ≤ Ideal.comap (algebraMap R S) (Module.annihilator S N) :=
    hann.symm.le
  have hann_ge :
      Ideal.comap (algebraMap R S) (Module.annihilator S N) ≤ Module.annihilator R N :=
    hann.le
  let φ : R ⧸ Module.annihilator R N →+* S ⧸ Module.annihilator S N :=
    Ideal.quotientMap (Module.annihilator S N) (algebraMap R S) hann_le
  have hφinj : Function.Injective φ :=
    Ideal.quotientMap_injective' hann_ge
  have hφsurj : Function.Surjective φ :=
    Ideal.quotientMap_surjective hsurj
  have hφbij : Function.Bijective φ := ⟨hφinj, hφsurj⟩
  let e : R ⧸ Module.annihilator R N ≃+* S ⧸ Module.annihilator S N :=
    RingEquiv.ofBijective φ hφbij
  -- Compare both support dimensions through the quotient-annihilator presentation.
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    ringKrullDim_eq_of_ringEquiv e]

/-- Helper for Lemma 10.103.6: the lengths of regular sequences in the maximal ideals of `R` and
`S` coincide on `N` under a surjective local map `R → S`. -/
private theorem regularSequenceLengths_maximalIdeal_eq_of_surjective
    (hsurj : Function.Surjective (algebraMap R S)) :
    Ideal.regularSequenceLengths (maximalIdeal R) N =
      Ideal.regularSequenceLengths (maximalIdeal S) N := by
  have hmap :
      Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) hsurj
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    have hreg' : IsRegular N (rs.map (algebraMap R S)) :=
      (isRegular_map_algebraMap_iff (R := R) (S := S) (N := N) rs).2 hreg
    have hI' : Ideal.ofList (rs.map (algebraMap R S)) ≤ maximalIdeal S := by
      simpa [Ideal.map_ofList, hmap] using Ideal.map_mono (f := algebraMap R S) hI
    have hlen : (rs.length : ℕ∞) = (rs.map (algebraMap R S)).length := by
      simp
    exact ⟨rs.map (algebraMap R S), hreg', hI', hlen⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    rcases exists_preimage_list_in_maximalIdeal (R := R) (S := S) hsurj rs hI with
      ⟨rs', hrs', hI'⟩
    have hreg_map : IsRegular N (rs'.map (algebraMap R S)) := by
      simpa [hrs'] using hreg
    have hreg' : IsRegular N rs' :=
      (isRegular_map_algebraMap_iff (R := R) (S := S) (N := N) rs').1 hreg_map
    have hlen_nat : rs'.length = rs.length := by
      simpa using congrArg List.length hrs'
    have hlen : (rs'.length : ℕ∞) = rs.length :=
      congrArg (fun n : ℕ => (n : ℕ∞)) hlen_nat
    exact ⟨rs', hreg', hI', hlen.symm⟩

/-- Helper for Lemma 10.103.6: the module depth of `N` is unchanged after restricting scalars
along a surjective map `R → S`. -/
private theorem moduleDepth_eq_of_surjective
    (hsurj : Function.Surjective (algebraMap R S)) [Module.Finite R N] [Module.Finite S N] :
    moduleDepth R N = moduleDepth S N := by
  have hmap :
      Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap R S) hsurj
  have hsmul :
      (maximalIdeal S • (⊤ : Submodule S N)).restrictScalars R =
        maximalIdeal R • (⊤ : Submodule R N) := by
    simpa [hmap] using
      (Ideal.smul_restrictScalars (R := R) (S := S) (M := N) (maximalIdeal R)
        (⊤ : Submodule S N))
  have htop :
      maximalIdeal R • (⊤ : Submodule R N) = ⊤ ↔
        maximalIdeal S • (⊤ : Submodule S N) = ⊤ := by
    constructor
    · intro hR
      have hR' : (maximalIdeal S • (⊤ : Submodule S N)).restrictScalars R = ⊤ := by
        rw [hsmul, hR]
      exact
        (Submodule.restrictScalars_eq_top_iff (S := R)
          (p := maximalIdeal S • (⊤ : Submodule S N))).mp hR'
    · intro hS
      have hS' :
          (maximalIdeal S • (⊤ : Submodule S N)).restrictScalars R = ⊤ := by
        rw [hS, Submodule.restrictScalars_top]
      simpa [hsmul] using hS'
  by_cases hR : maximalIdeal R • (⊤ : Submodule R N) = ⊤
  · have hS : maximalIdeal S • (⊤ : Submodule S N) = ⊤ := htop.mp hR
    rw [show moduleDepth R N = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal R) N hR,
      show moduleDepth S N = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal S) N hS]
  · have hS : maximalIdeal S • (⊤ : Submodule S N) ≠ ⊤ := mt htop.mpr hR
    rw [show moduleDepth R N = sSup (Ideal.regularSequenceLengths (maximalIdeal R) N) from
        Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) N hR,
      show moduleDepth S N = sSup (Ideal.regularSequenceLengths (maximalIdeal S) N) from
        Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal S) N hS,
      regularSequenceLengths_maximalIdeal_eq_of_surjective (R := R) (S := S) (N := N) hsurj]

-- Proof sketch: identify `S` with a quotient of `R` using surjectivity of `algebraMap R S`.
-- Under restriction of scalars, the maximal ideal of `S` is the image of the maximal ideal of
-- `R`, and both the depth and the support dimension of `N` are unchanged by passage to this
-- quotient presentation. Therefore the defining equality for Cohen-Macaulay modules is equivalent
-- over `S` and over `R`.
/-- Lemma 10.103.6: for a surjective homomorphism `R → S` of Noetherian local rings and a finite
`S`-module `N`, the module `N` is Cohen-Macaulay over `S` if and only if it is
Cohen-Macaulay over `R` via restriction of scalars. -/
theorem cohenMacaulay_iff_restrictScalars_of_surjective
    (hsurj : Function.Surjective (algebraMap R S)) :
    CohenMacaulay S N ↔ CohenMacaulay R N := by
  constructor
  · intro hS
    let _ : CohenMacaulay S N := hS
    let _ : Module.Finite R S := Module.Finite.of_surjective (Algebra.linearMap R S) hsurj
    let _ : Module.Finite R N := Module.Finite.trans S N
    -- Transport the defining equality through the support-dimension and depth comparisons.
    have hdepthDim :
        Module.supportDim R N = WithBot.some (moduleDepth R N) := by
      rw [supportDim_eq_of_surjective (R := R) (S := S) (N := N) hsurj,
        moduleDepth_eq_of_surjective (R := R) (S := S) (N := N) hsurj,
        hS.supportDim_eq_moduleDepth]
    exact ⟨hdepthDim⟩
  · intro hR
    let _ : CohenMacaulay R N := hR
    let _ : Module.Finite S N := Module.Finite.of_restrictScalars_finite R S N
    -- The same invariance lemmas rewrite the `R`-equality back to the `S`-equality.
    have hdepthDim :
        Module.supportDim S N = WithBot.some (moduleDepth S N) := by
      rw [← supportDim_eq_of_surjective (R := R) (S := S) (N := N) hsurj,
        ← moduleDepth_eq_of_surjective (R := R) (S := S) (N := N) hsurj,
        hR.supportDim_eq_moduleDepth]
    exact ⟨hdepthDim⟩

namespace CohenMacaulay

/-- Restricting scalars along a surjective local ring map preserves the Cohen-Macaulay property. -/
theorem of_surjective (hsurj : Function.Surjective (algebraMap R S)) [CohenMacaulay S N] :
    CohenMacaulay R N :=
  (cohenMacaulay_iff_restrictScalars_of_surjective hsurj).1 ‹_›

end CohenMacaulay

end Module

end

/-! ### Lemma_10_103_7 (from Chap10) -/
universe u v

open PrimeSpectrum

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]

/- Domain-style sampling:
* primary domain: Cohen-Macaulay modules, support dimension, and associated primes over
  Noetherian local rings;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.CohenMacaulay.supportDim_eq_moduleDepth`,
  `moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes`,
  `minimal_support_iff_minimal_associatedPrimes`;
* best owner abstraction: the chapter owner class `Module.CohenMacaulay`;
* primitive data: the ambient local Noetherian ring, the module structure on `M`, and the owner
  instance `[Module.CohenMacaulay R M]`;
* derived API: the equality `Module.supportDim R M = .some (moduleDepth R M)` and the inherited
  finiteness instance.

Source/core/bridge triage:
* `source-facing`: the two consequences for associated primes of a Cohen-Macaulay module;
* `core/canonical`: `Module.CohenMacaulay`, `Module.support`, `Module.supportDim`,
  `associatedPrimes`, and `ringKrullDim`;
* `bridge/view`: passing between support-minimal prime points and minimal associated ideals.
-/

-- Proof sketch: apply Lemma `10.72.9` to get
-- `.some (moduleDepth R M) ≤ ringKrullDim (R ⧸ 𝔭.asIdeal)`, use the Cohen-Macaulay identity
-- `Module.CohenMacaulay.supportDim_eq_moduleDepth`, and
-- combine this with the general inequality `ringKrullDim (R ⧸ 𝔭.asIdeal) ≤ Module.supportDim R M`
-- coming from `𝔭 ∈ Module.support R M`. Equality of dimensions forces `𝔭` to be minimal in the
-- support.
omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.103.7: the zero locus of a prime ideal is the upper interval above the
corresponding point of `Spec R`. -/
private lemma primeSpectrum_zeroLocus_prime_eq_Ici (𝔭 : PrimeSpectrum R) :
    PrimeSpectrum.zeroLocus (R := R) 𝔭.asIdeal = Set.Ici 𝔭 := by
  -- Both descriptions say exactly that the given prime contains `𝔭.asIdeal`.
  ext 𝔮
  change 𝔭.asIdeal ≤ 𝔮.asIdeal ↔ 𝔭 ≤ 𝔮
  rfl

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.103.7: support membership bounds the Krull dimension of the corresponding
prime quotient by the support dimension of the module. -/
private theorem ringKrullDim_quotient_le_supportDim_of_mem_support
    (𝔮 : PrimeSpectrum R) (h𝔮 : 𝔮 ∈ Module.support R M) :
    ringKrullDim (R ⧸ 𝔮.asIdeal) ≤ Module.supportDim R M := by
  -- The quotient by `𝔮` is a further quotient of `R / Ann(M)`, so its dimension can only drop.
  have hann_le : Module.annihilator R M ≤ 𝔮.asIdeal :=
    Module.annihilator_le_of_mem_support h𝔮
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R) (M := M)]
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hann_le)
    (Ideal.Quotient.factor_surjective hann_le)

/-- Helper for Lemma 10.103.7: an associated prime of a Cohen-Macaulay module has quotient ring
dimension equal to the support dimension. -/
private theorem ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
    (𝔭 : PrimeSpectrum R) (h𝔭 : 𝔭.asIdeal ∈ associatedPrimes R M) :
    ringKrullDim (R ⧸ 𝔭.asIdeal) = Module.supportDim R M := by
  -- The source proof is the depth sandwich `depth(M) ≤ dim(R/𝔭) ≤ dim(Supp M)`.
  have hlower :
      ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ 𝔭.asIdeal) :=
    moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (R := R) (M := M) 𝔭.asIdeal h𝔭
  have hlower' : Module.supportDim R M ≤ ringKrullDim (R ⧸ 𝔭.asIdeal) := by
    simpa [Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M)] using hlower
  have h𝔭_support : 𝔭 ∈ Module.support R M :=
    Module.associatedPrimes_subset_support (R := R) (M := M) (by simpa using h𝔭)
  have hup : ringKrullDim (R ⧸ 𝔭.asIdeal) ≤ Module.supportDim R M :=
    ringKrullDim_quotient_le_supportDim_of_mem_support (R := R) (M := M) 𝔭 h𝔭_support
  exact le_antisymm hup hlower'

/-- Helper for Lemma 10.103.7: quotient dimensions strictly decrease along a proper specialization
in `Spec R`. -/
private theorem ringKrullDim_quotient_lt_of_lt_primeSpectrum
    (𝔮 𝔭 : PrimeSpectrum R) (h𝔮𝔭 : 𝔮 < 𝔭) :
    ringKrullDim (R ⧸ 𝔭.asIdeal) < ringKrullDim (R ⧸ 𝔮.asIdeal) := by
  -- Rewrite both quotient dimensions as coheights and use the strict antitonicity of coheight.
  have hrw :
      ∀ 𝔯 : PrimeSpectrum R, ringKrullDim (R ⧸ 𝔯.asIdeal) = Order.coheight 𝔯 := by
    intro 𝔯
    rw [ringKrullDim_quotient, primeSpectrum_zeroLocus_prime_eq_Ici (R := R) 𝔯]
    exact (Order.coheight_eq_krullDim_Ici 𝔯).symm
  haveI : Nontrivial (R ⧸ 𝔭.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr 𝔭.isPrime.ne_top
  haveI : IsLocalRing (R ⧸ 𝔭.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔭.asIdeal) Ideal.Quotient.mk_surjective
  have h𝔭_fin : Order.coheight 𝔭 < ⊤ := by
    have hdim : ringKrullDim (R ⧸ 𝔭.asIdeal) < ⊤ := ringKrullDim_lt_top
    rw [hrw 𝔭] at hdim
    exact WithBot.coe_lt_coe.mp hdim
  rw [hrw 𝔭, hrw 𝔮]
  exact WithBot.coe_lt_coe.mpr (Order.coheight_strictAnti h𝔮𝔭 h𝔭_fin)

/-- Lemma 10.103.7: if `M` is a Cohen-Macaulay module over a Noetherian local ring and `𝔭` is an
associated prime of `M`, then the Krull dimension of `R / 𝔭` equals the dimension of the support
of `M`, and `𝔭` is minimal in `Module.support R M`. -/
theorem ringKrullDim_quotient_and_minimal_support_of_mem_associatedPrimes_of_cohenMacaulay
    (𝔭 : PrimeSpectrum R) (h𝔭 : 𝔭.asIdeal ∈ associatedPrimes R M) :
    ringKrullDim (R ⧸ 𝔭.asIdeal) = Module.supportDim R M ∧
      Minimal (· ∈ Module.support R M) 𝔭 := by
  have hdim :
      ringKrullDim (R ⧸ 𝔭.asIdeal) = Module.supportDim R M :=
    ringKrullDim_quotient_eq_supportDim_of_mem_associatedPrimes_of_cohenMacaulay
      (R := R) (M := M) 𝔭 h𝔭
  have h𝔭_support : 𝔭 ∈ Module.support R M :=
    Module.associatedPrimes_subset_support (R := R) (M := M) (by simpa using h𝔭)
  refine ⟨hdim, ?_⟩
  refine ⟨h𝔭_support, ?_⟩
  intro 𝔮 h𝔮 h𝔮𝔭
  -- If a smaller support point existed, strict dimension drop would contradict the equality above.
  by_contra hnot
  have h𝔮_ne : 𝔮 ≠ 𝔭 := fun hEq ↦ hnot (hEq ▸ le_rfl)
  have h𝔮_lt_𝔭 : 𝔮 < 𝔭 := lt_of_le_of_ne h𝔮𝔭 h𝔮_ne
  have hlt :
      ringKrullDim (R ⧸ 𝔭.asIdeal) < ringKrullDim (R ⧸ 𝔮.asIdeal) :=
    ringKrullDim_quotient_lt_of_lt_primeSpectrum (R := R) 𝔮 𝔭 h𝔮_lt_𝔭
  have hq_le :
      ringKrullDim (R ⧸ 𝔮.asIdeal) ≤ Module.supportDim R M :=
    ringKrullDim_quotient_le_supportDim_of_mem_support (R := R) (M := M) 𝔮 h𝔮
  have hcontr : Module.supportDim R M < Module.supportDim R M := by
    calc
      Module.supportDim R M = ringKrullDim (R ⧸ 𝔭.asIdeal) := hdim.symm
      _ < ringKrullDim (R ⧸ 𝔮.asIdeal) := hlt
      _ ≤ Module.supportDim R M := hq_le
  exact (lt_irrefl (Module.supportDim R M)) hcontr

-- Proof sketch: apply the minimal-support conclusion of
-- `ringKrullDim_quotient_and_minimal_support_of_mem_associatedPrimes_of_cohenMacaulay` to the
-- prime point corresponding to `p`, then use Proposition `10.63.6` to pass from minimality in the
-- support to minimality among associated primes.
/-- If `M` is Cohen-Macaulay, then every associated prime of `M` is minimal among the associated
primes; equivalently, `M` has no embedded associated primes. -/
theorem minimal_mem_associatedPrimes_of_mem_associatedPrimes_of_cohenMacaulay
    (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    Minimal (· ∈ associatedPrimes R M) p := by
  let 𝔭 : PrimeSpectrum R := ⟨p, (AssociatedPrimes.mem_iff.mp hp).isPrime⟩
  have hmain :
      ringKrullDim (R ⧸ 𝔭.asIdeal) = Module.supportDim R M ∧
        Minimal (· ∈ Module.support R M) 𝔭 :=
    ringKrullDim_quotient_and_minimal_support_of_mem_associatedPrimes_of_cohenMacaulay
      (R := R) (M := M) 𝔭 (by simpa [𝔭] using hp)
  -- Proposition `10.63.6` converts minimal support points into minimal associated primes.
  simpa [𝔭] using
    (minimal_support_iff_minimal_associatedPrimes (R := R) (M := M) 𝔭).mp hmain.2

end

/-! ### Definition_10_103_8 (from Chap10) -/
universe u v

open IsLocalRing

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Module

/-
Source/core/bridge triage:
* source-facing: `Module.MaximalCohenMacaulay R M`, the local maximal Cohen-Macaulay condition;
* core/canonical: the owner class `Module.CohenMacaulay`;
* bridge/view: `MaximalCohenMacaulay.toCohenMacaulay` and the local depth notation
  `moduleDepth R M`.

Primitive data are exactly the finiteness assumption and the source-facing equality comparing the
local depth of `M` to `ringKrullDim R`. The Cohen-Macaulay owner condition is derived API and
should be recovered through a bridge theorem/instance rather than stored as primitive public data.
-/
/-- Definition 10.103.8: a finite `R`-module over a Noetherian local ring is maximal
Cohen-Macaulay when its depth equals the Krull dimension of `R`. Since `ringKrullDim` takes
values in `WithBot ℕ∞`, the depth is compared in the same codomain via the canonical coercion
`WithTop ℕ = ℕ∞ → WithBot ℕ∞`. -/
class MaximalCohenMacaulay : Prop extends Module.Finite R M where
  depth_eq_ringKrullDim : .some (moduleDepth R M) = ringKrullDim R

namespace MaximalCohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

theorem nontrivial (h : MaximalCohenMacaulay R M) : Nontrivial M := by
  by_contra hM
  letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
  have hsmul : maximalIdeal R • (⊤ : Submodule R M) = ⊤ := by
    simpa using (Subsingleton.elim (maximalIdeal R • (⊤ : Submodule R M)) ⊤)
  have hdepth_top : moduleDepth R M = ⊤ :=
    Ideal.depth_eq_top_of_smul_top (maximalIdeal R) M hsmul
  have hdim_top : ringKrullDim R = ⊤ := by
    simpa [hdepth_top] using h.depth_eq_ringKrullDim.symm
  exact ringKrullDim_ne_top hdim_top

/-- A maximal Cohen-Macaulay module has support dimension equal to the Krull dimension of the
base ring. -/
theorem supportDim_eq_ringKrullDim (h : MaximalCohenMacaulay R M) :
    Module.supportDim R M = ringKrullDim R := by
  letI : Module.Finite R M := h.toFinite
  letI : Nontrivial M := h.nontrivial
  apply le_antisymm
  · exact Module.supportDim_le_ringKrullDim R M
  · rw [← h.depth_eq_ringKrullDim]
    exact depth_le_supportDim

/-- A maximal Cohen-Macaulay module is Cohen-Macaulay. -/
theorem toCohenMacaulay (h : MaximalCohenMacaulay R M) : Module.CohenMacaulay R M :=
  letI : Module.Finite R M := h.toFinite
  Module.CohenMacaulay.mk <| by
    calc
      Module.supportDim R M = ringKrullDim R := supportDim_eq_ringKrullDim h
      _ = .some (moduleDepth R M) := h.depth_eq_ringKrullDim.symm

end MaximalCohenMacaulay

/-- The source-facing maximal Cohen-Macaulay condition implies the chapter owner condition. -/
instance cohenMacaulay_of_maximalCohenMacaulay [MaximalCohenMacaulay R M] :
    Module.CohenMacaulay R M :=
  ‹MaximalCohenMacaulay R M›.toCohenMacaulay

end Module

end

/-! ### Lemma_10_103_9 (from Chap10) -/
universe u v

open PrimeSpectrum

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.103.9: the zero locus of a prime ideal is the upper interval above the
corresponding point of `Spec R`. -/
private lemma primeSpectrum_zeroLocus_prime_eq_Ici (𝔭 : PrimeSpectrum R) :
    PrimeSpectrum.zeroLocus (R := R) 𝔭.asIdeal = Set.Ici 𝔭 := by
  -- Both descriptions say exactly that the given prime contains `𝔭.asIdeal`.
  ext 𝔮
  change 𝔭.asIdeal ≤ 𝔮.asIdeal ↔ 𝔭 ≤ 𝔮
  rfl

/-- Helper for Lemma 10.103.9: the Krull dimension of a Noetherian local ring is represented by a
natural number. -/
private lemma ringKrullDim_eq_nat_of_local_noetherian_ring :
    ∃ n : ℕ, ringKrullDim R = n := by
  -- Convert the finite-dimensional local Krull dimension into an actual natural number.
  have hbot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim R).unbot hbot).toNat
  have hneTop : (ringKrullDim R).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim' : ((ringKrullDim R).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
  refine ⟨n, ?_⟩
  calc
    ringKrullDim R = (ringKrullDim R).unbot hbot := by
      exact (WithBot.coe_unbot (ringKrullDim R) hbot).symm
    _ = n := hdim'

/-- Helper for Lemma 10.103.9: the head of a maximal prime chain is a minimal point of `Spec R`.
-/
private lemma head_isMin_of_isMaxChain (p : LTSeries (PrimeSpectrum R))
    (hp : IsMaxChain (· ≤ ·) (Set.range p)) :
    IsMin p.head := by
  rw [isMin_iff_forall_not_lt]
  intro q hq
  -- Inserting a smaller prime into the chain still gives a chain, contradicting maximality.
  have hchain : IsChain (· ≤ ·) (insert q (Set.range p)) := by
    refine hp.isChain.insert ?_
    intro x hx _
    rcases hx with ⟨i, rfl⟩
    exact Or.inl (hq.le.trans (p.monotone (Fin.zero_le i)))
  have hEq : insert q (Set.range p) = Set.range p :=
    (hp.2 hchain (Set.subset_insert _ _)).symm
  have hq_mem : q ∈ Set.range p := by
    rw [← hEq]
    simp
  rcases hq_mem with ⟨i, hi⟩
  have hhead_le_q : p.head ≤ q := by
    rw [← hi]
    exact p.monotone (Fin.zero_le i)
  exact hq.not_ge hhead_le_q

/-- Helper for Lemma 10.103.9: the last point of a maximal prime chain is a maximal point of
`Spec R`. -/
private lemma last_isMax_of_isMaxChain (p : LTSeries (PrimeSpectrum R))
    (hp : IsMaxChain (· ≤ ·) (Set.range p)) :
    IsMax p.last := by
  rw [isMax_iff_forall_not_lt]
  intro q hq
  -- Inserting a larger prime into the chain still gives a chain, contradicting maximality.
  have hchain : IsChain (· ≤ ·) (insert q (Set.range p)) := by
    refine hp.isChain.insert ?_
    intro x hx _
    rcases hx with ⟨i, rfl⟩
    exact Or.inr ((p.monotone (Fin.le_last i)).trans hq.le)
  have hEq : insert q (Set.range p) = Set.range p :=
    (hp.2 hchain (Set.subset_insert _ _)).symm
  have hq_mem : q ∈ Set.range p := by
    rw [← hEq]
    simp
  rcases hq_mem with ⟨i, hi⟩
  have hq_le_last : q ≤ p.last := by
    rw [← hi]
    exact p.monotone (Fin.le_last i)
  exact hq.not_ge hq_le_last

/-- Helper for Lemma 10.103.9: full support makes the head of a maximal prime chain an associated
prime of the Cohen-Macaulay module. -/
private lemma head_mem_associatedPrimes_of_full_support_cohenMacaulay
    (hCM : Module.CohenMacaulay R M) (hsupp : Module.support R M = Set.univ)
    (p : LTSeries (PrimeSpectrum R)) (hp : IsMaxChain (· ≤ ·) (Set.range p)) :
    p.head.asIdeal ∈ associatedPrimes R M := by
  let _ : Module.CohenMacaulay R M := hCM
  have hhead_min : IsMin p.head := head_isMin_of_isMaxChain p hp
  have hhead_min_support : Minimal (· ∈ Module.support R M) p.head := by
    refine ⟨?_, ?_⟩
    · simpa [hsupp]
    · intro q hq hqle
      exact hhead_min hqle
  -- Minimal support points are associated primes in the Noetherian setting.
  exact Module.minimal_support_mem_associatedPrimes p.head hhead_min_support

/-- Helper for Lemma 10.103.9: the coheight of the head of a maximal chain equals `dim R` under
the full-support Cohen-Macaulay hypothesis. -/
private lemma coheight_head_eq_ringKrullDim_of_full_support_cohenMacaulay
    (hCM : Module.CohenMacaulay R M) (hsupp : Module.support R M = Set.univ)
    (p : LTSeries (PrimeSpectrum R)) (hp : IsMaxChain (· ≤ ·) (Set.range p)) :
    Order.coheight p.head = ringKrullDim R := by
  let _ : Module.CohenMacaulay R M := hCM
  have hhead_assoc :
      p.head.asIdeal ∈ associatedPrimes R M :=
    head_mem_associatedPrimes_of_full_support_cohenMacaulay hCM hsupp p hp
  have hquot :
      ringKrullDim (R ⧸ p.head.asIdeal) = Module.supportDim R M :=
    (ringKrullDim_quotient_and_minimal_support_of_mem_associatedPrimes_of_cohenMacaulay
      (R := R) (M := M) p.head hhead_assoc).1
  have hsupportDim : Module.supportDim R M = ringKrullDim R := by
    have hsupport :
        Order.krullDim (Module.support R M) = Order.krullDim (PrimeSpectrum R) := by
      rw [hsupp]
      exact
        (Order.krullDim_eq_of_orderIso
          (OrderIso.Set.univ : (Set.univ : Set (PrimeSpectrum R)) ≃o PrimeSpectrum R))
    simpa [Module.supportDim, ringKrullDim] using hsupport
  -- Rewrite the quotient dimension as the Krull dimension of the upper interval over `p.head`.
  calc
    Order.coheight p.head = ringKrullDim (R ⧸ p.head.asIdeal) := by
      rw [ringKrullDim_quotient, primeSpectrum_zeroLocus_prime_eq_Ici (R := R) p.head]
      exact Order.coheight_eq_krullDim_Ici p.head
    _ = Module.supportDim R M := hquot
    _ = ringKrullDim R := hsupportDim

/-- Helper for Lemma 10.103.9: if the maximal chain has positive length, one can choose an element
of the second prime that avoids all minimal primes of `R`. -/
private lemma exists_mem_second_prime_avoiding_minimalPrimes
    (p : LTSeries (PrimeSpectrum R)) (hp : IsMaxChain (· ≤ ·) (Set.range p))
    (hlen : p.length ≠ 0) :
    ∃ x, x ∈ (p 1).asIdeal ∧ x ∈ IsLocalRing.maximalIdeal R ∧ ∀ q ∈ minimalPrimes R, x ∉ q := by
  have hhead_min : IsMin p.head := head_isMin_of_isMaxChain p hp
  let i1 : Fin (p.length + 1) := ⟨1, Nat.succ_lt_succ (Nat.pos_of_ne_zero hlen)⟩
  have hi1_lt : 1 < p.length + 1 := Nat.succ_lt_succ (Nat.pos_of_ne_zero hlen)
  have hi1 : i1 = 1 := by
    ext
    simp [i1, Nat.mod_eq_of_lt hi1_lt]
  have hhead_lt : p.head < p i1 := by
    have hstep := p.step ⟨0, Nat.pos_of_ne_zero hlen⟩
    simpa [i1, RelSeries.head] using hstep
  have hnot_subset :
      ¬ ((p i1).asIdeal : Set R) ⊆ ⋃ q ∈ minimalPrimes R, (q : Set R) := by
    intro hsubset
    obtain ⟨q, hq, hp1_le_q⟩ :=
      (((p i1).asIdeal).subset_union_prime_finite
        (minimalPrimes.finite_of_isNoetherianRing R) ((p i1).asIdeal) ((p i1).asIdeal)
        fun q hq _ _ ↦ Ideal.minimalPrimes_isPrime hq).mp hsubset
    have hhead_le_p1 : p.head.asIdeal ≤ (p i1).asIdeal :=
      p.monotone (Fin.zero_le i1)
    have hq_le_head : q ≤ p.head.asIdeal := by
      exact hq.2 ⟨p.head.2, bot_le⟩ (hhead_le_p1.trans hp1_le_q)
    have hp1_eq_head : (p i1).asIdeal = p.head.asIdeal := by
      exact le_antisymm (hp1_le_q.trans hq_le_head) hhead_le_p1
    exact hhead_lt.ne (PrimeSpectrum.ext hp1_eq_head.symm)
  obtain ⟨x, hx_mem, hx_not_union⟩ := Set.not_subset.mp hnot_subset
  refine ⟨x, ?_, ?_, ?_⟩
  · simpa [hi1] using hx_mem
  · exact IsLocalRing.le_maximalIdeal_of_isPrime ((p i1).asIdeal) hx_mem
  · intro q hq hqx
    exact hx_not_union <| Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hqx⟩⟩

/-- Helper for Lemma 10.103.9: if `x` lies in the second prime but not in the head, then the
second prime is minimal over `p.head + (x)`. -/
private lemma second_prime_mem_minimalPrimes_sup_span_singleton
    (p : LTSeries (PrimeSpectrum R)) (hp : IsMaxChain (· ≤ ·) (Set.range p))
    (hlen : p.length ≠ 0) {x : R}
    (hx_mem : x ∈ (p 1).asIdeal) (hx_not_head : x ∉ p.head.asIdeal) :
    (p 1).asIdeal ∈ (p.head.asIdeal ⊔ Ideal.span {x}).minimalPrimes := by
  let i1 : Fin (p.length + 1) := ⟨1, Nat.succ_lt_succ (Nat.pos_of_ne_zero hlen)⟩
  have hi1 : i1 = 1 := by
    ext
    simp [i1, Nat.mod_eq_of_lt (Nat.succ_lt_succ (Nat.pos_of_ne_zero hlen))]
  have hone : ((1 : Fin (p.length + 1)) : ℕ) = 1 := by
    simp [Nat.mod_eq_of_lt (Nat.succ_lt_succ (Nat.pos_of_ne_zero hlen))]
  have hhead_lt_i1 : p.head < p i1 := by
    have hstep := p.step ⟨0, Nat.pos_of_ne_zero hlen⟩
    simpa [RelSeries.head] using hstep
  have hhead_lt_second : p.head < p 1 := by
    simpa [hi1] using hhead_lt_i1
  have hsup_le_second : p.head.asIdeal ⊔ Ideal.span {x} ≤ (p 1).asIdeal := by
    refine sup_le ?_ ?_
    · exact p.monotone (show (0 : Fin (p.length + 1)) ≤ 1 by simp)
    · exact (Ideal.span_singleton_le_iff_mem ((p 1).asIdeal)).2 hx_mem
  have hsup_ne_top : p.head.asIdeal ⊔ Ideal.span {x} ≠ ⊤ := by
    intro htop
    exact (p 1).2.ne_top <| top_le_iff.mp (htop ▸ hsup_le_second)
  obtain ⟨q, hq, hq_le_second⟩ :=
    Ideal.exists_minimalPrimes_le (I := p.head.asIdeal ⊔ Ideal.span {x}) hsup_le_second
  let q' : PrimeSpectrum R := ⟨q, hq.1.1⟩
  have hhead_le_q : p.head.asIdeal ≤ q := le_sup_left.trans hq.1.2
  have hx_mem_q : x ∈ q := le_sup_right.trans hq.1.2 (Ideal.mem_span_singleton_self x)
  have hhead_ne_q : p.head.asIdeal ≠ q := by
    intro hEq
    exact hx_not_head (hEq ▸ hx_mem_q)
  have hhead_lt_q : p.head < q' := by
    exact lt_of_le_of_ne hhead_le_q (fun hEq ↦ hhead_ne_q (congrArg PrimeSpectrum.asIdeal hEq))
  have hq_eq_second : q' = p 1 := by
    by_contra hneq
    have hq_lt_second : q' < p 1 := lt_of_le_of_ne hq_le_second hneq
    -- Inserting a prime strictly between `p.head` and `p 1` enlarges the chain, contradicting
    -- maximality.
    have hchain : IsChain (· ≤ ·) (insert q' (Set.range p)) := by
      refine hp.isChain.insert ?_
      intro y hy _
      rcases hy with ⟨i, rfl⟩
      by_cases hi0 : i = 0
      · subst hi0
        exact Or.inr hhead_lt_q.le
      · have h1_le_i : (1 : Fin (p.length + 1)) ≤ i := by
          have hi0_val : i.1 ≠ 0 := by
            intro hi0_val
            apply hi0
            ext
            simpa using hi0_val
          have h1_le_i_nat : ((1 : Fin (p.length + 1)) : ℕ) ≤ i.1 := by
            simpa [Nat.mod_eq_of_lt (Nat.succ_lt_succ (Nat.pos_of_ne_zero hlen))] using
              (show (1 : ℕ) ≤ i.1 by omega)
          exact Fin.le_iff_val_le_val.mpr h1_le_i_nat
        exact Or.inl (hq_le_second.trans (p.monotone h1_le_i))
    have hEq : insert q' (Set.range p) = Set.range p :=
      (hp.2 hchain (Set.subset_insert _ _)).symm
    have hq_mem_range : q' ∈ Set.range p := by
      rw [← hEq]
      simp
    rcases hq_mem_range with ⟨i, hi⟩
    by_cases hi0 : i = 0
    · subst hi0
      exact hhead_lt_q.ne <| by simpa [RelSeries.head, q'] using hi
    · have h1_le_i : (1 : Fin (p.length + 1)) ≤ i := by
        have hi0_val : i.1 ≠ 0 := by
          intro hi0_val
          apply hi0
          ext
          simpa using hi0_val
        have h1_le_i_nat : ((1 : Fin (p.length + 1)) : ℕ) ≤ i.1 := by
          simpa [Nat.mod_eq_of_lt (Nat.succ_lt_succ (Nat.pos_of_ne_zero hlen))] using
            (show (1 : ℕ) ≤ i.1 by omega)
        exact Fin.le_iff_val_le_val.mpr h1_le_i_nat
      have hi_le_one : i ≤ 1 := by
        by_contra hi_gt_one
        have h1_lt_i : (1 : Fin (p.length + 1)) < i := lt_of_not_ge hi_gt_one
        have hsecond_lt_q : p 1 < q' := by
          simpa [hi] using p.strictMono h1_lt_i
        exact hsecond_lt_q.not_ge hq_le_second
      have hi1 : i = 1 := by
        ext
        omega
      exact hneq <| by simpa [q'] using hi1 ▸ hi.symm
  have hqIdeal_eq : q = (p 1).asIdeal := congrArg PrimeSpectrum.asIdeal hq_eq_second
  simpa [hqIdeal_eq] using hq

/-- Helper for Lemma 10.103.9: associated primes over `R` transport to associated primes over a
quotient ring along the canonical surjection. -/
private lemma associated_prime_map_quotient_of_mem_associatedPrimes
    (I : Ideal R) [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M]
    {q : Ideal R} (hq : q ∈ associatedPrimes R M) :
    q.map (Ideal.Quotient.mk I) ∈ associatedPrimes (R ⧸ I) M := by
  have himage :
      q ∈ Ideal.comap (algebraMap R (R ⧸ I)) '' associatedPrimes (R ⧸ I) M := by
    rwa [associatedPrimes_restrictScalars_eq_image_comap (R := R) (S := R ⧸ I) (M := M)]
  rcases himage with ⟨qbar, hqbar, hcomap⟩
  have hqbar_eq : qbar = q.map (Ideal.Quotient.mk I) := by
    calc
      qbar = Ideal.map (Ideal.Quotient.mk I) (Ideal.comap (Ideal.Quotient.mk I) qbar) := by
        symm
        exact Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective qbar
      _ = q.map (Ideal.Quotient.mk I) := by
        simpa using congrArg (Ideal.map (Ideal.Quotient.mk I)) hcomap
  simpa [hqbar_eq] using hqbar

/-- Helper for Lemma 10.103.9: support over a quotient ring is detected after contracting the
prime to the original ring. -/
private lemma mem_support_over_quotient_iff_comap_mem_support
    (I : Ideal R) [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M]
    (qbar : PrimeSpectrum (R ⧸ I)) :
    qbar ∈ Module.support (R ⧸ I) M ↔
      PrimeSpectrum.comap (Ideal.Quotient.mk I) qbar ∈ Module.support R M := by
  rw [Module.mem_support_iff', Module.mem_support_iff']
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    intro r hr
    have hneq := hm (Ideal.Quotient.mk I r) <| by
      simpa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hr
    intro hzero
    have hzero' : (algebraMap R (R ⧸ I) r) • m = 0 := by
      rw [IsScalarTower.algebraMap_smul (R := R) (A := R ⧸ I) r m]
      exact hzero
    exact hneq <| by
      simpa using hzero'
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    intro s hs
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hneq := hm r <| by
      simpa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hs
    intro hzero
    have hzero' : (algebraMap R (R ⧸ I) r) • m = 0 := by
      simpa using hzero
    have hzero'' : r • m = 0 := by
      rw [← IsScalarTower.algebraMap_smul (R := R) (A := R ⧸ I) r m]
      exact hzero'
    exact hneq hzero''

/-- Helper for Lemma 10.103.9: when `M` has full support, quotienting by `a` identifies the
support dimension of `M / aM` with the Krull dimension of `R / (a)`. -/
private lemma supportDim_quotSMulTop_eq_ringKrullDim_quotient_span_singleton_of_full_support
    [Module.Finite R M] (hsupp : Module.support R M = Set.univ) (a : R) :
    Module.supportDim R (QuotSMulTop a M) =
      ringKrullDim (R ⧸ Ideal.span ({a} : Set R)) := by
  -- Full support turns the support of `M / aM` into the zero locus of `(a)`.
  rw [Module.supportDim, Module.support_quotSMulTop, hsupp, Set.univ_inter]
  -- The quotient-spectrum model of `Spec (R / (a))` is exactly that zero locus.
  rw [ringKrullDim_quotient, PrimeSpectrum.zeroLocus_span]

/-- Helper for Lemma 10.103.9: full support over `R` descends to full support over any quotient
ring after restricting to the quotient module structure. -/
private lemma support_over_quotient_eq_univ_of_support_eq_univ
    (I : Ideal R) [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M]
    (hsupp : Module.support R M = Set.univ) :
    Module.support (R ⧸ I) M = Set.univ := by
  ext qbar
  -- Support over the quotient is detected after contracting the prime back to `R`.
  rw [mem_support_over_quotient_iff_comap_mem_support (R := R) (M := M) I qbar, hsupp]
  simp

/-- Helper for Lemma 10.103.9: full support identifies the support dimension of `M` with the
Krull dimension of the ambient ring. -/
private lemma supportDim_eq_ringKrullDim_of_support_eq_univ
    [Module.Finite R M] (hsupp : Module.support R M = Set.univ) :
    Module.supportDim R M = ringKrullDim R := by
  -- Replacing the support by all of `Spec R` turns the support dimension into the ambient Krull
  -- dimension.
  have hsupport :
      Order.krullDim (Module.support R M) = Order.krullDim (PrimeSpectrum R) := by
    rw [hsupp]
    exact
      (Order.krullDim_eq_of_orderIso
        (OrderIso.Set.univ : (Set.univ : Set (PrimeSpectrum R)) ≃o PrimeSpectrum R))
  simpa [Module.supportDim, ringKrullDim] using hsupport

/-- Helper for Lemma 10.103.9: a maximal chain in an upper interval is already maximal in the
ambient order once the interval base point is minimal. -/
private lemma isMaxChain_of_isMin_head_and_isMaxChain_ici
    {α : Type*} [Preorder α] {a : α} {t : Set (Set.Ici a)}
    (ha : IsMin a) (ht : IsMaxChain (· ≤ ·) t) :
    IsMaxChain (· ≤ ·) (Subtype.val '' t) := by
  constructor
  · -- Forgetting the subtype preserves the chain property.
    simpa using
      ht.isChain.image_of_map_rel (· ≤ ·) (· ≤ ·) (Subtype.val) (fun _ _ h ↦ h)
  · intro s hs hsubset
    let s' : Set (Set.Ici a) := Subtype.val ⁻¹' s
    have hs'_chain : IsChain (· ≤ ·) s' := by
      -- Pull the ambient chain back to the upper interval.
      simpa [s'] using
        hs.preimage (r := (· ≤ ·)) (s := (· ≤ ·)) (f := Subtype.val)
          Subtype.val_injective (fun _ _ h ↦ h)
    have ht_subset : t ⊆ s' := by
      intro x hx
      exact hsubset ⟨x, hx, rfl⟩
    have hEq : t = s' := ht.2 hs'_chain ht_subset
    refine Set.Subset.antisymm hsubset ?_
    have ha_mem_t : (⟨a, le_rfl⟩ : Set.Ici a) ∈ t := ht.bot_mem
    have ha_mem_image : a ∈ Subtype.val '' t := ⟨⟨a, le_rfl⟩, ha_mem_t, rfl⟩
    have ha_mem_s : a ∈ s := hsubset ha_mem_image
    intro x hx
    have hax : a ≤ x := by
      by_cases hxa_eq : x = a
      · simpa [hxa_eq]
      · rcases hs hx ha_mem_s hxa_eq with hxa | hax
        · exact ha hxa
        · exact hax
    have hx' : (⟨x, hax⟩ : Set.Ici a) ∈ s' := hx
    have hx_t : (⟨x, hax⟩ : Set.Ici a) ∈ t := by
      rw [hEq]
      exact hx'
    exact ⟨⟨x, hax⟩, hx_t, rfl⟩

/-- Helper for Lemma 10.103.9: the tail of a nontrivial strict prime chain is exactly the upper
slice of the original range above its second point. -/
private lemma range_tail_eq_upper_slice_range
    (p : LTSeries (PrimeSpectrum R)) (hlen : p.length ≠ 0) :
    Set.range (p.tail hlen) = {q : PrimeSpectrum R | q ∈ Set.range p ∧ p 1 ≤ q} := by
  ext q
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨?_, ?_⟩
    · -- The tail entries are the original chain entries indexed by successors.
      refine ⟨(Fin.cast (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hlen)) i).succ, rfl⟩
    · -- Every successor index lies above `1`, so the tail lies in the upper slice.
      exact p.monotone (show (1 : Fin (p.length + 1)) ≤
        (Fin.cast (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hlen)) i).succ by
          exact Fin.le_iff_val_le_val.mpr (by
            change 1 % (p.length + 1) ≤ (Fin.cast
              (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hlen)) i).1 + 1
            rw [Nat.mod_eq_of_lt (Nat.succ_lt_succ (Nat.pos_of_ne_zero hlen))]
            exact Nat.succ_le_succ (Nat.zero_le _)))
  · rintro ⟨⟨i, rfl⟩, hi⟩
    obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
    · -- The head cannot lie above the second point in a strict chain.
      have hone :
          (⟨1, Nat.succ_lt_succ (Nat.pos_of_ne_zero hlen)⟩ : Fin (p.length + 1)) = 1 := by
        ext
        simp [Nat.mod_eq_of_lt (Nat.succ_lt_succ (Nat.pos_of_ne_zero hlen))]
      have hstep : p 0 < p 1 := by
        simpa [hone] using p.step ⟨0, Nat.pos_of_ne_zero hlen⟩
      exact (hstep.not_ge hi).elim
    · -- Any later point is represented uniquely by a tail index.
      refine ⟨Fin.cast (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hlen)).symm j, rfl⟩

/-- Helper for Lemma 10.103.9: once `a` lies in the second prime, every point of the tail chain
lies in the zero locus of `(a)`. -/
private lemma mem_zeroLocus_span_singleton_of_mem_range_tail
    (p : LTSeries (PrimeSpectrum R)) (hlen : p.length ≠ 0) {a : R}
    (ha : a ∈ (p 1).asIdeal) {q : PrimeSpectrum R}
    (hq : q ∈ Set.range (p.tail hlen)) :
    q ∈ PrimeSpectrum.zeroLocus (R := R) (Ideal.span ({a} : Set R)) := by
  -- Rewrite the tail range as the upper slice where monotonicity carries `a` into every prime.
  rw [range_tail_eq_upper_slice_range (R := R) p hlen] at hq
  refine (PrimeSpectrum.mem_zeroLocus q (Ideal.span ({a} : Set R))).2 ?_
  exact Ideal.span_singleton_le_iff_mem q.asIdeal |>.2 (hq.2 ha)

/-- Helper for Lemma 10.103.9: an order isomorphism carries the upper interval above `a` to the
upper interval above its image. -/
private lemma exists_orderIso_ici_congr {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o β) (a : α) :
    Nonempty (Set.Ici a ≃o Set.Ici (e a)) := by
  refine ⟨{
      toFun := fun x ↦ ⟨e x.1, e.monotone x.2⟩
      invFun := fun y ↦ ⟨e.symm y.1, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }⟩
  · -- Pulling back along the inverse order isomorphism returns to the original lower bound.
    have hy := e.symm.monotone y.2
    simpa using hy
  · -- Both subtype coordinates are definitionally preserved by `e.symm ∘ e`.
    intro x
    ext
    simp
  · -- The same holds on the codomain side by `e ∘ e.symm = id`.
    intro y
    ext
    simp
  · -- Comparability in the interval is exactly comparability in the ambient order.
    intro x y
    change e x.1 ≤ e y.1 ↔ x.1 ≤ y.1
    exact e.map_rel_iff

/-- Helper for Lemma 10.103.9: the chosen interval transport for an order isomorphism. -/
private noncomputable def orderIso_ici_congr {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o β) (a : α) :
    Set.Ici a ≃o Set.Ici (e a) :=
  Classical.choice (exists_orderIso_ici_congr e a)

/-- Helper for Lemma 10.103.9: the tail of a maximal chain is already maximal in the upper
interval above the second prime. -/
private lemma tail_preimage_isMaxChain_ici_second
    (p : LTSeries (PrimeSpectrum R)) (hp : IsMaxChain (· ≤ ·) (Set.range p))
    (hlen : p.length ≠ 0) :
    IsMaxChain (· ≤ ·) (Subtype.val ⁻¹' Set.range (p.tail hlen) : Set (Set.Ici (p 1))) := by
  have hmem : p 1 ∈ Set.range p := ⟨1, rfl⟩
  -- Restrict the original maximal chain to the upper interval above the second point.
  have hici :
      IsMaxChain (· ≤ ·) (Subtype.val ⁻¹' Set.range p : Set (Set.Ici (p 1))) :=
    by
      constructor
      · -- Restricting a chain to a subtype preserves comparability.
        simpa using hp.isChain.preimage (r := (· ≤ ·)) (s := (· ≤ ·))
          (f := Subtype.val) Subtype.val_injective (fun _ _ h ↦ h)
      · intro t ht hsubset
        -- Extend a larger upper chain by the unchanged lower slice of the original chain.
        have h_union_chain :
            IsChain (· ≤ ·) ({x : PrimeSpectrum R | x ∈ Set.range p ∧ x ≤ p 1} ∪
              Subtype.val '' t) := by
          rw [isChain_union]
          refine ⟨?_, ?_, ?_⟩
          · simpa using hp.isChain.mono (by
              intro x hx
              exact hx.1)
          · simpa using ht.image_of_map_rel (r := (· ≤ ·)) (s := (· ≤ ·))
              (f := Subtype.val) (fun _ _ h ↦ h)
          · intro x hx y hy hxy
            left
            rcases hy with ⟨y', hy', rfl⟩
            exact hx.2.trans y'.2
        have hs_subset :
            Set.range p ⊆ ({x : PrimeSpectrum R | x ∈ Set.range p ∧ x ≤ p 1} ∪
              Subtype.val '' t) := by
          intro x hx
          by_cases hxp : p 1 ≤ x
          · right
            refine ⟨⟨x, hxp⟩, ?_, rfl⟩
            exact hsubset hx
          · left
            refine ⟨hx, ?_⟩
            cases hp.isChain.total hx hmem with
            | inl h => exact h
            | inr h => exact (hxp h).elim
        have hs_eq :
            Set.range p =
              ({x : PrimeSpectrum R | x ∈ Set.range p ∧ x ≤ p 1} ∪ Subtype.val '' t) :=
          hp.2 h_union_chain hs_subset
        apply Set.Subset.antisymm hsubset
        intro x hx
        have : ((x : PrimeSpectrum R) ∈
            ({x : PrimeSpectrum R | x ∈ Set.range p ∧ x ≤ p 1} ∪ Subtype.val '' t)) :=
          Or.inr ⟨x, hx, rfl⟩
        exact hs_eq.symm ▸ this
  -- Route correction: rewrite the upper slice as the literal tail range before quotient transport.
  have hset :
      (Subtype.val ⁻¹' Set.range (p.tail hlen) : Set (Set.Ici (p 1))) =
        (Subtype.val ⁻¹' Set.range p : Set (Set.Ici (p 1))) := by
    ext x
    constructor
    · intro hx
      have hx' : (x : PrimeSpectrum R) ∈ Set.range (p.tail hlen) := hx
      rw [range_tail_eq_upper_slice_range (R := R) p hlen] at hx'
      exact hx'.1
    · intro hx
      rw [range_tail_eq_upper_slice_range (R := R) p hlen]
      exact ⟨hx, x.2⟩
  rw [hset]
  exact hici

/-- Helper for Lemma 10.103.9: the upper interval in the zero locus above the head point is just
the ambient upper interval above that point. -/
private lemma exists_zeroLocus_ici_head_orderIso
    (I : Ideal R) {q : PrimeSpectrum R}
    (hq : q ∈ PrimeSpectrum.zeroLocus (R := R) I) :
    Nonempty (Set.Ici (⟨q, hq⟩ : PrimeSpectrum.zeroLocus (R := R) I) ≃o Set.Ici q) := by
  refine ⟨{
      toFun := fun x ↦ ⟨x.1.1, x.2⟩
      invFun := fun y ↦ ⟨⟨y.1, ?_⟩, y.2⟩
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }⟩
  · -- The zero locus is an upper set, so every point above `q` remains inside it.
    exact (PrimeSpectrum.mem_zeroLocus y.1 I).2 <|
      ((PrimeSpectrum.mem_zeroLocus q I).1 hq).trans y.2
  · -- Forgetting and reattaching the zero-locus proof does not change the underlying point.
    intro x
    ext
    rfl
  · -- The ambient upper interval data is unchanged by the inverse construction.
    intro y
    ext
    rfl
  · -- The order relation is inherited from the ambient spectrum.
    intro x y
    rfl

/-- Helper for Lemma 10.103.9: the upper interval in the zero locus above the head point is just
the ambient upper interval above that point. -/
private noncomputable def zeroLocus_ici_head_orderIso
    (I : Ideal R) {q : PrimeSpectrum R}
    (hq : q ∈ PrimeSpectrum.zeroLocus (R := R) I) :
    Set.Ici (⟨q, hq⟩ : PrimeSpectrum.zeroLocus (R := R) I) ≃o Set.Ici q :=
  Classical.choice (exists_zeroLocus_ici_head_orderIso (R := R) I hq)

/-- Helper for Lemma 10.103.9: the quotient-spectrum order isomorphism identifies the upper
interval above the quotient head with the ambient upper interval above the original head. -/
private lemma exists_quotient_ici_head_orderIso
    (I : Ideal R) {q : PrimeSpectrum R}
    (hq : q ∈ PrimeSpectrum.zeroLocus (R := R) I) :
    Nonempty (Set.Ici ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨q, hq⟩) ≃o
      Set.Ici q) := by
  let e : PrimeSpectrum (R ⧸ I) ≃o PrimeSpectrum.zeroLocus (R := R) I :=
    Ideal.primeSpectrumQuotientOrderIsoZeroLocus I
  -- First lift the quotient/zero-locus correspondence to upper intervals.
  let eIci :
      Set.Ici (e.symm ⟨q, hq⟩) ≃o Set.Ici (e (e.symm ⟨q, hq⟩)) :=
    orderIso_ici_congr e (e.symm ⟨q, hq⟩)
  -- Then rewrite the endpoint by `e.apply_symm_apply` and forget the zero-locus subtype.
  let eEq :
      Set.Ici (e (e.symm ⟨q, hq⟩)) ≃o Set.Ici (⟨q, hq⟩ : PrimeSpectrum.zeroLocus (R := R) I) :=
    OrderIso.setCongr _ _ <| by
      simpa using congrArg Set.Ici (e.apply_symm_apply ⟨q, hq⟩)
  exact ⟨eIci.trans (eEq.trans (zeroLocus_ici_head_orderIso (R := R) I hq))⟩

/-- Helper for Lemma 10.103.9: the quotient-spectrum order isomorphism identifies the upper
interval above the quotient head with the ambient upper interval above the original head. -/
private noncomputable def quotient_ici_head_orderIso
    (I : Ideal R) {q : PrimeSpectrum R}
    (hq : q ∈ PrimeSpectrum.zeroLocus (R := R) I) :
    Set.Ici ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨q, hq⟩) ≃o Set.Ici q :=
  Classical.choice (exists_quotient_ici_head_orderIso (R := R) I hq)

/-- Helper for Lemma 10.103.9: after quotienting by `(a)`, the support of `M / aM` over the
quotient ring is all of the quotient spectrum when `M` had full support over `R`. -/
private lemma support_quotSMulTop_over_quotient_eq_univ_of_full_support
    [Module.Finite R M] (hsupp : Module.support R M = Set.univ) (a : R) :
    Module.support (R ⧸ Ideal.span ({a} : Set R)) (QuotSMulTop a M) = Set.univ := by
  let hTors : Module.IsTorsionBySet R (QuotSMulTop a M) (Ideal.span ({a} : Set R)) :=
    (Module.isTorsionBySet_iff_is_torsion_by_span (R := R) (M := QuotSMulTop a M)
      ({a} : Set R)).1 <|
      (Module.isTorsionBySet_singleton_iff (R := R) (M := QuotSMulTop a M) (a := a)).2 <|
        Module.isTorsionBy_quotient_element_smul (M := M) a
  let _ : Module (R ⧸ Ideal.span ({a} : Set R)) (QuotSMulTop a M) := hTors.module
  let _ : IsScalarTower R (R ⧸ Ideal.span ({a} : Set R)) (QuotSMulTop a M) :=
    Module.IsTorsionBySet.isScalarTower hTors
  ext qbar
  constructor
  · intro _
    simp
  · intro _
    -- Detect quotient support by contracting the prime back to `R`.
    exact (mem_support_over_quotient_iff_comap_mem_support (R := R) (M := QuotSMulTop a M)
        (I := Ideal.span ({a} : Set R)) qbar).2 <| by
      rw [Module.support_quotSMulTop, hsupp]
      refine ⟨by simp, ?_⟩
      refine (PrimeSpectrum.mem_zeroLocus _ _).2 ?_
      -- The contracted prime always contains `(a)`.
      intro x hx
      simp at hx
      subst hx
      change Ideal.Quotient.mk (Ideal.span ({x} : Set R)) x ∈ qbar.asIdeal
      have hxzero : Ideal.Quotient.mk (Ideal.span ({x} : Set R)) x = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span (by simp)
      simpa [hxzero] using (qbar.asIdeal.zero_mem :
        (0 : R ⧸ Ideal.span ({x} : Set R)) ∈ qbar.asIdeal)

/-- Helper for Lemma 10.103.9: the quotient-spectrum point corresponding to the second prime has
ideal equal to the image of that prime under the quotient map. -/
private lemma quotient_head_asIdeal_eq_map_second_prime
    (p : LTSeries (PrimeSpectrum R)) (I : Ideal R)
    (hq : p 1 ∈ PrimeSpectrum.zeroLocus (R := R) I) :
    ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨p 1, hq⟩).asIdeal =
      (p 1).asIdeal.map (Ideal.Quotient.mk I) := by
  -- Compare the quotient point with its image back in the zero locus, then rewrite its ideal by
  -- the quotient-map comap/map formulas.
  have hcomap_eq :
      PrimeSpectrum.comap (Ideal.Quotient.mk I)
        ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨p 1, hq⟩) = p 1 := by
    exact congrArg Subtype.val
      ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).apply_symm_apply ⟨p 1, hq⟩)
  have hcomap_asIdeal :
      Ideal.comap (Ideal.Quotient.mk I)
          (((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨p 1, hq⟩).asIdeal) =
        (p 1).asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hcomap_eq
  calc
    ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨p 1, hq⟩).asIdeal =
        Ideal.map (Ideal.Quotient.mk I)
          (Ideal.comap (Ideal.Quotient.mk I)
            (((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨p 1, hq⟩).asIdeal)) := by
          symm
          exact Ideal.map_comap_of_surjective (Ideal.Quotient.mk I)
            Ideal.Quotient.mk_surjective _
    _ = (p 1).asIdeal.map (Ideal.Quotient.mk I) := by
      simpa [hcomap_asIdeal]

/-- Helper for Lemma 10.103.9: the one-step quotient `M / aM` remains Cohen-Macaulay and has full
support over the principal quotient ring. -/
private lemma quotSMulTop_cohenMacaulay_and_full_support_over_principal_quotient
    [Module.Finite R M] {a : R}
    [IsLocalRing (R ⧸ Ideal.span ({a} : Set R))]
    (ha_max : a ∈ IsLocalRing.maximalIdeal R)
    (hCM : Module.CohenMacaulay R M) (hsupp : Module.support R M = Set.univ)
    {d : ℕ} (hMdim_nat : Module.supportDim R M = d)
    (hdrop : Module.supportDim R (QuotSMulTop a M) + 1 = Module.supportDim R M) :
    Module.CohenMacaulay (R ⧸ Ideal.span ({a} : Set R)) (QuotSMulTop a M) ∧
      Module.support (R ⧸ Ideal.span ({a} : Set R)) (QuotSMulTop a M) = Set.univ := by
  let _ : Module.CohenMacaulay R M := hCM
  have hreg_list : RingTheory.Sequence.IsRegular M [a] := by
    -- The one-step support-dimension drop is exactly the owner hypothesis ensuring that `[a]` is
    -- an `M`-regular sequence.
    refine Module.isRegular_of_supportDim_quotient_add_length_eq_of_cohenMacaulay
      (R := R) (M := M) (gs := [a]) (d := d) ?_ hMdim_nat ?_
    · intro g hg
      simpa [List.mem_singleton.mp hg] using ha_max
    · rw [Ideal.ofList_singleton, Submodule.ideal_span_singleton_smul]
      simpa [QuotSMulTop] using hdrop
  have hreg : IsSMulRegular M a := by
    -- A regular singleton records exactly the non-zero-divisor property of its entry.
    simpa using ((RingTheory.Sequence.isRegular_cons_iff (M := M) a []).1 hreg_list).1
  have hCMquot_R : Module.CohenMacaulay R (QuotSMulTop a M) := by
    exact
      (Module.cohenMacaulay_iff_quotSMulTop_of_mem_maximalIdeal
        (R := R) (M := M) (x := a) ha_max hreg).1 hCM
  let hTors :
      Module.IsTorsionBySet R (QuotSMulTop a M) (Ideal.span ({a} : Set R)) :=
    (Module.isTorsionBySet_iff_is_torsion_by_span (R := R) (M := QuotSMulTop a M)
      ({a} : Set R)).1 <|
      (Module.isTorsionBySet_singleton_iff (R := R) (M := QuotSMulTop a M) (a := a)).2 <|
        Module.isTorsionBy_quotient_element_smul (M := M) a
  let _ : Module (R ⧸ Ideal.span ({a} : Set R)) (QuotSMulTop a M) := hTors.module
  let _ : IsScalarTower R (R ⧸ Ideal.span ({a} : Set R)) (QuotSMulTop a M) :=
    Module.IsTorsionBySet.isScalarTower hTors
  let _ : Module.Finite (R ⧸ Ideal.span ({a} : Set R)) (QuotSMulTop a M) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span ({a} : Set R)) (QuotSMulTop a M)
  have hCMquot_S :
      Module.CohenMacaulay (R ⧸ Ideal.span ({a} : Set R)) (QuotSMulTop a M) :=
    (Module.cohenMacaulay_iff_restrictScalars_of_surjective
      (R := R) (S := R ⧸ Ideal.span ({a} : Set R)) (N := QuotSMulTop a M)
      Ideal.Quotient.mk_surjective).2 hCMquot_R
  refine ⟨hCMquot_S, ?_⟩
  -- The support computation from Lemma `10.40.9` already shows that quotient support stays full.
  exact support_quotSMulTop_over_quotient_eq_univ_of_full_support (R := R) (M := M) hsupp a

/-- Helper for Lemma 10.103.9: once the second prime is associated after quotienting by `(a)`,
the corresponding quotient-spectrum head is minimal. -/
private lemma quotient_head_isMin_of_associated_second_prime
    [Module.Finite R M] {a : R} (p : LTSeries (PrimeSpectrum R)) (I : Ideal R)
    [IsLocalRing (R ⧸ I)]
    [Module (R ⧸ I) (QuotSMulTop a M)] [IsScalarTower R (R ⧸ I) (QuotSMulTop a M)]
    [Module.Finite (R ⧸ I) (QuotSMulTop a M)]
    (hq : p 1 ∈ PrimeSpectrum.zeroLocus (R := R) I)
    (hassoc : (p 1).asIdeal ∈ associatedPrimes R (QuotSMulTop a M))
    (hCMquot : Module.CohenMacaulay (R ⧸ I) (QuotSMulTop a M))
    (hsuppquot : Module.support (R ⧸ I) (QuotSMulTop a M) = Set.univ) :
    IsMin ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨p 1, hq⟩) := by
  let qbar : PrimeSpectrum (R ⧸ I) :=
    (Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨p 1, hq⟩
  have hqbar_assoc :
      qbar.asIdeal ∈ associatedPrimes (R ⧸ I) (QuotSMulTop a M) := by
    -- Transport the associated prime across the quotient map, then rewrite the quotient head ideal
    -- into the literal mapped second prime.
    have hmap_assoc :
        (p 1).asIdeal.map (Ideal.Quotient.mk I) ∈ associatedPrimes (R ⧸ I) (QuotSMulTop a M) :=
      associated_prime_map_quotient_of_mem_associatedPrimes
        (R := R) (M := QuotSMulTop a M) I hassoc
    simpa [qbar, quotient_head_asIdeal_eq_map_second_prime (R := R) p I hq] using hmap_assoc
  let _ : Module.CohenMacaulay (R ⧸ I) (QuotSMulTop a M) := hCMquot
  have hminimal_support :
      Minimal (· ∈ Module.support (R ⧸ I) (QuotSMulTop a M)) qbar :=
    (ringKrullDim_quotient_and_minimal_support_of_mem_associatedPrimes_of_cohenMacaulay
      (R := R ⧸ I) (M := QuotSMulTop a M) qbar hqbar_assoc).2
  -- Full quotient support converts minimal support into minimality in the quotient spectrum.
  have hminimal_support' := minimal_mem_iff.mp hminimal_support
  intro q hqle
  exact (hminimal_support'.2 (by simpa [hsuppquot]) hqle).le

/-- Helper for Lemma 10.103.9: the literal quotient tail chain obtained by transporting `p.tail`
through the quotient-spectrum interval order isomorphism. -/
private noncomputable def tail_chain_in_quotient
    (p : LTSeries (PrimeSpectrum R)) (hlen : p.length ≠ 0) (I : Ideal R)
    (hq : p 1 ∈ PrimeSpectrum.zeroLocus (R := R) I) :
    LTSeries (PrimeSpectrum (R ⧸ I)) := by
  let tailIci : LTSeries (Set.Ici (p 1)) :=
    { length := (p.tail hlen).length
      toFun := fun i ↦
        ⟨(p.tail hlen) i, by
          -- Every tail point lies above the second prime.
          simpa using LTSeries.head_le (p.tail hlen) i⟩
      step := fun i ↦ (p.tail hlen).step i }
  let e : Set.Ici (p 1) ≃o
      Set.Ici ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨p 1, hq⟩) :=
    (quotient_ici_head_orderIso (R := R) I hq).symm
  -- Route correction: package the transported tail as an actual `LTSeries`, not only as an image
  -- of sets inside the quotient spectrum.
  exact tailIci.map (fun x ↦ (e x).1) (fun _ _ h ↦ e.strictMono h)

/-- Helper for Lemma 10.103.9: the ambient transported image of the tail is exactly the range of
the literal quotient tail chain. -/
private lemma mapped_tail_range_eq_transport_image
    (p : LTSeries (PrimeSpectrum R)) (hlen : p.length ≠ 0) (I : Ideal R)
    (hq : p 1 ∈ PrimeSpectrum.zeroLocus (R := R) I) :
    Set.range (tail_chain_in_quotient (R := R) p hlen I hq) =
      Subtype.val '' (((quotient_ici_head_orderIso (R := R) I hq).symm) ''
        (Subtype.val ⁻¹' Set.range (p.tail hlen) : Set (Set.Ici (p 1)))) := by
  let tailIci : LTSeries (Set.Ici (p 1)) :=
    { length := (p.tail hlen).length
      toFun := fun i ↦
        ⟨(p.tail hlen) i, by
          simpa using LTSeries.head_le (p.tail hlen) i⟩
      step := fun i ↦ (p.tail hlen).step i }
  let e : Set.Ici (p 1) ≃o
      Set.Ici ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨p 1, hq⟩) :=
    (quotient_ici_head_orderIso (R := R) I hq).symm
  have htailIci :
      Set.range tailIci = (Subtype.val ⁻¹' Set.range (p.tail hlen) : Set (Set.Ici (p 1))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · intro hx
      rcases hx with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      exact Subtype.ext hi
  have hmap :
      Set.range (tailIci.map (fun x ↦ (e x).1) (fun _ _ h ↦ e.strictMono h)) =
        (fun x ↦ (e x).1) '' Set.range tailIci := by
    ext qbar
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨tailIci i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rcases hx with ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  -- Unfold the packaged chain and rewrite its range in the ambient quotient spectrum.
  rw [tail_chain_in_quotient, hmap, htailIci]
  ext qbar
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, hy⟩, hval⟩
    refine ⟨x, hx, ?_⟩
    have hy' : e x = y := by simpa using hy
    simpa [hy'] using hval

/-- Helper for Lemma 10.103.9: once the quotient head is minimal, the transported quotient tail
range is again a maximal chain in the quotient spectrum. -/
private lemma mapped_tail_isMaxChain_in_quotient
    (p : LTSeries (PrimeSpectrum R)) (hp : IsMaxChain (· ≤ ·) (Set.range p))
    (hlen : p.length ≠ 0) (I : Ideal R)
    (hq : p 1 ∈ PrimeSpectrum.zeroLocus (R := R) I)
    (hqbar_min :
      IsMin ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨p 1, hq⟩)) :
    IsMaxChain (· ≤ ·) (Set.range (tail_chain_in_quotient (R := R) p hlen I hq)) := by
  let e : Set.Ici (p 1) ≃o
      Set.Ici ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨p 1, hq⟩) :=
    (quotient_ici_head_orderIso (R := R) I hq).symm
  have hpre :
      IsMaxChain (· ≤ ·) (Subtype.val ⁻¹' Set.range (p.tail hlen) : Set (Set.Ici (p 1))) :=
    tail_preimage_isMaxChain_ici_second (R := R) p hp hlen
  have htransport :
      IsMaxChain (· ≤ ·)
        (e '' (Subtype.val ⁻¹' Set.range (p.tail hlen) : Set (Set.Ici (p 1)))) :=
    IsMaxChain.image e hpre
  have hambient :
      IsMaxChain (· ≤ ·)
        (Subtype.val '' (e '' (Subtype.val ⁻¹' Set.range (p.tail hlen) :
          Set (Set.Ici (p 1))))) :=
    isMaxChain_of_isMin_head_and_isMaxChain_ici hqbar_min htransport
  -- Rewrite the transported ambient set as the literal range of `tailQ`.
  exact (mapped_tail_range_eq_transport_image (R := R) p hlen I hq).symm ▸ hambient

/-- Helper for Lemma 10.103.9: once the Krull dimension is identified with the natural number
`n`, the source-faithful induction through a principal quotient proves the maximal-chain length
statement. -/
private theorem ringKrullDim_eq_length_of_maximal_prime_chain_of_full_support_cohenMacaulay_of_eq_nat
    (n : ℕ) :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N]
      (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ)
      (p : LTSeries (PrimeSpectrum A)) (hp : IsMaxChain (· ≤ ·) (Set.range p))
      (hdim : ringKrullDim A = n),
      ringKrullDim A = p.length := by
  induction n with
  | zero =>
      intro A _ _ _ N _ _ _ hCM hsupp p hp hdim
      have hlen_le : p.length ≤ ringKrullDim A := by
        simpa using (Order.LTSeries.length_le_krullDim p)
      have hlen_le_zero :
          (((p.length : ℕ∞) : WithBot ℕ∞) ≤ 0) := by
        simpa [hdim] using hlen_le
      have hlen_zero : p.length = 0 := by
        exact Nat.eq_zero_of_le_zero (by exact_mod_cast hlen_le_zero)
      -- In dimension `0`, every strict chain is already trivial.
      simpa [hdim, hlen_zero]
  | succ n ih =>
      intro A _ _ _ N _ _ _ hCM hsupp p hp hdim
      have hsupportDim :
          Module.supportDim A N = ringKrullDim A :=
        supportDim_eq_ringKrullDim_of_support_eq_univ (R := A) (M := N) hsupp
      have hhead_coheight :
          Order.coheight p.head = ringKrullDim A :=
        coheight_head_eq_ringKrullDim_of_full_support_cohenMacaulay
          (R := A) (M := N) hCM hsupp p hp
      have hlen : p.length ≠ 0 := by
        intro hzero
        have hlast_max : IsMax p.last := last_isMax_of_isMaxChain (R := A) p hp
        have hcoheight_last : Order.coheight p.last = 0 :=
          (Order.coheight_eq_zero).2 hlast_max
        have hcoheight_head :
            Order.coheight p.head = 0 := by
          have hlast_eq_head : p.last = p.head := by
            have hlast_idx : (Fin.last p.length : Fin (p.length + 1)) = 0 := by
              ext
              simpa [hzero]
            simpa [RelSeries.last, RelSeries.head] using congrArg p hlast_idx
          simpa [hlast_eq_head] using hcoheight_last
        have hcoheight_head_cast : ((Order.coheight p.head : ℕ∞) : WithBot ℕ∞) = 0 :=
          congrArg (fun t : ℕ∞ ↦ (t : WithBot ℕ∞)) hcoheight_head
        have hdim_zero : ringKrullDim A = 0 := by
          calc
            ringKrullDim A = ((Order.coheight p.head : ℕ∞) : WithBot ℕ∞) := hhead_coheight.symm
            _ = 0 := hcoheight_head_cast
        have : ((n + 1 : ℕ) : WithBot ℕ∞) = (0 : WithBot ℕ∞) := by
          simpa [hdim] using hdim_zero
        have : (n + 1 : ℕ) = 0 := by
          exact_mod_cast this
        exact Nat.succ_ne_zero n this
      obtain ⟨x, hx_mem, hx_max, hx_avoid⟩ :=
        exists_mem_second_prime_avoiding_minimalPrimes (R := A) p hp hlen
      have hhead_min : IsMin p.head := head_isMin_of_isMaxChain (R := A) p hp
      have hx_not_head : x ∉ p.head.asIdeal := by
        exact hx_avoid p.head.asIdeal (PrimeSpectrum.isMin_iff.mp hhead_min)
      have hhead_assoc :
          p.head.asIdeal ∈ associatedPrimes A N :=
        head_mem_associatedPrimes_of_full_support_cohenMacaulay
          (R := A) (M := N) hCM hsupp p hp
      have hsecond_min :
          (p 1).asIdeal ∈ (p.head.asIdeal ⊔ Ideal.span {x}).minimalPrimes :=
        second_prime_mem_minimalPrimes_sup_span_singleton
          (R := A) p hp hlen hx_mem hx_not_head
      obtain ⟨m, hm_pos, hsecond_assoc⟩ :=
        exists_mem_associatedPrimes_quotient_span_singleton_pow_of_mem_minimalPrimes_sup
          (R := A) (M := N) x p.head.asIdeal (p 1).asIdeal hhead_assoc hsecond_min
      let a : A := x ^ m
      let I : Ideal A := Ideal.span ({a} : Set A)
      have ha_max : a ∈ IsLocalRing.maximalIdeal A := by
        simpa [a] using (IsLocalRing.maximalIdeal A).pow_mem_of_mem hx_max m hm_pos
      have ha_mem_second : a ∈ (p 1).asIdeal := by
        simpa [a] using ((p 1).asIdeal).pow_mem_of_mem hx_mem m hm_pos
      have ha_avoid : ∀ q ∈ minimalPrimes A, a ∉ q := by
        intro q hq haq
        apply hx_avoid q hq
        exact (Ideal.minimalPrimes_isPrime hq).mem_of_pow_mem m <| by
          simpa [a] using haq
      have hdim_drop :
          ringKrullDim A = ringKrullDim (A ⧸ I) + 1 := by
        simpa [I] using
          ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes
            (R := A) a ha_max ha_avoid
      have hdrop :
          Module.supportDim A (QuotSMulTop a N) + 1 = Module.supportDim A N := by
        calc
          Module.supportDim A (QuotSMulTop a N) + 1 = ringKrullDim (A ⧸ I) + 1 := by
            rw [supportDim_quotSMulTop_eq_ringKrullDim_quotient_span_singleton_of_full_support
              (R := A) (M := N) hsupp a]
          _ = ringKrullDim A := hdim_drop.symm
          _ = Module.supportDim A N := hsupportDim.symm
      let hTors : Module.IsTorsionBySet A (QuotSMulTop a N) I :=
        (Module.isTorsionBySet_iff_is_torsion_by_span (R := A) (M := QuotSMulTop a N)
          ({a} : Set A)).1 <|
          (Module.isTorsionBySet_singleton_iff (R := A) (M := QuotSMulTop a N) (a := a)).2 <|
            Module.isTorsionBy_quotient_element_smul (M := N) a
      have hI_le_second : I ≤ (p 1).asIdeal := by
        simpa [I] using (Ideal.span_singleton_le_iff_mem ((p 1).asIdeal)).2 ha_mem_second
      have hI_ne_top : I ≠ ⊤ := by
        intro hI_top
        exact (p 1).2.ne_top <| top_le_iff.mp (hI_top ▸ hI_le_second)
      let _ : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne_top
      let _ : IsLocalRing (A ⧸ I) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      let _ : Module (A ⧸ I) (QuotSMulTop a N) := hTors.module
      let _ : IsScalarTower A (A ⧸ I) (QuotSMulTop a N) :=
        Module.IsTorsionBySet.isScalarTower hTors
      let _ : Module.Finite (A ⧸ I) (QuotSMulTop a N) :=
        Module.Finite.of_restrictScalars_finite A (A ⧸ I) (QuotSMulTop a N)
      have hquot_data :
          Module.CohenMacaulay (A ⧸ I) (QuotSMulTop a N) ∧
            Module.support (A ⧸ I) (QuotSMulTop a N) = Set.univ :=
        quotSMulTop_cohenMacaulay_and_full_support_over_principal_quotient
          (R := A) (M := N) ha_max hCM hsupp
          (show Module.supportDim A N = n + 1 by
            calc
              Module.supportDim A N = ringKrullDim A := hsupportDim
              _ = n + 1 := hdim)
          hdrop
      have hq :
          p 1 ∈ PrimeSpectrum.zeroLocus (R := A) I := by
        refine (PrimeSpectrum.mem_zeroLocus (p 1) I).2 ?_
        simpa [I] using (Ideal.span_singleton_le_iff_mem ((p 1).asIdeal)).2 ha_mem_second
      have hqbar_min :
          IsMin ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨p 1, hq⟩) :=
        quotient_head_isMin_of_associated_second_prime
          (R := A) (M := N) (a := a) p I hq hsecond_assoc hquot_data.1 hquot_data.2
      have htail_max :
          IsMaxChain (· ≤ ·) (Set.range (tail_chain_in_quotient (R := A) p hlen I hq)) :=
        mapped_tail_isMaxChain_in_quotient (R := A) p hp hlen I hq hqbar_min
      obtain ⟨mQ, hQ_nat⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (R := A ⧸ I)
      have hmQ_succ : mQ + 1 = n + 1 := by
        have hmQ_succ' :
            (((mQ + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞)) := by
          simpa [hQ_nat, hdim] using hdim_drop.symm
        exact_mod_cast hmQ_succ'
      have hQdim : ringKrullDim (A ⧸ I) = n := by
        have hmQ : mQ = n := by omega
        simpa [hQ_nat, hmQ]
      have htail_dim :
          ringKrullDim (A ⧸ I) =
            (tail_chain_in_quotient (R := A) p hlen I hq).length := by
        exact ih (A := A ⧸ I) (N := QuotSMulTop a N) hquot_data.1 hquot_data.2
          (tail_chain_in_quotient (R := A) p hlen I hq) htail_max hQdim
      have htail_len :
          (tail_chain_in_quotient (R := A) p hlen I hq).length = p.length - 1 := by
        simp [tail_chain_in_quotient]
      -- The quotient chain has length one less, so adding back the head recovers the full chain.
      calc
        ringKrullDim A = ringKrullDim (A ⧸ I) + 1 := hdim_drop
        _ = (tail_chain_in_quotient (R := A) p hlen I hq).length + 1 := by
          rw [htail_dim]
        _ = p.length := by
          rw [htail_len]
          exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hlen))

-- Proof sketch: argue by induction on `ringKrullDim R`. For positive dimension, use prime
-- avoidance to choose `x ∈ p₁` outside the minimal primes, pass to `R / xR` and `M / xM`, apply
-- the Cohen-Macaulay quotient lemmas to keep full support, identify `p₁ / (x)` as a minimal prime
-- of the quotient, and then apply the induction hypothesis to the induced maximal chain there.
/-- Lemma 10.103.9: if `R` is a Noetherian local ring and `M` is a finite `R`-module whose support
is all of `Spec R` and whose depth equals the dimension of its support, then every maximal chain
of prime ideals of `R`, encoded as an `LTSeries` with maximal range, has length `ringKrullDim R`.
-/
theorem ringKrullDim_eq_length_of_maximal_prime_chain_of_full_support_cohenMacaulay
    (hCM : Module.CohenMacaulay R M) (hsupp : Module.support R M = Set.univ)
    (p : LTSeries (PrimeSpectrum R))
    (hp : IsMaxChain (· ≤ ·) (Set.range p)) :
    ringKrullDim R = p.length := by
  obtain ⟨d, hdim⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (R := R)
  -- Route correction: close the proof by the textbook induction on `dim R`, choosing an element in
  -- the second prime, passing to a suitable power quotient, and applying the induction hypothesis
  -- to the transported tail chain in the quotient spectrum.
  exact
    ringKrullDim_eq_length_of_maximal_prime_chain_of_full_support_cohenMacaulay_of_eq_nat
      d hCM hsupp p hp hdim

end
