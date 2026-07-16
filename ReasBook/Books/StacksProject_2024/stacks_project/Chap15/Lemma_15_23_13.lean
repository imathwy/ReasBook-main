import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_63_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_72_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.stacks_project.Chap10.Lemma_10_63_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_63_15
import StacksProject_2024.stacks_project.Chap10.Lemma_10_63_18
import StacksProject_2024.stacks_project.Chap10.Lemma_10_72_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_72_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_23_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open LocalizedModule (AtPrime map)
open CategoryTheory
open IsLocalRing
open RingTheory Sequence
open scoped ENat Pointwise

attribute [local instance] RingHomInvPair.of_ringEquiv

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/- Domain triage:
* primary domain: local-to-global isomorphism criteria for finite module maps over Noetherian
  rings, using localized depth and associated primes;
* sampled owner declarations:
  `moduleDepth`,
  `injective_of_injective_localizedMap_at_associatedPrimes`,
  `exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes`,
  `subsingleton_iff_associatedPrimes_eq_empty`;
* best owner abstraction: the local-depth bridge `moduleDepth` together with the owner set
  `associatedPrimes R _`;
* primitive data: the linear map `φ : M →ₗ[R] N` and the primewise disjunction from the source;
* derived API: injectivity via associated-prime localizations and vanishing of the cokernel via
  emptiness of associated primes.

Layering:
* this numbered item is `source-facing`: it is the textbook criterion for when a finite module map
  is an isomorphism from primewise local data;
* the `core/canonical` owners reused here are `moduleDepth` and `associatedPrimes`;
* no extra `bridge/view` wrapper should be introduced in this file.
-/

-- Proof sketch: first apply Lemma `15.23.12` to the kernel to obtain injectivity of `φ`, since
-- bijectivity of the localized map implies injectivity and the second branch excludes associated
-- primes of the codomain. Then replace `N` by a finite submodule containing the image of `M`,
-- form the cokernel `Q`, and analyze its localizations: in the first branch `Qₚ = 0`, while in
-- the second branch Lemmas `10.63.18` and `10.72.6` give `moduleDepth` at least `1` for `Qₚ`.
-- Hence `Q` has no associated primes, so Lemma `10.63.7` forces `Q = 0`, proving surjectivity.
/-- Helper for Lemma 15.23.13: over a Noetherian local ring, if the maximal ideal is associated
to a finite module, then that module has depth `0`. -/
lemma moduleDepth_eq_zero_of_maximalIdeal_mem_associatedPrimes
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Type*} [AddCommGroup L] [Module A L] [Module.Finite A L]
    (hassoc : maximalIdeal A ∈ associatedPrimes A L) :
    moduleDepth A L = 0 := by
  -- An associated maximal ideal bounds the depth by the dimension of the residue field quotient.
  have hle :
      WithBot.some (moduleDepth A L : ℕ∞) ≤
        ringKrullDim (A ⧸ maximalIdeal A) :=
    moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (maximalIdeal A) hassoc
  have hdim : ringKrullDim (A ⧸ maximalIdeal A) = 0 := by
    letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
    exact ringKrullDim_eq_zero_of_field (A ⧸ maximalIdeal A)
  rw [hdim] at hle
  have hdepth_le : moduleDepth A L ≤ 0 := by
    simpa [WithBot.some_eq_coe] using hle
  exact le_antisymm hdepth_le bot_le

/-- Helper for Lemma 15.23.13: localizing a finite module at one of its associated primes gives a
module of depth `0`. -/
lemma moduleDepth_atPrime_eq_zero_of_mem_associatedPrimes
    {L : Type*} [AddCommGroup L] [Module R L] [Module.Finite R L]
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ associatedPrimes R L) :
    moduleDepth (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal L) = 0 := by
  -- Translate to the exact-annihilator API before applying the localization theorem.
  have hp' : p.asIdeal ∈ associatedPrimesOfModule R L := by
    simpa [associatedPrimesOfModule_eq_associatedPrimes] using hp
  have hmax' :
      maximalIdeal (Localization.AtPrime p.asIdeal) ∈
        associatedPrimesOfModule (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal L) := by
    exact mem_associatedPrimesOfModule_atPrime_of_mem_associatedPrimesOfModule hp'
  have hmax :
      maximalIdeal (Localization.AtPrime p.asIdeal) ∈
        associatedPrimes (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal L) := by
    simpa [associatedPrimesOfModule_eq_associatedPrimes] using hmax'
  -- Now apply the local depth-zero criterion at the maximal ideal of `R_p`.
  exact moduleDepth_eq_zero_of_maximalIdeal_mem_associatedPrimes hmax

/-- Helper for Lemma 15.23.13: over a Noetherian local ring, if the maximal ideal is not
associated to a finite module, then that module has depth at least `1`. -/
lemma one_le_moduleDepth_of_maximalIdeal_not_mem_associatedPrimes
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Type*} [AddCommGroup L] [Module A L] [Module.Finite A L]
    (hnot : maximalIdeal A ∉ associatedPrimes A L) :
    (1 : ℕ∞) ≤ moduleDepth A L := by
  by_cases htop : maximalIdeal A • (⊤ : Submodule A L) = ⊤
  · rw [show moduleDepth A L = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal A) L htop]
    simp
  · have hnot_le : ∀ q ∈ associatedPrimes A L, ¬ maximalIdeal A ≤ q := by
      intro q hq hle
      have hq_le : q ≤ maximalIdeal A := by
        exact IsLocalRing.le_maximalIdeal (AssociatedPrimes.mem_iff.mp hq).isPrime.ne_top
      have hq_eq : q = maximalIdeal A := le_antisymm hq_le hle
      exact hnot <| hq_eq ▸ hq
    have hL : Nontrivial L := by
      by_contra hL
      letI : Subsingleton L := not_nontrivial_iff_subsingleton.mp hL
      apply htop
      ext l
      simp [Subsingleton.elim l 0]
    obtain ⟨x, hx, hreg⟩ :=
      (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes
        (R := A) (M := L) (I := maximalIdeal A)).2 hnot_le
    rw [show moduleDepth A L = sSup (Ideal.regularSequenceLengths (maximalIdeal A) L) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) L htop]
    refine le_sSup ?_
    refine ⟨[x], ?_, ?_, by simp⟩
    · exact RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal L
        (by
          intro r hr
          simpa [List.mem_singleton.mp hr] using hx)
        ((RingTheory.Sequence.isWeaklyRegular_singleton_iff L x).2 hreg)
    · simpa using hx

/-- Helper for Lemma 15.23.13: if a prime is not associated to a module, then after localizing at
that prime the maximal ideal is still not associated, so the localized depth is at least `1`. -/
lemma one_le_moduleDepth_atPrime_of_not_mem_associatedPrimes
    {L : Type*} [AddCommGroup L] [Module R L] [Module.Finite R L]
    (p : PrimeSpectrum R) (hp : p.asIdeal ∉ associatedPrimes R L) :
    (1 : ℕ∞) ≤ moduleDepth (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal L) := by
  -- If the localized maximal ideal were associated, the converse localization theorem would pull
  -- it back to an associated prime of the original module.
  have hnot_loc :
      maximalIdeal (Localization.AtPrime p.asIdeal) ∉
        associatedPrimes (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal L) := by
    intro hloc
    have hloc' :
        maximalIdeal (Localization.AtPrime p.asIdeal) ∈
        associatedPrimesOfModule (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal L) := by
      simpa [associatedPrimesOfModule_eq_associatedPrimes] using hloc
    have hp' : p.asIdeal ∈ associatedPrimesOfModule R L := by
      exact
        mem_associatedPrimesOfModule_of_mem_associatedPrimesOfModule_atPrime_of_fg hloc'
          p.asIdeal.fg_of_isNoetherianRing
    have hp'' : p.asIdeal ∈ associatedPrimes R L := by
      simpa [associatedPrimesOfModule_eq_associatedPrimes] using hp'
    exact hp hp''
  -- The local positive-depth criterion now applies in the localized ring.
  exact one_le_moduleDepth_of_maximalIdeal_not_mem_associatedPrimes hnot_loc

/-- Helper for Lemma 15.23.13: an exact-annihilator witness remains a witness in the cyclic
submodule it generates. -/
lemma exists_mem_associatedPrimes_span_singleton_of_isAssociatedToModule
    {Q : Type*} [AddCommGroup Q] [Module R Q] {p : Ideal R}
    (hp : Ideal.IsAssociatedToModule R Q p) :
    ∃ q : Q, p ∈ associatedPrimes R (R ∙ q) := by
  rw [Ideal.isAssociatedToModule_iff_exists_torsionOf] at hp
  rcases hp with ⟨hpPrime, q, hq⟩
  have hqSingleton : q ∈ ({q} : Set Q) := by
    simp
  have hqMem : q ∈ (R ∙ q : Submodule R Q) := by
    exact Submodule.subset_span hqSingleton
  let qK : R ∙ q := ⟨q, hqMem⟩
  have hqK : p = Ideal.torsionOf R (R ∙ q) qK := by
    ext r
    rw [hq, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
    change (r • q = 0) ↔ (r • qK = 0)
    constructor
    · intro hr
      apply Subtype.ext
      simpa using hr
    · intro hr
      simpa using congrArg Subtype.val hr
  have hp' : p ∈ associatedPrimesOfModule R (R ∙ q) := by
    rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf]
    exact ⟨hpPrime, qK, hqK⟩
  exact ⟨q, by simpa [associatedPrimesOfModule_eq_associatedPrimes] using hp'⟩

/-- Helper for Lemma 15.23.13: the preimage in `N` of the cyclic submodule generated by a cokernel
class fits into an exact sequence `M → P → K`. -/
lemma preimage_span_exact_of_cokernel_witness
    (φ : M →ₗ[R] N) (hφinj : Function.Injective φ) (q : N ⧸ LinearMap.range φ) :
    let K : Submodule R (N ⧸ LinearMap.range φ) := R ∙ q
    let P : Submodule R N := K.comap (Submodule.mkQ (LinearMap.range φ))
    ∃ φP : M →ₗ[R] P, ∃ π : P →ₗ[R] K,
      Function.Injective φP ∧ Function.Exact φP π ∧ Function.Surjective π := by
  let K : Submodule R (N ⧸ LinearMap.range φ) := R ∙ q
  let P : Submodule R N := K.comap (Submodule.mkQ (LinearMap.range φ))
  have hφP_mem : ∀ m : M, φ m ∈ P := by
    intro m
    change Submodule.mkQ (LinearMap.range φ) (φ m) ∈ K
    have hzero : Submodule.mkQ (LinearMap.range φ) (φ m) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range φ)).2 (LinearMap.mem_range_self φ m)
    simpa [hzero] using (Submodule.zero_mem K)
  let φP : M →ₗ[R] P := LinearMap.codRestrict P φ hφP_mem
  have hπ_mem : ∀ y : P, (Submodule.mkQ (LinearMap.range φ)) y.1 ∈ K := by
    intro y
    exact y.2
  let π : P →ₗ[R] K :=
    LinearMap.codRestrict K ((Submodule.mkQ (LinearMap.range φ)).comp P.subtype) hπ_mem
  have hφP_inj : Function.Injective φP := by
    intro m₁ m₂ hm
    apply hφinj
    exact congrArg Subtype.val hm
  have hexact : Function.Exact φP π := by
    intro y
    constructor
    · intro hy
      have hy' : Submodule.mkQ (LinearMap.range φ) (y : N) = 0 := by
        simpa [π] using congrArg Subtype.val hy
      have hyRange : (y : N) ∈ LinearMap.range φ := by
        exact (Submodule.Quotient.mk_eq_zero (LinearMap.range φ)).1 hy'
      rcases hyRange with ⟨m, hm⟩
      exact ⟨m, Subtype.ext hm⟩
    · rintro ⟨m, hm⟩
      rw [← hm]
      apply Subtype.ext
      simpa [π, φP] using
        (Submodule.Quotient.mk_eq_zero (LinearMap.range φ)).2 (LinearMap.mem_range_self φ m)
  have hπ_surj : Function.Surjective π := by
    intro k
    obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (LinearMap.range φ) k.1
    have hyP : y ∈ P := by
      change Submodule.mkQ (LinearMap.range φ) y ∈ K
      simpa [hy] using k.2
    refine ⟨⟨y, hyP⟩, ?_⟩
    exact Subtype.ext hy
  exact ⟨φP, π, hφP_inj, hexact, hπ_surj⟩

/-- Helper for Lemma 15.23.13: linear equivalences preserve regular-sequence lengths over a fixed
ring, which is the key invariant underlying depth. -/
lemma regularSequenceLengths_eq_of_equiv_local
    {A : Type*} [CommRing A]
    {X : Type*} [AddCommGroup X] [Module A X]
    {Y : Type*} [AddCommGroup Y] [Module A Y]
    (I : Ideal A) (e : X ≃ₗ[A] Y) :
    Ideal.regularSequenceLengths I X = Ideal.regularSequenceLengths I Y := by
  -- Transport regular sequences across the linear equivalence without changing their lengths.
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

/-- Helper for Lemma 15.23.13: linear equivalences preserve module depth over a local ring. This
is the rewrite bridge used to remove the `ULift` packaging after applying Lemma `10.72.6`. -/
lemma moduleDepth_eq_of_equiv_local
    {A : Type*} [CommRing A] [IsLocalRing A]
    {X : Type*} [AddCommGroup X] [Module A X] [Module.Finite A X]
    {Y : Type*} [AddCommGroup Y] [Module A Y] [Module.Finite A Y]
    (e : X ≃ₗ[A] Y) :
    moduleDepth A X = moduleDepth A Y := by
  have htop :
      maximalIdeal A • (⊤ : Submodule A X) = ⊤ ↔
        maximalIdeal A • (⊤ : Submodule A Y) = ⊤ := by
    constructor
    · intro h
      have := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using this
    · intro h
      have := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using this
  by_cases hX : maximalIdeal A • (⊤ : Submodule A X) = ⊤
  · -- The top-depth case is preserved because the maximal-ideal action transports across `e`.
    rw [show moduleDepth A X = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal A) X hX]
    rw [show moduleDepth A Y = ⊤ from
      Ideal.depth_eq_top_of_smul_top (maximalIdeal A) Y (htop.mp hX)]
  · -- In the finite-depth case, both sides are the same supremum of regular-sequence lengths.
    rw [show moduleDepth A X = sSup (Ideal.regularSequenceLengths (maximalIdeal A) X) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) X hX]
    rw [show moduleDepth A Y = sSup (Ideal.regularSequenceLengths (maximalIdeal A) Y) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) Y (mt htop.mpr hX)]
    rw [regularSequenceLengths_eq_of_equiv_local (maximalIdeal A) e]

/-- Helper for Lemma 15.23.13: package a presented exact row into a short complex whose objects
all lie in one chosen universe by conjugating the maps with `ULift.moduleEquiv`. -/
abbrev shortComplexOfShortExact_ulift
    {A : Type u} [CommRing A]
    {X : Type v} [AddCommGroup X] [Module A X]
    {Y Z : Type w} [AddCommGroup Y] [Module A Y] [AddCommGroup Z] [Module A Z]
    (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (hExact : Function.Exact f g) :
    ShortComplex (ModuleCat.{max u v w} A) :=
  ShortComplex.moduleCatMk
    ((((ULift.moduleEquiv : ULift.{max u v w, w} Y ≃ₗ[A] Y).symm.toLinearMap :
        Y →ₗ[A] ULift.{max u v w, w} Y).comp
      (f.comp ((ULift.moduleEquiv : ULift.{max u v w, v} X ≃ₗ[A] X).toLinearMap :
        ULift.{max u v w, v} X →ₗ[A] X))))
    ((((ULift.moduleEquiv : ULift.{max u v w, w} Z ≃ₗ[A] Z).symm.toLinearMap :
        Z →ₗ[A] ULift.{max u v w, w} Z).comp
      (g.comp ((ULift.moduleEquiv : ULift.{max u v w, w} Y ≃ₗ[A] Y).toLinearMap :
        ULift.{max u v w, w} Y →ₗ[A] Y))))
    <| by
      ext x
      simp
      simpa using congr_fun hExact.comp_eq_zero (ULift.down x)

/-- Helper for Lemma 15.23.13: the ULift-packaged short complex is short exact whenever the
original row is exact with injective left map and surjective right map. -/
lemma shortComplexOfShortExact_ulift_shortExact
    {A : Type u} [CommRing A]
    {X : Type v} [AddCommGroup X] [Module A X]
    {Y Z : Type w} [AddCommGroup Y] [Module A Y] [AddCommGroup Z] [Module A Z]
    (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (hExact : Function.Exact f g)
    (hInj : Function.Injective f) (hSurj : Function.Surjective g) :
    (shortComplexOfShortExact_ulift (A := A) (X := X) (Y := Y) (Z := Z) f g hExact).ShortExact := by
  have hExact' : (shortComplexOfShortExact_ulift (A := A) (X := X) (Y := Y) (Z := Z)
      f g hExact).Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (shortComplexOfShortExact_ulift (A := A) (X := X) (Y := Y) (Z := Z) f g hExact)]
    intro y
    constructor
    · intro hy
      have hyUp : ULift.up (g y.down) = 0 := by
        simpa [shortComplexOfShortExact_ulift] using hy
      have hy' : g y.down = 0 := by
        simpa using congrArg ULift.down hyUp
      obtain ⟨x, hx⟩ := (hExact y.down).1 hy'
      refine ⟨⟨x⟩, ?_⟩
      change ULift.up (f x) = y
      apply ULift.ext
      simpa using hx
    · rintro ⟨x, rfl⟩
      change ULift.up (g (f x.down)) = 0
      apply ULift.ext
      simpa using congr_fun hExact.comp_eq_zero x.down
  have hMono : Mono (shortComplexOfShortExact_ulift (A := A) (X := X) (Y := Y) (Z := Z)
      f g hExact).f := by
    rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    change ULift.up (f x.down) = ULift.up (f y.down) at hxy
    apply ULift.ext
    apply hInj
    simpa using congrArg ULift.down hxy
  have hEpi : Epi (shortComplexOfShortExact_ulift (A := A) (X := X) (Y := Y) (Z := Z)
      f g hExact).g := by
    rw [ModuleCat.epi_iff_surjective]
    intro z
    obtain ⟨y, hy⟩ := hSurj z.down
    refine ⟨⟨y⟩, ?_⟩
    change ULift.up (g y) = z
    apply ULift.ext
    simpa using hy
  exact ShortComplex.ShortExact.mk' hExact' hMono hEpi

/-- Helper for Lemma 15.23.13: a `ULift` of a local ring is still local. -/
lemma isLocalRing_ulift
    {A : Type u} [CommRing A] [IsLocalRing A] :
    IsLocalRing (ULift.{w, u} A) := by
  -- Transport locality across the surjective ring equivalence `A ≃ ULift A`.
  exact
    IsLocalRing.of_surjective'
      ((ULift.ringEquiv.symm : A ≃+* ULift.{w, u} A).toRingHom)
      (ULift.ringEquiv.symm : A ≃+* ULift.{w, u} A).surjective

/-- Helper for Lemma 15.23.13: a `ULift` of a Noetherian ring is still Noetherian. -/
lemma isNoetherianRing_ulift
    {A : Type u} [CommRing A] [IsNoetherianRing A] :
    IsNoetherianRing (ULift.{w, u} A) := by
  -- Transport the Noetherian self-module condition across the ring equivalence `A ≃ ULift A`.
  letI :
      RingHomInvPair
        ((ULift.ringEquiv.symm : A ≃+* ULift.{w, u} A).toRingHom)
        ((ULift.ringEquiv : ULift.{w, u} A ≃+* A).toRingHom) :=
    RingHomInvPair.of_ringEquiv (ULift.ringEquiv.symm : A ≃+* ULift.{w, u} A)
  letI :
      RingHomInvPair
        ((ULift.ringEquiv : ULift.{w, u} A ≃+* A).toRingHom)
        ((ULift.ringEquiv.symm : A ≃+* ULift.{w, u} A).toRingHom) :=
    RingHomInvPair.of_ringEquiv (ULift.ringEquiv : ULift.{w, u} A ≃+* A)
  rw [isNoetherianRing_iff]
  let hA : IsNoetherian A A := (isNoetherianRing_iff).mp inferInstance
  let e : A ≃ₛₗ[((ULift.ringEquiv.symm : A ≃+* ULift.{w, u} A).toRingHom)] ULift.{w, u} A :=
    (ULift.ringEquiv.symm : A ≃+* ULift.{w, u} A).toSemilinearEquiv
  exact isNoetherian_of_linearEquiv e

/-- Helper for Lemma 15.23.13: restricting scalars along `ULift.ringEquiv` preserves finite
generation of a module. -/
lemma moduleFinite_ulift_ring_compHom
    {A : Type u} [CommRing A]
    {X : Type v} [AddCommGroup X] [Module A X] [Module.Finite A X] :
    let _ : Module (ULift.{w, u} A) X :=
      Module.compHom X (ULift.ringEquiv.toRingHom : ULift.{w, u} A →+* A)
    Module.Finite (ULift.{w, u} A) X := by
  -- View the identity map as semilinear for `A → ULift A` and push finite generation across it.
  letI : Module (ULift.{w, u} A) X :=
    Module.compHom X (ULift.ringEquiv.toRingHom : ULift.{w, u} A →+* A)
  letI :
      RingHomSurjective ((ULift.ringEquiv.symm : A ≃+* ULift.{w, u} A).toRingHom) :=
    RingHomSurjective.mk (ULift.ringEquiv.symm : A ≃+* ULift.{w, u} A).surjective
  let f : X →ₛₗ[((ULift.ringEquiv.symm : A ≃+* ULift.{w, u} A).toRingHom)] X := by
    refine LinearMap.mk ?_ ?_
    · exact AddHom.mk (fun x ↦ x) (fun x y ↦ rfl)
    · intro a x
      rfl
  have hsurj : Function.Surjective f := by
    -- The semilinear identity map is obviously surjective.
    intro x
    refine ⟨x, ?_⟩
    change x = x
    rfl
  exact Module.Finite.of_surjective f hsurj

/-- Helper for Lemma 15.23.13: mapping a finite list of `ULift A` scalars down along the ring
equivalence sends the corresponding finitely generated ideal to the ideal generated by the mapped
list. -/
lemma ideal_ofList_map_ulift_ringEquiv
    {A : Type u} [CommRing A] (rs : List (ULift.{w, u} A)) :
    Ideal.map (ULift.ringEquiv : ULift.{w, u} A ≃+* A) (Ideal.ofList rs) =
      Ideal.ofList (rs.map ULift.down) := by
  -- Rewrite both ideals as spans and compare the image of the generating set explicitly.
  rw [Ideal.ofList, Ideal.ofList, Ideal.map_span]
  have hs : (⇑ULift.ringEquiv '' {r | r ∈ rs} : Set A) = {r | r ∈ rs.map ULift.down} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      refine ⟨⟨x⟩, ?_, rfl⟩
      simpa using hx
  rw [hs]

/-- Helper for Lemma 15.23.13: after changing the ring from `A` to `ULift A` by `Module.compHom`,
an `A`-linear map is still linear for the lifted scalar action. -/
lemma compatibleSmul_ulift_ring_compHom
    {A : Type u} [CommRing A]
    {X : Type v} [AddCommGroup X] [Module A X]
    {Y : Type w} [AddCommGroup Y] [Module A Y] :
    let _ : Module (ULift.{max u v w, u} A) X :=
      Module.compHom X (ULift.ringEquiv.toRingHom : ULift.{max u v w, u} A →+* A)
    let _ : Module (ULift.{max u v w, u} A) Y :=
      Module.compHom Y (ULift.ringEquiv.toRingHom : ULift.{max u v w, u} A →+* A)
    LinearMap.CompatibleSMul X Y (ULift.{max u v w, u} A) A := by
  -- The lifted scalar action is literally the old action after taking `ULift.down`.
  letI : Module (ULift.{max u v w, u} A) X :=
    Module.compHom X (ULift.ringEquiv.toRingHom : ULift.{max u v w, u} A →+* A)
  letI : Module (ULift.{max u v w, u} A) Y :=
    Module.compHom Y (ULift.ringEquiv.toRingHom : ULift.{max u v w, u} A →+* A)
  refine ⟨?_⟩
  intro f c x
  change f (c.down • x) = c.down • f x
  simp

/-- Helper for Lemma 15.23.13: for the `Module.compHom` action of `ULift A` on a finite
`A`-module, the maximal-ideal Nakayama condition `𝔪 • ⊤ = ⊤` is unchanged. -/
lemma maximalIdeal_smul_top_iff_ulift_ring_compHom
    {A : Type u} [CommRing A] [IsLocalRing A]
    {T : Type v} [AddCommGroup T] [Module A T] [Module.Finite A T] :
    let _ : IsLocalRing (ULift.{w, u} A) := isLocalRing_ulift (A := A)
    let _ : Module (ULift.{w, u} A) T :=
      Module.compHom T (ULift.ringEquiv.toRingHom : ULift.{w, u} A →+* A)
    let _ : Module.Finite (ULift.{w, u} A) T := moduleFinite_ulift_ring_compHom (A := A) (X := T)
    (maximalIdeal (ULift.{w, u} A)) • (⊤ : Submodule (ULift.{w, u} A) T) = ⊤ ↔
      (maximalIdeal A) • (⊤ : Submodule A T) = ⊤ := by
  letI : IsLocalRing (ULift.{w, u} A) := isLocalRing_ulift (A := A)
  letI : Module (ULift.{w, u} A) T :=
    Module.compHom T (ULift.ringEquiv.toRingHom : ULift.{w, u} A →+* A)
  letI : Module.Finite (ULift.{w, u} A) T := moduleFinite_ulift_ring_compHom (A := A) (X := T)
  constructor
  · intro htop
    -- Nakayama over the lifted local ring forces the common additive group `T` to be trivial.
    have hJac : maximalIdeal (ULift.{w, u} A) ≤ Ring.jacobson (ULift.{w, u} A) := by
      simpa [Ideal.jacobson_bot] using
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal (ULift.{w, u} A)))
    letI : Subsingleton T :=
      subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson
        (R := ULift.{w, u} A) (M := T) (I := maximalIdeal (ULift.{w, u} A)) htop hJac
    -- In a subsingleton module every submodule equals `⊤`, so the original Nakayama condition holds.
    ext x
    simp [Subsingleton.elim x 0]
  · intro htop
    -- The same Nakayama argument in the original local ring again trivializes the additive group.
    have hJac : maximalIdeal A ≤ Ring.jacobson A := by
      simpa [Ideal.jacobson_bot] using
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A))
    letI : Subsingleton T :=
      subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson
        (R := A) (M := T) (I := maximalIdeal A) htop hJac
    -- After restricting scalars along `ULift.ringEquiv`, the same trivial module satisfies
    -- `𝔪 • ⊤ = ⊤` for the lifted scalar action as well.
    ext x
    simp [Subsingleton.elim x 0]

/-- Helper for Lemma 15.23.13: a short exact sequence of finite modules over a Noetherian local
ring yields the standard lower bound on the depth of the quotient module, even when the three
modules live in different universes. -/
lemma moduleDepth_right_ge_min_of_exact_injective_surjective
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Type v} [AddCommGroup X] [Module A X] [Module.Finite A X]
    {Y Z : Type w} [AddCommGroup Y] [Module A Y] [Module.Finite A Y]
    [AddCommGroup Z] [Module A Z] [Module.Finite A Z]
    (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z)
    (hExact : Function.Exact f g) (hInj : Function.Injective f) (hSurj : Function.Surjective g) :
    moduleDepth A Z ≥ min (moduleDepth A Y) (moduleDepth A X - 1) := by
  -- Route correction: shrink the three finite modules down to the ring universe, apply the
  -- Chapter 10 short-exact owner there, and then transport the resulting depth inequality back
  -- along the canonical `Shrink.linearEquiv` equivalences.
  let _ : Small.{u} A := small_self A
  letI : Small.{u} X := Module.Finite.small (R := A) (M := X)
  letI : Small.{u} Y := Module.Finite.small (R := A) (M := Y)
  letI : Small.{u} Z := Module.Finite.small (R := A) (M := Z)
  let eX : Shrink.{u} X ≃ₗ[A] X := Shrink.linearEquiv A X
  let eY : Shrink.{u} Y ≃ₗ[A] Y := Shrink.linearEquiv A Y
  let eZ : Shrink.{u} Z ≃ₗ[A] Z := Shrink.linearEquiv A Z
  let fShrink : Shrink.{u} X →ₗ[A] Shrink.{u} Y :=
    eY.symm.toLinearMap.comp (f.comp eX.toLinearMap)
  let gShrink : Shrink.{u} Y →ₗ[A] Shrink.{u} Z :=
    eZ.symm.toLinearMap.comp (g.comp eY.toLinearMap)
  have hExactShrink : Function.Exact fShrink gShrink := by
    intro y
    constructor
    · intro hy
      have hy' : g (eY y) = 0 := by
        have hy'' : eZ (gShrink y) = eZ 0 := congrArg eZ hy
        simpa [gShrink, LinearMap.comp_apply] using hy''
      obtain ⟨x, hx⟩ := (hExact (eY y)).1 hy'
      refine ⟨eX.symm x, ?_⟩
      apply eY.injective
      simpa [fShrink, LinearMap.comp_apply] using hx
    · rintro ⟨x, rfl⟩
      have hcomp : eZ (gShrink (fShrink x)) = eZ 0 := by
        simp [gShrink, fShrink, LinearMap.comp_apply]
        simpa using congr_fun hExact.comp_eq_zero (eX x)
      exact eZ.injective hcomp
  have hInjShrink : Function.Injective fShrink := by
    intro x₁ x₂ hxx
    have hxx' : eY (fShrink x₁) = eY (fShrink x₂) := congrArg eY hxx
    have hfx : f (eX x₁) = f (eX x₂) := by
      simpa [fShrink, LinearMap.comp_apply] using hxx'
    exact eX.injective (hInj hfx)
  have hSurjShrink : Function.Surjective gShrink := by
    intro z
    obtain ⟨y, hy⟩ := hSurj (eZ z)
    refine ⟨eY.symm y, ?_⟩
    apply eZ.injective
    simpa [gShrink, LinearMap.comp_apply] using hy
  have hfiniteX : Module.Finite A (Shrink.{u, v} X) := Module.Finite.equiv eX.symm
  have hfiniteY : Module.Finite A (Shrink.{u, w} Y) := Module.Finite.equiv eY.symm
  have hfiniteZ : Module.Finite A (Shrink.{u, w} Z) := Module.Finite.equiv eZ.symm
  letI : Module.Finite A (Shrink.{u, v} X) := hfiniteX
  letI : Module.Finite A (Shrink.{u, w} Y) := hfiniteY
  letI : Module.Finite A (Shrink.{u, w} Z) := hfiniteZ
  let eUX : ULift.{u, u} (Shrink.{u, v} X) ≃ₗ[A] Shrink.{u, v} X := ULift.moduleEquiv
  let eUY : ULift.{u, u} (Shrink.{u, w} Y) ≃ₗ[A] Shrink.{u, w} Y := ULift.moduleEquiv
  let eUZ : ULift.{u, u} (Shrink.{u, w} Z) ≃ₗ[A] Shrink.{u, w} Z := ULift.moduleEquiv
  letI : Module A (ULift.{u, u} (Shrink.{u, v} X)) := inferInstance
  letI : Module A (ULift.{u, u} (Shrink.{u, w} Y)) := inferInstance
  letI : Module A (ULift.{u, u} (Shrink.{u, w} Z)) := inferInstance
  letI : Module.Finite A (ULift.{u, u} (Shrink.{u, v} X)) := Module.Finite.equiv eUX.symm
  letI : Module.Finite A (ULift.{u, u} (Shrink.{u, w} Y)) := Module.Finite.equiv eUY.symm
  letI : Module.Finite A (ULift.{u, u} (Shrink.{u, w} Z)) := Module.Finite.equiv eUZ.symm
  let S : ShortComplex (ModuleCat.{u} A) :=
    shortComplexOfShortExact_ulift
      (A := A) (X := Shrink.{u, v} X) (Y := Shrink.{u, w} Y) (Z := Shrink.{u, w} Z)
      fShrink gShrink hExactShrink
  letI : Module.Finite A S.X₁ := by
    change Module.Finite A (ULift.{u, u} (Shrink.{u, v} X))
    exact Module.Finite.equiv eUX.symm
  letI : Module.Finite A S.X₃ := by
    change Module.Finite A (ULift.{u, u} (Shrink.{u, w} Z))
    exact Module.Finite.equiv eUZ.symm
  have hShortExact :
      S.ShortExact := by
    exact shortComplexOfShortExact_ulift_shortExact
      (A := A) (X := Shrink.{u, v} X) (Y := Shrink.{u, w} Y) (Z := Shrink.{u, w} Z)
      fShrink gShrink hExactShrink hInjShrink hSurjShrink
  have hShrink :
      moduleDepth A (ULift.{u, u} (Shrink.{u, w} Z)) ≥
        min (moduleDepth A (ULift.{u, u} (Shrink.{u, w} Y)))
          (moduleDepth A (ULift.{u, u} (Shrink.{u, v} X)) - 1) := by
    -- The owner theorem now applies after the final harmless ULift packaging inside universe `u`.
    simpa using
      (CategoryTheory.ShortComplex.ShortExact.moduleDepth_right_ge_min (R := A) (S := S) hShortExact)
  -- Finally, remove first the ULift packaging and then the shrink packaging.
  simpa [moduleDepth_eq_of_equiv_local eUZ, moduleDepth_eq_of_equiv_local eUY,
    moduleDepth_eq_of_equiv_local eUX, moduleDepth_eq_of_equiv_local eZ,
    moduleDepth_eq_of_equiv_local eY, moduleDepth_eq_of_equiv_local eX] using hShrink

/-- Helper for Lemma 15.23.13: if the quotient depth is bounded below by the usual short-exact
minimum, and the other two depths are at least `1` and `2`, then the quotient depth is at least
`1`. -/
lemma one_le_of_depth_right_bound {a b c : ℕ∞}
    (hbound : c ≥ min a (b - 1)) (ha : (1 : ℕ∞) ≤ a) (hb : (2 : ℕ∞) ≤ b) :
    (1 : ℕ∞) ≤ c := by
  have hb' : (1 : ℕ∞) ≤ b - 1 := by
    by_cases htop : b = ⊤
    · simp [htop]
    · have hb_nat : (2 : ℕ) ≤ ENat.toNat b := by
        exact ENat.toNat_le_toNat hb htop
      have hb_nat' : (1 : ℕ) ≤ ENat.toNat b - 1 := by
        omega
      -- Reduce to the finite `ENat` case via `toNat`.
      rw [← ENat.coe_toNat htop]
      have hb_nat'' : ((1 : ℕ) : ℕ∞) ≤ ((ENat.toNat b - 1 : ℕ) : ℕ∞) := by
        exact_mod_cast hb_nat'
      simpa using hb_nat''
  have hmin : (1 : ℕ∞) ≤ min a (b - 1) := by
    -- Both entries of the minimum are already at least `1`.
    exact le_min ha hb'
  exact hmin.trans hbound

/-- Lemma 15.23.13: let `R` be a Noetherian ring and let `φ : M → N` be a map of `R`-modules with
`M` finite. If for every prime `p` of `R` either the localized map `Mₚ → Nₚ` is an isomorphism,
or the localized module `Mₚ` has depth at least `2` and `p` is not an associated prime of `N`,
then `φ` is an isomorphism. -/
theorem bijective_of_localizedMap_bijective_or_depth_localizedModule_ge_two_and_not_mem_associatedPrimes
    (φ : M →ₗ[R] N)
    (hφ : ∀ p : PrimeSpectrum R,
      Function.Bijective (map p.asIdeal.primeCompl φ) ∨
        ((2 : ℕ∞) ≤
            moduleDepth (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M) ∧
          p.asIdeal ∉ associatedPrimes R N)) :
    Function.Bijective φ := by
  -- First prove injectivity by ruling out the depth branch on associated primes of `M`.
  have hloc_inj : ∀ p : associatedPrimes R M,
      Function.Injective (map ((p : Ideal R).primeCompl) φ) := by
    intro p
    let pp : PrimeSpectrum R := ⟨(p : Ideal R), (AssociatedPrimes.mem_iff.mp p.2).isPrime⟩
    rcases hφ pp with hbij | hdepth
    · simpa [pp] using hbij.1
    · have hzero :
        moduleDepth (Localization.AtPrime pp.asIdeal) (AtPrime pp.asIdeal M) = 0 :=
        moduleDepth_atPrime_eq_zero_of_mem_associatedPrimes pp p.2
      have hnot_two : ¬ ((2 : ℕ∞) ≤
          moduleDepth (Localization.AtPrime pp.asIdeal) (AtPrime pp.asIdeal M)) := by
        simpa [hzero]
      exact (hnot_two hdepth.1).elim
  have hφinj : Function.Injective φ :=
    injective_of_injective_localizedMap_at_associatedPrimes φ hloc_inj
  -- Now analyze the cokernel `Q = N / range φ` and show it has no associated primes.
  let Q : Type w := N ⧸ LinearMap.range φ
  by_cases hQsub : Subsingleton Q
  · -- If the cokernel is zero, the quotient map is trivial and `φ` is surjective.
    have hsurj : Function.Surjective φ := by
      intro n
      have hzeroQ : (Submodule.mkQ (LinearMap.range φ)) n = 0 := by
        letI : Subsingleton Q := hQsub
        exact Subsingleton.elim _ _
      have hnRange : n ∈ LinearMap.range φ := by
        exact (Submodule.Quotient.mk_eq_zero (LinearMap.range φ)).1 hzeroQ
      rcases hnRange with ⟨m, hm⟩
      exact ⟨m, hm⟩
    exact ⟨hφinj, hsurj⟩
  · -- Pick an associated prime of the nonzero cokernel and generate a finite cyclic submodule.
    letI : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hQsub
    obtain ⟨p, hpQ⟩ := associatedPrimes.nonempty R Q
    have hpQ' : p ∈ associatedPrimesOfModule R Q := by
      simpa [associatedPrimesOfModule_eq_associatedPrimes] using hpQ
    have hpAssoc : Ideal.IsAssociatedToModule R Q p := by
      exact (mem_associatedPrimesOfModule_iff (R := R) (M := Q) p).mp hpQ'
    obtain ⟨q, hqK⟩ := exists_mem_associatedPrimes_span_singleton_of_isAssociatedToModule hpAssoc
    let K : Submodule R Q := R ∙ q
    let P : Submodule R N := K.comap (Submodule.mkQ (LinearMap.range φ))
    have hKfg : K.FG := by
      simpa [K] using (Submodule.fg_span_singleton q : (R ∙ q : Submodule R Q).FG)
    letI : Module.Finite R K := Module.Finite.of_fg hKfg
    have hpK : p ∈ associatedPrimes R K := by
      simpa [K] using hqK
    letI : p.IsPrime := (AssociatedPrimes.mem_iff.mp hpQ).isPrime
    let pp : PrimeSpectrum R := ⟨p, (AssociatedPrimes.mem_iff.mp hpQ).isPrime⟩
    have hKloc :
        maximalIdeal (Localization.AtPrime p) ∈
          associatedPrimes (Localization.AtPrime p) (AtPrime p K) := by
      have hpK' : p ∈ associatedPrimesOfModule R K := by
        simpa [associatedPrimesOfModule_eq_associatedPrimes] using hpK
      have hloc' :
          maximalIdeal (Localization.AtPrime p) ∈
            associatedPrimesOfModule (Localization.AtPrime p) (AtPrime p K) := by
        exact mem_associatedPrimesOfModule_atPrime_of_mem_associatedPrimesOfModule hpK'
      simpa [associatedPrimesOfModule_eq_associatedPrimes] using hloc'
    -- Route correction: the quotient term must be controlled via localized depth, not via the
    -- middle-term associated-prime inclusion, because the available exact-sequence API only
    -- constrains associated primes of the middle object.
    rcases hφ pp with hbij | hdepth
    · -- If `φ_p` is bijective, the localized cokernel vanishes, so the localized cyclic submodule
      -- also vanishes, contradicting the localized associated-prime witness.
      have hmkQ_exact : Function.Exact φ (Submodule.mkQ (LinearMap.range φ)) := by
        rw [LinearMap.exact_iff, Submodule.ker_mkQ]
      have hmkQ_exact_loc :
          Function.Exact (LocalizedModule.map p.primeCompl φ)
            (LocalizedModule.map p.primeCompl (Submodule.mkQ (LinearMap.range φ))) := by
        exact LocalizedModule.map_exact p.primeCompl φ
          (Submodule.mkQ (LinearMap.range φ)) hmkQ_exact
      have hmkQ_loc_surj :
          Function.Surjective
            (LocalizedModule.map p.primeCompl (Submodule.mkQ (LinearMap.range φ))) := by
        exact LocalizedModule.map_surjective p.primeCompl
          (Submodule.mkQ (LinearMap.range φ)) (Submodule.mkQ_surjective _)
      have hmkQ_loc_zero :
          LocalizedModule.map p.primeCompl (Submodule.mkQ (LinearMap.range φ)) = 0 := by
        have hker :
            LinearMap.ker
                (LocalizedModule.map p.primeCompl (Submodule.mkQ (LinearMap.range φ))) = ⊤ := by
          calc
            LinearMap.ker
                (LocalizedModule.map p.primeCompl (Submodule.mkQ (LinearMap.range φ))) =
                LinearMap.range (LocalizedModule.map p.primeCompl φ) :=
                  LinearMap.exact_iff.mp hmkQ_exact_loc
            _ = ⊤ := LinearMap.range_eq_top.2 hbij.2
        ext z
        have hz :
            z ∈ LinearMap.ker
              (LocalizedModule.map p.primeCompl (Submodule.mkQ (LinearMap.range φ))) := by
          rw [hker]
          simp
        exact (LinearMap.mem_ker.mp hz)
      have hQloc_sub : Subsingleton (AtPrime p Q) := by
        refine ⟨fun a b ↦ ?_⟩
        obtain ⟨x, rfl⟩ := hmkQ_loc_surj a
        obtain ⟨y, rfl⟩ := hmkQ_loc_surj b
        simp [hmkQ_loc_zero]
      have hKloc_sub : Subsingleton (AtPrime p K) := by
        letI : Subsingleton (AtPrime p Q) := hQloc_sub
        exact (LocalizedModule.map_injective p.primeCompl K.subtype K.subtype_injective).subsingleton
      have hKloc_empty :
          associatedPrimes (Localization.AtPrime p) (AtPrime p K) = ∅ := by
        simpa using
          (subsingleton_iff_associatedPrimes_eq_empty
            (R := Localization.AtPrime p) (M := AtPrime p K)).1 hKloc_sub
      have hfalse :
          maximalIdeal (Localization.AtPrime p) ∈
            (∅ : Set (Ideal (Localization.AtPrime p))) := by
        simpa [hKloc_empty] using hKloc
      exact hfalse.elim
    · -- In the depth branch, pass to the finite cyclic submodule `K` and its preimage `P`.
      obtain ⟨φP, π, hφP_inj, hpreExact, hπ_surj⟩ :=
        preimage_span_exact_of_cokernel_witness φ hφinj q
      letI : Module.Finite R P := Module.Finite.of_exact hpreExact hπ_surj
      have hPloc_pos :
          (1 : ℕ∞) ≤ moduleDepth (Localization.AtPrime p) (AtPrime p P) := by
        have hP_not_assoc : p ∉ associatedPrimes R P := by
          intro hpP
          exact hdepth.2 <| associatedPrimes.subset_of_injective P.subtype_injective hpP
        exact one_le_moduleDepth_atPrime_of_not_mem_associatedPrimes pp hP_not_assoc
      have hφP_exact_loc :
          Function.Exact
            (LocalizedModule.map p.primeCompl φP) (LocalizedModule.map p.primeCompl π) := by
        exact LocalizedModule.map_exact p.primeCompl φP π hpreExact
      have hφP_inj_loc :
          Function.Injective (LocalizedModule.map p.primeCompl φP) := by
        exact LocalizedModule.map_injective p.primeCompl φP hφP_inj
      have hπ_surj_loc :
          Function.Surjective (LocalizedModule.map p.primeCompl π) := by
        exact LocalizedModule.map_surjective p.primeCompl π hπ_surj
      have hKdepth :
          moduleDepth (Localization.AtPrime p) (AtPrime p K) ≥
            min (moduleDepth (Localization.AtPrime p) (AtPrime p P))
              (moduleDepth (Localization.AtPrime p) (AtPrime p M) - 1) := by
        -- Package the localized exact sequence into a common module universe before applying the
        -- Chapter 10 depth inequality for short exact sequences.
        exact moduleDepth_right_ge_min_of_exact_injective_surjective
          (LocalizedModule.map p.primeCompl φP)
          (LocalizedModule.map p.primeCompl π)
          hφP_exact_loc hφP_inj_loc hπ_surj_loc
      have hKloc_pos :
          (1 : ℕ∞) ≤ moduleDepth (Localization.AtPrime p) (AtPrime p K) := by
        -- The left and middle localized terms already have depths at least `2` and `1`.
        exact one_le_of_depth_right_bound hKdepth hPloc_pos hdepth.1
      have hKloc_zero :
          moduleDepth (Localization.AtPrime p) (AtPrime p K) = 0 :=
        moduleDepth_atPrime_eq_zero_of_mem_associatedPrimes pp hpK
      -- The localized cyclic cokernel cannot simultaneously have depth `0` and positive depth.
      simpa [hKloc_zero] using hKloc_pos

end
