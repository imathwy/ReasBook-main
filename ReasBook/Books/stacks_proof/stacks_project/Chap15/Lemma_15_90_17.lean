import Mathlib
import Mathlib.CategoryTheory.CommSq
import StacksProject_2024.Chap15.Definition_15_89_1
import StacksProject_2024.Chap15.Proposition_15_90_16
import StacksProject_2024.Chap15.Remark_15_90_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ModuleCat

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: flat base change and formal glueing for module morphisms in `ModuleCat`;
- inspected same-domain owners:
  `CategoryTheory.CommSq`,
  `ModuleCat.extendScalars`,
  `idealPowerTorsionRestrictedBaseChange_isEquivalence`,
  `formalGlueingCan`,
  `formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective`;
- best owner abstraction: the ambient owner is the canonical base-change functor
  `ModuleCat.extendScalars (algebraMap R S)`, while the comparison compatibilities themselves are
  canonically owned by `CategoryTheory.CommSq`; the source-facing content here is only the
  existence of a descended map together with its comparison isomorphism;
- primitive data: a descended `R`-module, the descended morphism, and the comparison
  isomorphism after extension of scalars;
- derived API: the kernel and cokernel comparison isomorphisms, which come from the flat formal
  glueing equivalence and should stay theorem-level output rather than primitive packaged fields.

Source/core/bridge triage:
- `source-facing`: the two existence statements below;
- `core/canonical`: `ModuleCat.extendScalars (algebraMap R S)` and the formal glueing equivalence;
- `bridge/view`: the comparison isomorphism identifying the given `S`-linear map with the base
  change of the descended `R`-linear map.
-/

-- Proof sketch: choose generators `f₁, ..., fₜ` of `I`, regard the localizations of `φ` as an
-- object of the formal glueing category from Remark `15.90.10`, and apply Proposition `15.90.16`
-- to descend `M'` and the localized comparison data to an `R`-module `M`. The induced morphism in
-- the glueing category then comes from a unique `R`-linear map `M ⟶ N`, and Lemma `15.90.3`
-- gives the kernel and cokernel comparison isomorphisms as derived consequences of the chosen
-- descent datum.
/-- Helper for Lemma 15.90.17: if an `S`-module is `(IS)`-power torsion, then localizing it away
from any `r ∈ I` yields the zero object. -/
private theorem away_localization_isZero_of_isIdealPowerTorsion_of_mem
    (I : Ideal R) {K : ModuleCat S} {r : R}
    (hK : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) K) (hr : r ∈ I) :
    IsZero (ModuleCat.of (Localization.Away r) (LocalizedModule.Away r K)) := by
  have hprincipal : Module.IsIdealPowerTorsion (principalIdeal r) K := by
    -- Proof comment: specialize the `(IS)`-power torsion hypothesis to the principal generator
    -- `r`, using that `(algebraMap R S r)^n` lies in `(IS)^n` for every exponent `n`.
    rw [Module.isIdealPowerTorsion_principalIdeal_iff]
    rw [Module.isIdealPowerTorsion_iff] at hK
    intro x
    obtain ⟨n, hn⟩ := hK x
    refine ⟨⟨r ^ (n : ℕ), ⟨(n : ℕ), rfl⟩⟩, ?_⟩
    let a : ↥((Ideal.map (algebraMap R S) I) ^ (n : ℕ)) :=
      ⟨(algebraMap R S r) ^ (n : ℕ), by
        exact Ideal.pow_mem_pow (n : ℕ) (Ideal.mem_map_of_mem (algebraMap R S) hr)⟩
    simpa [a, Algebra.smul_def, map_pow] using hn a
  rw [Module.isIdealPowerTorsion_principalIdeal_iff] at hprincipal
  have hsub : Subsingleton (LocalizedModule.Away r K) := by
    -- Proof comment: powers-of-`r` torsion is exactly the criterion for the away localization to
    -- collapse to a subsingleton module.
    rw [LocalizedModule.subsingleton_iff (S := Submonoid.powers r) (M := K)]
    simpa [Module.IsTorsion'] using hprincipal
  -- Proof comment: a subsingleton module object of `ModuleCat` is the zero object.
  exact
    ModuleCat.isZero_of_subsingleton
      (ModuleCat.of (Localization.Away r) (LocalizedModule.Away r K))

/-- Helper for Lemma 15.90.17: flat extension of scalars identifies the base change of a kernel
with the kernel of the base-changed map. -/
private noncomputable abbrev kernel_baseChange_iso_of_flat
    (hflat : (algebraMap R S).Flat)
    {M N : ModuleCat R} (f : M ⟶ N) :
    (extendScalars (algebraMap R S)).obj (kernel f) ≅
      kernel ((extendScalars (algebraMap R S)).map f) := by
  -- Route correction: use the canonical preserved-kernel comparison for `extendScalars`
  -- instead of rebuilding the kernel comparison by hand.
  let _ : PreservesFiniteLimits (extendScalars (algebraMap R S)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (f := algebraMap R S) hflat
  let _ : Functor.PreservesZeroMorphisms (extendScalars (algebraMap R S)) := by
    infer_instance
  exact PreservesKernel.iso (extendScalars (algebraMap R S)) f

/-- Helper for Lemma 15.90.17: the inverse kernel comparison carries the transported kernel
inclusion to the kernel inclusion of the base-changed map. -/
private theorem kernel_baseChange_iso_of_flat_inv_ι
    (hflat : (algebraMap R S).Flat)
    {M N : ModuleCat R} (f : M ⟶ N) :
    (kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f).inv ≫
        (extendScalars (algebraMap R S)).map (kernel.ι f) =
      kernel.ι ((extendScalars (algebraMap R S)).map f) := by
  -- The generic `PreservesKernel.iso_inv_ι` identity is exactly the required transport rule.
  let _ : PreservesFiniteLimits (extendScalars (algebraMap R S)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (f := algebraMap R S) hflat
  simpa [kernel_baseChange_iso_of_flat] using
    (PreservesKernel.iso_inv_ι (G := extendScalars (algebraMap R S)) f)

/-- Helper for Lemma 15.90.17: extension of scalars identifies the base change of a cokernel with
the cokernel of the base-changed map. -/
private noncomputable abbrev cokernel_baseChange_iso
    {M N : ModuleCat R} (f : M ⟶ N) :
    (extendScalars (algebraMap R S)).obj (cokernel f) ≅
      cokernel ((extendScalars (algebraMap R S)).map f) := by
  let F : ModuleCat R ⥤ ModuleCat S := extendScalars (algebraMap R S)
  let _ : F.PreservesZeroMorphisms := by
    infer_instance
  let hColim :
      IsColimit
        (CokernelCofork.ofπ
          (F.map (cokernel.π f))
          (by
            simpa using congrArg F.map (cokernel.condition f))) := by
    -- Extension of scalars is a left adjoint, so it preserves the cokernel cofork of `f`.
    exact isColimitOfHasCokernelOfPreservesColimit F f
  -- Compare the transported cokernel cofork with the categorical cokernel of the mapped morphism.
  exact
    IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (F.map f))
      hColim

/-- Helper for Lemma 15.90.17: the cokernel base-change comparison carries the transported
quotient map to the cokernel projection of the base-changed map. -/
private theorem cokernel_baseChange_iso_π_hom
    {M N : ModuleCat R} (f : M ⟶ N) :
    (extendScalars (algebraMap R S)).map (cokernel.π f) ≫
        (cokernel_baseChange_iso (R := R) (S := S) f).hom =
      cokernel.π ((extendScalars (algebraMap R S)).map f) := by
  let F : ModuleCat R ⥤ ModuleCat S := extendScalars (algebraMap R S)
  let _ : F.PreservesZeroMorphisms := by
    infer_instance
  let hColim :
      IsColimit
        (CokernelCofork.ofπ
          (F.map (cokernel.π f))
          (by
            simpa using congrArg F.map (cokernel.condition f))) := by
    -- Reuse the preserved cokernel cofork from `cokernel_baseChange_iso`.
    exact isColimitOfHasCokernelOfPreservesColimit F f
  -- The comparison isomorphism is characterized by its effect on the cokernel projection.
  simpa [cokernel_baseChange_iso, hColim] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      hColim
      (cokernelIsCokernel (F.map f))
      WalkingParallelPair.one)

/-- Helper for Lemma 15.90.17: if localizing an `S`-module away from `r` gives the zero object,
then every element is killed by some power of `r`. -/
private theorem powers_torsion_of_away_isZero
    {K : ModuleCat S} {r : R}
    (hK : IsZero (ModuleCat.of (Localization.Away r) (LocalizedModule.Away r K))) :
    ∀ x : K, ∃ s : Submonoid.powers r, s • x = 0 := by
  -- Proof comment: a zero localized module is in particular subsingleton, and the standard
  -- localization criterion rewrites that subsingleton condition as powers-of-`r` torsion.
  have hsub : Subsingleton (LocalizedModule.Away r K) :=
    ModuleCat.subsingleton_of_isZero hK
  intro x
  obtain ⟨s, hs, hsx⟩ :=
    (LocalizedModule.subsingleton_iff (S := Submonoid.powers r) (M := K)).1 hsub x
  exact ⟨⟨s, hs⟩, hsx⟩

/-- Helper for Lemma 15.90.17: every away-localized generator is the corresponding denominator-one
generator scaled by the localized denominator. -/
private theorem away_mk_eq_scalar_smul_mk_one
    {K : ModuleCat S} {r : R} (x : K) (s : Submonoid.powers r) :
    (LocalizedModule.mk x s : LocalizedModule.Away r K) =
      (Localization.mk 1 s : Localization.Away r) •
        (LocalizedModule.mk x (1 : Submonoid.powers r) : LocalizedModule.Away r K) := by
  -- Proof comment: move the denominator into the localization scalar, so surjectivity reduces to
  -- the denominator-one generators.
  simpa [one_smul] using
    (LocalizedModule.mk_smul_mk (R := R) (S := Submonoid.powers r)
      (r := 1) (m := x) (s := s) (t := (1 : Submonoid.powers r))).symm

/-- Helper for Lemma 15.90.17: multiplying a localized generator by its own denominator clears
that denominator. -/
private theorem away_power_smul_mk_eq_mk_one
    {K : ModuleCat S} {r : R} (x : K) (s : Submonoid.powers r) :
    (((s : R) : Localization.Away r) •
        (LocalizedModule.mk x s : LocalizedModule.Away r K)) =
      (LocalizedModule.mk x (1 : Submonoid.powers r) : LocalizedModule.Away r K) := by
  -- Proof comment: this is the standard localization cancellation identity specialized to away
  -- localizations of `R`-modules coming from `S`-modules.
  rw [LocalizedModule.smul'_mk]
  simpa using (LocalizedModule.mk_cancel (s := s) (m := x))

/-- Helper for Lemma 15.90.17: vanishing of the localized kernel forces injectivity of the
localized map. -/
private theorem localized_map_injective_of_zero_kernel
    {A B : ModuleCat S} (φ : A ⟶ B) (r : R)
    (hkerZero :
      IsZero
        (ModuleCat.of (Localization.Away r)
          (LocalizedModule.Away r (kernel (C := ModuleCat S) φ)))) :
    Function.Injective (LocalizedModule.map (Submonoid.powers r) (φ.hom.restrictScalars R)) := by
  let g : LocalizedModule.Away r A →ₗ[Localization.Away r] LocalizedModule.Away r B :=
    LocalizedModule.map (Submonoid.powers r) (φ.hom.restrictScalars R)
  have hkerBot : LinearMap.ker g = ⊥ := by
    apply Submodule.eq_bot_iff.mpr
    intro z hz
    change g z = 0 at hz
    induction z using LocalizedModule.induction_on with
    | _ a s =>
        rw [LocalizedModule.map_mk] at hz
        rw [IsLocalizedModule.mk'_eq_zero'] at hz
        obtain ⟨t, ht⟩ := hz
        let k : kernel φ :=
          ⟨t • a, by
            -- Proof comment: the denominator-cleared numerator lands in the ordinary kernel.
            change φ.hom (t • a) = 0
            simpa [LinearMap.map_smul] using ht⟩
        obtain ⟨u, hu⟩ := powers_torsion_of_away_isZero (K := kernel φ) hkerZero k
        have hua : (u * t) • a = 0 := by
          -- Proof comment: the zero localized kernel kills a further power of `r` on the kernel
          -- element `t • a`, hence on the original numerator after combining denominators.
          simpa [k, smul_smul, mul_comm, mul_left_comm, mul_assoc] using congrArg Subtype.val hu
        rw [IsLocalizedModule.mk'_eq_zero']
        exact ⟨u * t, by simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hua⟩
  -- Proof comment: once the localized kernel is trivial, the localized map is injective.
  exact LinearMap.ker_eq_bot.mp hkerBot

/-- Helper for Lemma 15.90.17: vanishing of the localized cokernel forces surjectivity of the
localized map. -/
private theorem localized_map_surjective_of_zero_cokernel
    {A B : ModuleCat S} (φ : A ⟶ B) (r : R)
    (hcokerZero :
      IsZero
        (ModuleCat.of (Localization.Away r)
          (LocalizedModule.Away r (cokernel (C := ModuleCat S) φ)))) :
    Function.Surjective (LocalizedModule.map (Submonoid.powers r) (φ.hom.restrictScalars R)) := by
  let g : LocalizedModule.Away r A →ₗ[Localization.Away r] LocalizedModule.Away r B :=
    LocalizedModule.map (Submonoid.powers r) (φ.hom.restrictScalars R)
  let q : B →ₗ[R] cokernel φ := (cokernel.π φ).hom.restrictScalars R
  intro z
  induction z using LocalizedModule.induction_on with
  | _ y s =>
      obtain ⟨t, ht⟩ := powers_torsion_of_away_isZero (K := cokernel φ) hcokerZero (q y)
      have hqzero : q (t • y) = 0 := by
        -- Proof comment: the torsion witness in the localized cokernel says the class of `y`
        -- becomes zero after multiplying by a power of `r`.
        simpa [q, LinearMap.map_smul] using ht
      have hmem : t • y ∈ LinearMap.range φ.hom := by
        -- Proof comment: the cokernel is the quotient by the range, so zero class means exactly
        -- that the denominator-cleared numerator already lies in the range.
        rw [← Submodule.ker_mkQ]
        exact LinearMap.mem_ker.mpr (by simpa [q] using hqzero)
      rcases hmem with ⟨x, hx⟩
      have hbase :
          g (LocalizedModule.mk x t : LocalizedModule.Away r A) =
            (LocalizedModule.mk y (1 : Submonoid.powers r) : LocalizedModule.Away r B) := by
        -- Proof comment: `x` maps to the denominator-cleared numerator, and that numerator
        -- localizes to the denominator-one generator by cancellation.
        rw [LocalizedModule.map_mk, hx, ← LocalizedModule.smul'_mk]
        simpa using away_power_smul_mk_eq_mk_one (R := R) (S := S) (x := y) (s := t)
      refine ⟨(Localization.mk 1 s : Localization.Away r) •
          (LocalizedModule.mk x t : LocalizedModule.Away r A), ?_⟩
      calc
        g ((Localization.mk 1 s : Localization.Away r) •
            (LocalizedModule.mk x t : LocalizedModule.Away r A))
            = (Localization.mk 1 s : Localization.Away r) •
                g (LocalizedModule.mk x t : LocalizedModule.Away r A) := by
                  simp
        _ = (Localization.mk 1 s : Localization.Away r) •
              (LocalizedModule.mk y (1 : Submonoid.powers r) : LocalizedModule.Away r B) := by
              rw [hbase]
        _ = (LocalizedModule.mk y s : LocalizedModule.Away r B) := by
              symm
              exact away_mk_eq_scalar_smul_mk_one (R := R) (S := S) (x := y) (s := s)

/-- Helper for Lemma 15.90.17: if the localized kernel and cokernel of `φ` vanish, then the
localized map induced by `φ` is an isomorphism in the owner used by formal glueing. -/
private theorem localized_map_iso_of_zero_kernel_cokernel
    {A B : ModuleCat S} (φ : A ⟶ B) (r : R)
    (hkerZero :
      IsZero
        (ModuleCat.of (Localization.Away r)
          (LocalizedModule.Away r (kernel (C := ModuleCat S) φ))))
    (hcokerZero :
      IsZero
        (ModuleCat.of (Localization.Away r)
          (LocalizedModule.Away r (cokernel (C := ModuleCat S) φ)))) :
    ∃ e :
        ModuleCat.of (Localization.Away r) (LocalizedModule.Away r A) ≅
          ModuleCat.of (Localization.Away r) (LocalizedModule.Away r B),
      e.hom = ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers r) (φ.hom.restrictScalars R)) := by
  let g : LocalizedModule.Away r A →ₗ[Localization.Away r] LocalizedModule.Away r B :=
    LocalizedModule.map (Submonoid.powers r) (φ.hom.restrictScalars R)
  have hbij : Function.Bijective g := by
    refine ⟨?_, ?_⟩
    · -- Proof comment: the localized kernel vanishes, so the localized map is injective.
      exact localized_map_injective_of_zero_kernel (R := R) (S := S) φ r hkerZero
    · -- Proof comment: the localized cokernel vanishes, so every localized target generator lifts.
      exact localized_map_surjective_of_zero_cokernel (R := R) (S := S) φ r hcokerZero
  refine ⟨(LinearEquiv.ofBijective g hbij).toModuleIso, rfl⟩

/-- Helper for Lemma 15.90.17: each generator `f i ∈ I` gives a localized comparison
isomorphism whose forward map is the localized map induced by `φ` followed by the canonical
comparison for `N`. -/
private theorem exists_map_to_glueing_comparison_iso_of_mem
    (I : Ideal R) {t : ℕ} (f : Fin t → R) (hspan : Ideal.span (Set.range f) = I)
    (N : ModuleCat R) (M' : ModuleCat S)
    (φ : M' ⟶ (extendScalars (algebraMap R S)).obj N)
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    (i : Fin t) :
    ∃ e :
        ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M') ≅
          localTensorModuleCat S (f i) (((formalGlueingCan S f).obj N).glue.localModule i),
      e.hom =
        ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers (f i)) (φ.hom.restrictScalars R)) ≫
          (((formalGlueingCan S f).obj N).comparisonIso i).hom := by
  have hfiSpan : f i ∈ Ideal.span (Set.range f) := Ideal.subset_span ⟨i, rfl⟩
  have hfi : f i ∈ I := by
    rw [← hspan]
    exact hfiSpan
  have hkerZero :
      IsZero
        (ModuleCat.of (Localization.Away (f i))
          (LocalizedModule.Away (f i) (kernel (C := ModuleCat S) φ))) :=
    away_localization_isZero_of_isIdealPowerTorsion_of_mem (R := R) (S := S) I hker hfi
  have hcokerZero :
      IsZero
        (ModuleCat.of (Localization.Away (f i))
          (LocalizedModule.Away (f i) (cokernel (C := ModuleCat S) φ))) :=
    away_localization_isZero_of_isIdealPowerTorsion_of_mem (R := R) (S := S) I hcoker hfi
  rcases
      localized_map_iso_of_zero_kernel_cokernel (R := R) (S := S) φ (f i) hkerZero hcokerZero with
    ⟨e, he⟩
  -- Proof comment: after identifying the localized map with an isomorphism, compose with the
  -- canonical comparison isomorphism from the glueing datum attached to `N`.
  refine ⟨e ≪≫ (((formalGlueingCan S f).obj N).comparisonIso i), ?_⟩
  simpa [he, Category.assoc]

/-- Helper for Lemma 15.90.17: choose the localized comparison isomorphism for part `(1)` from the
preceding existence theorem. -/
private noncomputable abbrev map_to_glueing_comparison_iso_of_mem
    (I : Ideal R) {t : ℕ} (f : Fin t → R) (hspan : Ideal.span (Set.range f) = I)
    (N : ModuleCat R) (M' : ModuleCat S)
    (φ : M' ⟶ (extendScalars (algebraMap R S)).obj N)
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    (i : Fin t) :
    ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M') ≅
      localTensorModuleCat S (f i) (((formalGlueingCan S f).obj N).glue.localModule i) :=
  Classical.choose
    (exists_map_to_glueing_comparison_iso_of_mem
      (R := R) (S := S) I f hspan N M' φ hker hcoker i)

/-- Helper for Lemma 15.90.17: the chosen localized comparison isomorphism for part `(1)` has the
expected forward map formula. -/
private theorem map_to_glueing_comparison_iso_of_mem_hom
    (I : Ideal R) {t : ℕ} (f : Fin t → R) (hspan : Ideal.span (Set.range f) = I)
    (N : ModuleCat R) (M' : ModuleCat S)
    (φ : M' ⟶ (extendScalars (algebraMap R S)).obj N)
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    (i : Fin t) :
    (map_to_glueing_comparison_iso_of_mem
        (R := R) (S := S) I f hspan N M' φ hker hcoker i).hom =
      ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers (f i)) (φ.hom.restrictScalars R)) ≫
        (((formalGlueingCan S f).obj N).comparisonIso i).hom :=
  Classical.choose_spec
    (exists_map_to_glueing_comparison_iso_of_mem
      (R := R) (S := S) I f hspan N M' φ hker hcoker i)

/-- Helper for Lemma 15.90.17: each generator `f i ∈ I` gives the localized comparison
isomorphism used to build the part `(2)` glueing datum, with the forward map obtained by first
applying the inverse localized comparison and then the canonical comparison for `M`. -/
private theorem exists_map_from_glueing_comparison_iso_of_mem
    (I : Ideal R) {t : ℕ} (f : Fin t → R) (hspan : Ideal.span (Set.range f) = I)
    (M : ModuleCat R) (N' : ModuleCat S)
    (φ : (extendScalars (algebraMap R S)).obj M ⟶ N')
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    (i : Fin t) :
    ∃ e :
        ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) N') ≅
          localTensorModuleCat S (f i) (((formalGlueingCan S f).obj M).glue.localModule i),
      ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers (f i)) (φ.hom.restrictScalars R)) ≫
          e.hom =
        (((formalGlueingCan S f).obj M).comparisonIso i).hom := by
  have hfiSpan : f i ∈ Ideal.span (Set.range f) := Ideal.subset_span ⟨i, rfl⟩
  have hfi : f i ∈ I := by
    rw [← hspan]
    exact hfiSpan
  have hkerZero :
      IsZero
        (ModuleCat.of (Localization.Away (f i))
          (LocalizedModule.Away (f i) (kernel (C := ModuleCat S) φ))) :=
    away_localization_isZero_of_isIdealPowerTorsion_of_mem (R := R) (S := S) I hker hfi
  have hcokerZero :
      IsZero
        (ModuleCat.of (Localization.Away (f i))
          (LocalizedModule.Away (f i) (cokernel (C := ModuleCat S) φ))) :=
    away_localization_isZero_of_isIdealPowerTorsion_of_mem (R := R) (S := S) I hcoker hfi
  rcases
      localized_map_iso_of_zero_kernel_cokernel (R := R) (S := S) φ (f i) hkerZero hcokerZero with
    ⟨e, he⟩
  -- Proof comment: part `(2)` uses the inverse localized comparison before inserting the
  -- canonical glue-side comparison attached to `M`.
  refine ⟨e.symm ≪≫ (((formalGlueingCan S f).obj M).comparisonIso i), ?_⟩
  have heInv :
      e.symm.hom ≫ ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers (f i)) (φ.hom.restrictScalars R)) =
        𝟙 _ := by
    -- The inverse comparison is defined as the categorical inverse of the localized isomorphism.
    have hcomp := congrArg (fun g ↦ e.symm.hom ≫ g) he
    simpa [Category.assoc] using hcomp
  calc
    ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers (f i)) (φ.hom.restrictScalars R)) ≫
        (e.symm ≪≫ (((formalGlueingCan S f).obj M).comparisonIso i)).hom
        =
          (ModuleCat.ofHom
              (LocalizedModule.map (Submonoid.powers (f i)) (φ.hom.restrictScalars R)) ≫
            e.symm.hom) ≫
              (((formalGlueingCan S f).obj M).comparisonIso i).hom := by
                simp [Category.assoc]
    _ = (𝟙 _) ≫ (((formalGlueingCan S f).obj M).comparisonIso i).hom := by
          rw [heInv]
    _ = (((formalGlueingCan S f).obj M).comparisonIso i).hom := by
          simp

/-- Helper for Lemma 15.90.17: choose the localized comparison isomorphism for part `(2)` from the
preceding existence theorem. -/
private noncomputable abbrev map_from_glueing_comparison_iso_of_mem
    (I : Ideal R) {t : ℕ} (f : Fin t → R) (hspan : Ideal.span (Set.range f) = I)
    (M : ModuleCat R) (N' : ModuleCat S)
    (φ : (extendScalars (algebraMap R S)).obj M ⟶ N')
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    (i : Fin t) :
    ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) N') ≅
      localTensorModuleCat S (f i) (((formalGlueingCan S f).obj M).glue.localModule i) :=
  Classical.choose
    (exists_map_from_glueing_comparison_iso_of_mem
      (R := R) (S := S) I f hspan M N' φ hker hcoker i)

/-- Helper for Lemma 15.90.17: after composing with the localized map induced by `φ`, the chosen
localized comparison for part `(2)` recovers the canonical comparison for `M`. -/
private theorem map_from_glueing_comparison_iso_of_mem_comp_hom
    (I : Ideal R) {t : ℕ} (f : Fin t → R) (hspan : Ideal.span (Set.range f) = I)
    (M : ModuleCat R) (N' : ModuleCat S)
    (φ : (extendScalars (algebraMap R S)).obj M ⟶ N')
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    (i : Fin t) :
    ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers (f i)) (φ.hom.restrictScalars R)) ≫
        (map_from_glueing_comparison_iso_of_mem
          (R := R) (S := S) I f hspan M N' φ hker hcoker i).hom =
      (((formalGlueingCan S f).obj M).comparisonIso i).hom :=
  Classical.choose_spec
    (exists_map_from_glueing_comparison_iso_of_mem
      (R := R) (S := S) I f hspan M N' φ hker hcoker i)

/-- Helper for Lemma 15.90.17: in part `(1)`, the base map `φ` together with identity local maps
defines the comparison square needed for a morphism into the canonical glueing datum of `N`. -/
private theorem map_to_glueing_hom_comparison_comm_of_mem
    (I : Ideal R) {t : ℕ} (f : Fin t → R) (hspan : Ideal.span (Set.range f) = I)
    (N : ModuleCat R) (M' : ModuleCat S)
    (φ : M' ⟶ (extendScalars (algebraMap R S)).obj N)
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    (i : Fin t) :
    CommSq
      (ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i)) (φ.hom.restrictScalars R)))
      (map_to_glueing_comparison_iso_of_mem
        (R := R) (S := S) I f hspan N M' φ hker hcoker i).hom
      (((formalGlueingCan S f).obj N).comparisonIso i).hom
      (𝟙 _) := by
  -- Proof comment: the chosen comparison isomorphism was defined so that its forward map is
  -- exactly the localized map of `φ` followed by the canonical comparison map.
  refine CommSq.mk ?_
  simpa [Category.assoc] using
    map_to_glueing_comparison_iso_of_mem_hom
      (R := R) (S := S) I f hspan N M' φ hker hcoker i

/-- Helper for Lemma 15.90.17: in part `(2)`, the base map `φ` together with identity local maps
defines the comparison square needed for a morphism from the canonical glueing datum of `M`. -/
private theorem map_from_glueing_hom_comparison_comm_of_mem
    (I : Ideal R) {t : ℕ} (f : Fin t → R) (hspan : Ideal.span (Set.range f) = I)
    (M : ModuleCat R) (N' : ModuleCat S)
    (φ : (extendScalars (algebraMap R S)).obj M ⟶ N')
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    (i : Fin t) :
    CommSq
      (ModuleCat.ofHom
        (LocalizedModule.map (Submonoid.powers (f i)) (φ.hom.restrictScalars R)))
      (((formalGlueingCan S f).obj M).comparisonIso i).hom
      (map_from_glueing_comparison_iso_of_mem
        (R := R) (S := S) I f hspan M N' φ hker hcoker i).hom
      (𝟙 _) := by
  -- Proof comment: part `(2)` is the dual square, so composing with the chosen comparison on the
  -- right collapses to the canonical comparison of `M`.
  refine CommSq.mk ?_
  simpa [Category.assoc] using
    map_from_glueing_comparison_iso_of_mem_comp_hom
      (R := R) (S := S) I f hspan M N' φ hker hcoker i

/-- Lemma 15.90.17 (1): let `φ : R → S` be a flat ring map, let `I ⊆ R` be a finitely generated
ideal such that `R ⧸ I → S ⧸ IS` is bijective, and let `M' ⟶ S ⊗[R] N` be an `S`-linear map
whose kernel and cokernel are `IS`-power torsion. Then this map descends to an `R`-linear map
`M ⟶ N` together with an isomorphism `S ⊗[R] M ≅ M'`; the kernel and cokernel comparisons after
base change are derived in the companion theorems below. -/
@[stacks 0ALK]
theorem exists_mapToBaseChangeDescent_of_kernel_cokernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (N : ModuleCat R) (M' : ModuleCat S)
    (φ : M' ⟶ (extendScalars (algebraMap R S)).obj N)
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S)) :
    ∃ (M : ModuleCat R) (f : M ⟶ N)
      (e : (extendScalars (algebraMap R S)).obj M ≅ M'),
      CommSq e.hom ((extendScalars (algebraMap R S)).map f) φ (𝟙 _) := by
  -- TODO: follow Proposition 15.90.16 literally by building a glueing datum with base `M'`,
  -- local pieces from `formalGlueingCan S f N`, and comparison isomorphisms from the localized
  -- isomorphisms of `φ`; the remaining blocker is the explicit localized-isomorphism packaging.
  sorry

/-- Companion to Lemma 15.90.17 (1): once a descent datum `M, f, e` is chosen, the kernel
comparison after base change is canonical. -/
theorem mapToBaseChangeDescent_kernelIso_of_kernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (N : ModuleCat R) (M' : ModuleCat S)
    (φ : M' ⟶ (extendScalars (algebraMap R S)).obj N)
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    {M : ModuleCat R} (f : M ⟶ N)
    (e : (extendScalars (algebraMap R S)).obj M ≅ M')
    (he : CommSq e.hom ((extendScalars (algebraMap R S)).map f) φ (𝟙 _)) :
    ∃ eker : (extendScalars (algebraMap R S)).obj (kernel f) ≅ kernel φ,
      CommSq
        ((extendScalars (algebraMap R S)).map (kernel.ι f))
        eker.hom
        e.hom
        (kernel.ι φ) := by
  let eKerMap :
      kernel ((extendScalars (algebraMap R S)).map f) ≅ kernel φ :=
    kernel.mapIso
      ((extendScalars (algebraMap R S)).map f)
      φ
      e
      (Iso.refl _)
      (by simpa using he.w.symm)
  refine ⟨kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f ≪≫ eKerMap, ?_⟩
  refine CommSq.mk ?_
  -- Proof comment: first rewrite the transported kernel inclusion through flat base change, and
  -- then use the defining property of `kernel.mapIso` for the comparison with `e`.
  have hbase :
      (extendScalars (algebraMap R S)).map (kernel.ι f) =
        (kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f).hom ≫
          kernel.ι ((extendScalars (algebraMap R S)).map f) := by
    have hcomp :=
      congrArg
        (fun g ↦ (kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f).hom ≫ g)
        (kernel_baseChange_iso_of_flat_inv_ι (R := R) (S := S) hflat f)
    simpa [Category.assoc] using hcomp
  have hmap :
      eKerMap.hom ≫ kernel.ι φ =
        kernel.ι ((extendScalars (algebraMap R S)).map f) ≫ e.hom := by
    simp [eKerMap, kernel.mapIso]
  calc
    (extendScalars (algebraMap R S)).map (kernel.ι f) ≫ e.hom
        = ((kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f).hom ≫
            kernel.ι ((extendScalars (algebraMap R S)).map f)) ≫ e.hom := by
            rw [hbase]
    _ = (kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f).hom ≫
          (kernel.ι ((extendScalars (algebraMap R S)).map f) ≫ e.hom) := by
          simp [Category.assoc]
    _ = (kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f).hom ≫
          (eKerMap.hom ≫ kernel.ι φ) := by
          rw [hmap]
    _ = (kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f).hom ≫ eKerMap.hom ≫
          kernel.ι φ := by
          simp [Category.assoc]

/-- Companion to Lemma 15.90.17 (1): once a descent datum `M, f, e` is chosen, the cokernel
comparison after base change is canonical. -/
theorem mapToBaseChangeDescent_cokernelIso_of_cokernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (N : ModuleCat R) (M' : ModuleCat S)
    (φ : M' ⟶ (extendScalars (algebraMap R S)).obj N)
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    {M : ModuleCat R} (f : M ⟶ N)
    (e : (extendScalars (algebraMap R S)).obj M ≅ M')
    (he : CommSq e.hom ((extendScalars (algebraMap R S)).map f) φ (𝟙 _)) :
    ∃ ecoker : (extendScalars (algebraMap R S)).obj (cokernel f) ≅ cokernel φ,
      CommSq
        ((extendScalars (algebraMap R S)).map (cokernel.π f))
        (𝟙 _)
        ecoker.hom
        (cokernel.π φ) := by
  let eCokerMap :
      cokernel ((extendScalars (algebraMap R S)).map f) ≅ cokernel φ :=
    cokernel.mapIso
      ((extendScalars (algebraMap R S)).map f)
      φ
      e
      (Iso.refl _)
      (by simpa using he.w.symm)
  refine ⟨cokernel_baseChange_iso (R := R) (S := S) f ≪≫ eCokerMap, ?_⟩
  refine CommSq.mk ?_
  -- Proof comment: the transported cokernel projection is identified by the preserved-cokernel
  -- comparison, and then `cokernel.mapIso` supplies the final square against `e`.
  have hmap :
      cokernel.π ((extendScalars (algebraMap R S)).map f) ≫ eCokerMap.hom =
        cokernel.π φ := by
    simp [eCokerMap, cokernel.mapIso]
  calc
    (extendScalars (algebraMap R S)).map (cokernel.π f) ≫
        ((cokernel_baseChange_iso (R := R) (S := S) f).hom ≫ eCokerMap.hom)
        = ((extendScalars (algebraMap R S)).map (cokernel.π f) ≫
            (cokernel_baseChange_iso (R := R) (S := S) f).hom) ≫ eCokerMap.hom := by
            simp [Category.assoc]
    _ = cokernel.π ((extendScalars (algebraMap R S)).map f) ≫ eCokerMap.hom := by
          rw [cokernel_baseChange_iso_π_hom (R := R) (S := S) f]
    _ = cokernel.π φ := hmap

-- Proof sketch: localize the map `S ⊗[R] M ⟶ N'` at generators of `I`; each localization is an
-- isomorphism because the kernel and cokernel are `IS`-power torsion. Using the same formal
-- glueing equivalence as in part `(1)`, descend the target `N'` and the localized comparison maps
-- to an `R`-module `N`, and obtain the descended map `M ⟶ N`. Lemma `15.90.3` then identifies the
-- base-changed kernels and cokernels from the chosen descent datum.
/-- Lemma 15.90.17 (2): under the same hypotheses on `R → S` and `I`, let `S ⊗[R] M ⟶ N'` be an
`S`-linear map whose kernel and cokernel are `IS`-power torsion. Then this map descends to an
`R`-linear map `M ⟶ N` together with an isomorphism `S ⊗[R] N ≅ N'`; the kernel and cokernel
comparisons after base change are derived in the companion theorems below. -/
@[stacks 0ALK]
theorem exists_mapFromBaseChangeDescent_of_kernel_cokernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (M : ModuleCat R) (N' : ModuleCat S)
    (φ : (extendScalars (algebraMap R S)).obj M ⟶ N')
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S)) :
    ∃ (N : ModuleCat R) (f : M ⟶ N)
      (e : (extendScalars (algebraMap R S)).obj N ≅ N'),
      CommSq ((extendScalars (algebraMap R S)).map f) φ e.hom (𝟙 _) := by
  -- TODO: apply the same glueing descent as in part `(1)`, but now replace the base object by
  -- `N'` and use the inverses of the localized isomorphisms of `φ` to define the comparison data.
  sorry

/-- Companion to Lemma 15.90.17 (2): once a descent datum `N, f, e` is chosen, the kernel
comparison after base change is canonical. -/
theorem mapFromBaseChangeDescent_kernelIso_of_kernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (M : ModuleCat R) (N' : ModuleCat S)
    (φ : (extendScalars (algebraMap R S)).obj M ⟶ N')
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    {N : ModuleCat R} (f : M ⟶ N)
    (e : (extendScalars (algebraMap R S)).obj N ≅ N')
    (he : CommSq ((extendScalars (algebraMap R S)).map f) φ e.hom (𝟙 _)) :
    ∃ eker : (extendScalars (algebraMap R S)).obj (kernel f) ≅ kernel φ,
      CommSq
        ((extendScalars (algebraMap R S)).map (kernel.ι f))
        eker.hom
        (𝟙 _)
        (kernel.ι φ) := by
  let eKerMap :
      kernel ((extendScalars (algebraMap R S)).map f) ≅ kernel φ :=
    kernel.mapIso
      ((extendScalars (algebraMap R S)).map f)
      φ
      (Iso.refl _)
      e
      (by simpa using he.w)
  refine ⟨kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f ≪≫ eKerMap, ?_⟩
  refine CommSq.mk ?_
  -- Proof comment: the only difference from part `(1)` is that the codomain comparison is now
  -- absorbed into `kernel.mapIso`, so the square closes directly after the base-change rewrite.
  have hbase :
      (extendScalars (algebraMap R S)).map (kernel.ι f) =
        (kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f).hom ≫
          kernel.ι ((extendScalars (algebraMap R S)).map f) := by
    have hcomp :=
      congrArg
        (fun g ↦ (kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f).hom ≫ g)
        (kernel_baseChange_iso_of_flat_inv_ι (R := R) (S := S) hflat f)
    simpa [Category.assoc] using hcomp
  have hmap :
      eKerMap.hom ≫ kernel.ι φ =
        kernel.ι ((extendScalars (algebraMap R S)).map f) := by
    simp [eKerMap, kernel.mapIso]
  calc
    (extendScalars (algebraMap R S)).map (kernel.ι f)
        = (kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f).hom ≫
            kernel.ι ((extendScalars (algebraMap R S)).map f) := hbase
    _ = (kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f).hom ≫
          (eKerMap.hom ≫ kernel.ι φ) := by
          rw [hmap]
    _ = (kernel_baseChange_iso_of_flat (R := R) (S := S) hflat f).hom ≫ eKerMap.hom ≫
          kernel.ι φ := by
          simp [Category.assoc]

/-- Companion to Lemma 15.90.17 (2): once a descent datum `N, f, e` is chosen, the cokernel
comparison after base change is canonical. -/
theorem mapFromBaseChangeDescent_cokernelIso_of_cokernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (M : ModuleCat R) (N' : ModuleCat S)
    (φ : (extendScalars (algebraMap R S)).obj M ⟶ N')
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    {N : ModuleCat R} (f : M ⟶ N)
    (e : (extendScalars (algebraMap R S)).obj N ≅ N')
    (he : CommSq ((extendScalars (algebraMap R S)).map f) φ e.hom (𝟙 _)) :
    ∃ ecoker : (extendScalars (algebraMap R S)).obj (cokernel f) ≅ cokernel φ,
      CommSq
        ((extendScalars (algebraMap R S)).map (cokernel.π f))
        e.hom
        ecoker.hom
        (cokernel.π φ) := by
  let eCokerMap :
      cokernel ((extendScalars (algebraMap R S)).map f) ≅ cokernel φ :=
    cokernel.mapIso
      ((extendScalars (algebraMap R S)).map f)
      φ
      (Iso.refl _)
      e
      (by simpa using he.w)
  refine ⟨cokernel_baseChange_iso (R := R) (S := S) f ≪≫ eCokerMap, ?_⟩
  refine CommSq.mk ?_
  -- Proof comment: this is the same preserved-cokernel transport as in part `(1)`, but now the
  -- comparison square against the base-changed target uses `e` on the left edge.
  have hmap :
      cokernel.π ((extendScalars (algebraMap R S)).map f) ≫ eCokerMap.hom =
        e.hom ≫ cokernel.π φ := by
    simp [eCokerMap, cokernel.mapIso]
  calc
    (extendScalars (algebraMap R S)).map (cokernel.π f) ≫
        ((cokernel_baseChange_iso (R := R) (S := S) f).hom ≫ eCokerMap.hom)
        = ((extendScalars (algebraMap R S)).map (cokernel.π f) ≫
            (cokernel_baseChange_iso (R := R) (S := S) f).hom) ≫ eCokerMap.hom := by
            simp [Category.assoc]
    _ = cokernel.π ((extendScalars (algebraMap R S)).map f) ≫ eCokerMap.hom := by
          rw [cokernel_baseChange_iso_π_hom (R := R) (S := S) f]
    _ = e.hom ≫ cokernel.π φ := hmap

end
