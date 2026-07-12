import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.SingleHomology
import StacksProject_2024.Chap15.Definition_15_89_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ChainComplex CategoryTheory.Limits
open scoped DirectSum

universe u

/-
Domain-style sampling for ideal-power torsion resolutions:
- primary domain: chain-complex resolutions of modules whose terms are direct sums of ideal-power
  quotients;
- same-domain declarations inspected:
  `QuasiIso`,
  `Module.IsIdealPowerTorsion`,
  `ChainComplex.IsFreeResolution`,
  `ChainComplex.IsFiniteFreeResolution`;
- best owner abstraction: the augmented chain complex data
  `π : F ⟶ moduleSingle[R] M` together with the canonical owner
  `QuasiIso π`; the source-specific extra datum is only the termwise direct-sum-of-quotients
  predicate on `F`;
- primitive data: the augmented chain complex and the degreewise direct-sum-of-quotients property;
- derived API: exactness and surjectivity of the resolution are carried by the canonical
  chain-complex owner `QuasiIso π`, while closure of `Module.IsIdealPowerTorsion` under linear
  equivalence and direct sums belongs to the module owner API rather than to a parallel
  chain-complex-specific wrapper.

Layer triage:
- `source-facing`: the existence of an infinite resolution by direct sums of quotients `R ⧸ I^n`;
- `core/canonical`: the augmented chain-complex owner with `QuasiIso π`;
- `bridge/view`: the termwise predicate recording that each degree is a direct sum of ideal-power
  quotients.

The previous local wrapper duplicated the chain-complex owner `QuasiIso π`. This file should
express the same mathematics directly over the canonical augmentation together with the
source-specific termwise quotient condition, reusing the owner-level `Module.IsIdealPowerTorsion`
API from `Definition_15_89_1` rather than re-declaring it locally.
-/

namespace ChainComplex

/-- A chain complex of `R`-modules is termwise a direct sum of quotients `R ⧸ I^n`, with the
exponent allowed to vary from summand to summand and from degree to degree. The summand index may
live in the module universe of the complex. -/
def IsTermwiseDirectSumOfIdealPowerQuotients
    {R : Type u} [CommRing R] (I : Ideal R) (F : ChainComplex (ModuleCat.{u} R) ℕ) : Prop :=
  ∀ n : ℕ, ∃ (ι : Type u) (exponent : ι → ℕ),
    Nonempty (F.X n ≃ₗ[R] (⨁ j : ι, R ⧸ (I ^ exponent j)))

section

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {F : ChainComplex (ModuleCat.{u} R) ℕ}

namespace IsTermwiseDirectSumOfIdealPowerQuotients

/-- Every term of a chain complex that is a direct sum of quotients `R ⧸ I^n` is `I`-power
torsion. This is derived API from the direct-sum presentation, not additional primitive data. -/
theorem isIdealPowerTorsion
    (hF : F.IsTermwiseDirectSumOfIdealPowerQuotients I) (n : ℕ) :
    Module.IsIdealPowerTorsion I (F.X n) := by
  rcases hF n with ⟨ι, exponent, ⟨e⟩⟩
  have hsum : Module.IsIdealPowerTorsion I (⨁ j : ι, R ⧸ (I ^ exponent j)) :=
    Module.isIdealPowerTorsion_directSum I fun j ↦
      Module.isIdealPowerTorsion_quotient_pow I (exponent j)
  exact (Module.isIdealPowerTorsion_iff_of_linearEquiv I e).2 hsum

end IsTermwiseDirectSumOfIdealPowerQuotients

end

end ChainComplex

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : ModuleCat.{u} R)

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (single₀ (ModuleCat R)) M

/-- Helper for Lemma 15.89.2: the canonical index type for the source-faithful cover of a module
by quotient powers, consisting of an exponent together with an element killed by that power. -/
abbrev ideal_power_cover_index (I : Ideal R) (N : ModuleCat.{u} R) :=
  Σ n : ℕ, Ideal.powerTorsion I N n

/-- Helper for Lemma 15.89.2: the witness-indexed cover uses classical decidable equality on its
index type so that the direct sum is available. -/
noncomputable instance ideal_power_cover_indexDecidableEq (I : Ideal R) (N : ModuleCat.{u} R) :
    DecidableEq (ideal_power_cover_index I N) :=
  Classical.decEq _

/-- Helper for Lemma 15.89.2: the canonical cover object is the direct sum of the quotients
`R ⧸ I^n` indexed by all annihilation witnesses in `N`. -/
abbrev ideal_power_cover_object (I : Ideal R) (N : ModuleCat.{u} R) : ModuleCat.{u} R :=
  ModuleCat.of R (⨁ p : ideal_power_cover_index I N, R ⧸ (I ^ p.1))

/-- Helper for Lemma 15.89.2: an annihilation witness `p` forces `I ^ p.1` to lie in the kernel
of the linear map `r ↦ r • p.2`. -/
theorem ideal_power_cover_component_ker_le
    {N : ModuleCat.{u} R} (p : ideal_power_cover_index I N) :
    I ^ p.1 ≤ (LinearMap.toSpanSingleton R N (p.2 : N)).ker := by
  -- Unpack the torsion witness carried by `p` and rewrite it as a kernel containment.
  intro a ha
  change (a : R) • (p.2 : N) = 0
  have hp : ∀ b : ↥(I ^ p.1), (b : R) • (p.2 : N) = 0 := by
    have hp' : (p.2 : N) ∈ Submodule.torsionBySet R N ↑(I ^ p.1) := p.2.2
    rw [Submodule.mem_torsionBySet_iff] at hp'
    exact hp'
  exact hp ⟨a, ha⟩

/-- Helper for Lemma 15.89.2: each annihilation witness determines the quotient-descended map
`R ⧸ I^n → N` sending the class of `1` to the chosen torsion element. -/
noncomputable def ideal_power_cover_component
    {N : ModuleCat.{u} R} (p : ideal_power_cover_index I N) :
    R ⧸ (I ^ p.1) →ₗ[R] N :=
  (I ^ p.1).liftQ (LinearMap.toSpanSingleton R N (p.2 : N))
    (ideal_power_cover_component_ker_le (I := I) p)

/-- Helper for Lemma 15.89.2: the quotient-descended component map sends the class of `r` to
`r • p.2`. -/
theorem ideal_power_cover_component_mkQ
    {N : ModuleCat.{u} R} (p : ideal_power_cover_index I N) (r : R) :
    ideal_power_cover_component I p ((I ^ p.1).mkQ r) = r • (p.2 : N) := by
  -- Evaluate the descended quotient map on a representative and then unfold the span-singleton map.
  simpa [ideal_power_cover_component, LinearMap.toSpanSingleton_apply] using
    (Submodule.liftQ_apply (p := I ^ p.1)
      (f := LinearMap.toSpanSingleton R N (p.2 : N))
      (h := ideal_power_cover_component_ker_le (I := I) p) r)

/-- Helper for Lemma 15.89.2: the witness-indexed cover object is literally a direct sum of
quotients `R ⧸ I^n`. -/
theorem ideal_power_cover_object_is_directSum
    (N : ModuleCat.{u} R) :
    Nonempty
      (ideal_power_cover_object I N ≃ₗ[R]
        (⨁ p : ideal_power_cover_index I N, R ⧸ (I ^ p.1))) := by
  -- The cover object is already written in the required direct-sum form.
  exact ⟨(LinearEquiv.refl R _ :
    (⨁ p : ideal_power_cover_index I N, R ⧸ (I ^ p.1)) ≃ₗ[R]
      (⨁ p : ideal_power_cover_index I N, R ⧸ (I ^ p.1)))⟩

/-- Helper for Lemma 15.89.2: the direct-sum map obtained by assembling all quotient summand maps
onto `N`. -/
noncomputable def ideal_power_cover_map (I : Ideal R) (N : ModuleCat.{u} R) :
    ideal_power_cover_object I N ⟶ N :=
  ModuleCat.ofHom <|
    DirectSum.toModule R (ideal_power_cover_index I N) N
      (ideal_power_cover_component I)

/-- Helper for Lemma 15.89.2: an `I`-power torsion element of `N` produces one cover index whose
underlying chosen element is exactly that element. -/
theorem exists_ideal_power_cover_index_of_isIdealPowerTorsion
    {N : ModuleCat.{u} R} (hN : Module.IsIdealPowerTorsion I N) (x : N) :
    ∃ p : ideal_power_cover_index I N, (p.2 : N) = x := by
  -- Package the annihilating power for `x` into the canonical sigma-type cover index.
  rw [Module.isIdealPowerTorsion_iff] at hN
  obtain ⟨n, hn⟩ := hN x
  refine ⟨⟨(n : ℕ), ⟨x, ?_⟩⟩, rfl⟩
  rw [Ideal.powerTorsion, Submodule.mem_torsionBySet_iff]
  exact hn

/-- Helper for Lemma 15.89.2: the canonical witness-indexed cover map is surjective on
`I`-power torsion modules. -/
theorem ideal_power_cover_map_surjective
    {N : ModuleCat.{u} R} (hN : Module.IsIdealPowerTorsion I N) :
    Function.Surjective (ideal_power_cover_map I N).hom := by
  -- Hit `x` with the single direct-sum summand indexed by one annihilation witness for `x`.
  intro x
  rcases exists_ideal_power_cover_index_of_isIdealPowerTorsion (I := I) hN x with ⟨p, rfl⟩
  refine ⟨DirectSum.lof R (ideal_power_cover_index I N) (fun q ↦ R ⧸ (I ^ q.1)) p
      ((I ^ p.1).mkQ 1), ?_⟩
  calc
    (ideal_power_cover_map I N).hom
        (DirectSum.lof R (ideal_power_cover_index I N) (fun q ↦ R ⧸ (I ^ q.1)) p
          ((I ^ p.1).mkQ 1)) =
      ideal_power_cover_component I p ((I ^ p.1).mkQ 1) := by
        change
          (DirectSum.toModule R (ideal_power_cover_index I N) N (ideal_power_cover_component I))
              ((DirectSum.lof R (ideal_power_cover_index I N) (fun q ↦ R ⧸ (I ^ q.1)) p) 1) =
            (ideal_power_cover_component I p) 1
        rw [DirectSum.toModule_lof]
    _ = (1 : R) • (p.2 : N) := ideal_power_cover_component_mkQ (I := I) p (1 : R)
    _ = (p.2 : N) := by simp

/-- Helper for Lemma 15.89.2: the canonical witness-indexed cover map is an epimorphism in
`ModuleCat R`. -/
theorem ideal_power_cover_epi
    {N : ModuleCat.{u} R} (hN : Module.IsIdealPowerTorsion I N) :
    Epi (ideal_power_cover_map I N) := by
  -- In `ModuleCat`, surjective linear maps are exactly epimorphisms.
  exact (ModuleCat.epi_iff_surjective _).2
    (ideal_power_cover_map_surjective (I := I) hN)

/-- Helper for Lemma 15.89.2: a submodule of an `I`-power torsion module is again
`I`-power torsion. -/
theorem isIdealPowerTorsion_of_mono
    {A B : ModuleCat.{u} R} (f : A ⟶ B) [Mono f]
    (hB : Module.IsIdealPowerTorsion I B) :
    Module.IsIdealPowerTorsion I A := by
  -- Pull each element of `A` across the injective map and reuse the annihilating power in `B`.
  have hf : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).1 inferInstance
  rw [Module.isIdealPowerTorsion_iff] at hB ⊢
  intro x
  obtain ⟨n, hn⟩ := hB (f.hom x)
  refine ⟨n, fun a ↦ hf ?_⟩
  simpa using hn a

/-- Helper for Lemma 15.89.2: the kernel of a map from an `I`-power torsion module is again
`I`-power torsion. -/
theorem isIdealPowerTorsion_kernel_of_isIdealPowerTorsion
    {A B : ModuleCat.{u} R} (f : A ⟶ B)
    (hA : Module.IsIdealPowerTorsion I A) :
    Module.IsIdealPowerTorsion I (kernel f : ModuleCat.{u} R) := by
  -- The kernel object is a submodule of the source via the canonical monomorphism `kernel.ι`.
  simpa using
    isIdealPowerTorsion_of_mono (I := I) (f := kernel.ι f) hA

/-- Helper for Lemma 15.89.2: every canonical cover object is `I`-power torsion, because it is a
direct sum of quotient modules `R ⧸ I^n`. -/
theorem ideal_power_cover_object_isIdealPowerTorsion
    (N : ModuleCat.{u} R) :
    Module.IsIdealPowerTorsion I (ideal_power_cover_object I N) := by
  -- Rewrite the cover object as its defining direct sum and use termwise torsion of the quotients.
  rcases ideal_power_cover_object_is_directSum (I := I) N with ⟨e⟩
  have hsum :
      Module.IsIdealPowerTorsion I
        (⨁ p : ideal_power_cover_index I N, R ⧸ (I ^ p.1)) :=
    Module.isIdealPowerTorsion_directSum I fun p ↦
      Module.isIdealPowerTorsion_quotient_pow I p.1
  exact (Module.isIdealPowerTorsion_iff_of_linearEquiv I e).2 hsum

/-- Helper for Lemma 15.89.2: the recursive syzygies obtained by repeatedly taking kernels of the
canonical cover maps. -/
noncomputable def ideal_power_recursive_syzygy
    (I : Ideal R) (M : ModuleCat.{u} R) : ℕ → ModuleCat.{u} R
  | 0 => M
  | n + 1 => kernel (ideal_power_cover_map I (ideal_power_recursive_syzygy I M n))

/-- Helper for Lemma 15.89.2: the `n`-th term of the recursive resolution, namely the canonical
cover of the `n`-th syzygy. -/
noncomputable def ideal_power_recursive_cover
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) : ModuleCat.{u} R :=
  ideal_power_cover_object I (ideal_power_recursive_syzygy I M n)

/-- Helper for Lemma 15.89.2: the canonical surjection from the `n`-th cover onto the `n`-th
syzygy. -/
noncomputable def ideal_power_recursive_coverMap
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    ideal_power_recursive_cover I M n ⟶ ideal_power_recursive_syzygy I M n :=
  ideal_power_cover_map I (ideal_power_recursive_syzygy I M n)

/-- Helper for Lemma 15.89.2: the differential is the next cover map followed by the kernel
inclusion into the previous cover. -/
noncomputable def ideal_power_recursive_differential
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    ideal_power_recursive_cover I M (n + 1) ⟶ ideal_power_recursive_cover I M n :=
  ideal_power_recursive_coverMap I M (n + 1) ≫
    kernel.ι (ideal_power_recursive_coverMap I M n)

/-- Helper for Lemma 15.89.2: each recursive differential lands in the kernel of the current
cover map. -/
theorem ideal_power_recursive_differential_comp_coverMap
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    ideal_power_recursive_differential I M n ≫
      ideal_power_recursive_coverMap I M n = 0 := by
  -- Evaluate the kernel relation on an element after applying the next cover map.
  apply ModuleCat.hom_ext
  ext x
  have hk :
      (ideal_power_recursive_coverMap I M n).hom
          ((kernel.ι (ideal_power_recursive_coverMap I M n)).hom
            ((ideal_power_recursive_coverMap I M (n + 1)).hom x)) = 0 := by
    exact LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom
        (kernel.condition (ideal_power_recursive_coverMap I M n)))
      ((ideal_power_recursive_coverMap I M (n + 1)).hom x)
  change
    (ideal_power_recursive_coverMap I M n).hom
        ((kernel.ι (ideal_power_recursive_coverMap I M n)).hom
          ((ideal_power_recursive_coverMap I M (n + 1)).hom x)) = 0
  exact hk

/-- Helper for Lemma 15.89.2: consecutive recursive differentials compose to zero because the
kernel inclusion kills the previous cover map. -/
theorem ideal_power_recursive_differential_sq
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    ideal_power_recursive_differential I M (n + 1) ≫
      ideal_power_recursive_differential I M n = 0 := by
  -- First collapse `d_{n+1} ≫ coverMap_{n+1}` to zero, then postcompose with the kernel
  -- inclusion for stage `n`.
  calc
    ideal_power_recursive_differential I M (n + 1) ≫
        ideal_power_recursive_differential I M n
      =
        (ideal_power_recursive_differential I M (n + 1) ≫
          ideal_power_recursive_coverMap I M (n + 1)) ≫
            kernel.ι (ideal_power_recursive_coverMap I M n) := by
              simpa [ideal_power_recursive_differential, Category.assoc]
    _ = 0 := by
      rw [ideal_power_recursive_differential_comp_coverMap (I := I) (M := M) (n := n + 1)]
      simp

/-- Helper for Lemma 15.89.2: the recursively defined syzygies remain `I`-power torsion. -/
theorem ideal_power_recursive_syzygy_isIdealPowerTorsion
    (hM : Module.IsIdealPowerTorsion I M) :
    ∀ n : ℕ, Module.IsIdealPowerTorsion I (ideal_power_recursive_syzygy I M n)
  | 0 => hM
  | n + 1 => by
      -- The next syzygy is exactly the kernel of the current cover map, so the kernel-torsion
      -- adapter applies directly to the already-torsion cover object.
      simpa [ideal_power_recursive_syzygy] using
        isIdealPowerTorsion_kernel_of_isIdealPowerTorsion
          (I := I)
          (f := ideal_power_recursive_coverMap I M n)
          (ideal_power_cover_object_isIdealPowerTorsion
            (I := I) (ideal_power_recursive_syzygy I M n))

/-- Helper for Lemma 15.89.2: the canonical kernel short complex attached to a recursive cover
stage is exact. -/
theorem ideal_power_recursive_exact_kernel_stage
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    (ShortComplex.mk
      (kernel.ι (ideal_power_recursive_coverMap I M n))
      (ideal_power_recursive_coverMap I M n)
      (kernel.condition (ideal_power_recursive_coverMap I M n))).Exact := by
  -- This is exactly the kernel short complex of the current cover map.
  exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)

/-- Helper for Lemma 15.89.2: covering the kernel of a torsion module surjects onto that kernel,
so the resulting short complex has the same image as the canonical kernel short complex. -/
theorem ideal_power_cover_stage_exact_of_kernel_cover
    {N : ModuleCat.{u} R} (hN : Module.IsIdealPowerTorsion I N) :
    (ShortComplex.mk
      (ideal_power_cover_map I (kernel (ideal_power_cover_map I N)) ≫
        kernel.ι (ideal_power_cover_map I N))
      (ideal_power_cover_map I N)
      (by
        simpa [Category.assoc] using
          kernel.condition (ideal_power_cover_map I N))).Exact := by
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk
      (ideal_power_cover_map I (kernel (ideal_power_cover_map I N)) ≫
        kernel.ι (ideal_power_cover_map I N))
      (ideal_power_cover_map I N)
      (by
        simpa [Category.assoc] using
          kernel.condition (ideal_power_cover_map I N))
  have hKernelTorsion :
      Module.IsIdealPowerTorsion I (kernel (ideal_power_cover_map I N) : ModuleCat.{u} R) :=
    isIdealPowerTorsion_kernel_of_isIdealPowerTorsion
      (I := I) (f := ideal_power_cover_map I N)
      (ideal_power_cover_object_isIdealPowerTorsion (I := I) N)
  have hCoverSurjective :
      Function.Surjective (ideal_power_cover_map I (kernel (ideal_power_cover_map I N))).hom :=
    ideal_power_cover_map_surjective (I := I) hKernelTorsion
  have hKernelExact :
      (ShortComplex.mk
        (kernel.ι (ideal_power_cover_map I N))
        (ideal_power_cover_map I N)
        (kernel.condition (ideal_power_cover_map I N))).Exact := by
    -- The canonical kernel short complex is exact by the universal property of `kernel.ι`.
    exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  have hCompositeRange :
      LinearMap.range
          ((ideal_power_cover_map I (kernel (ideal_power_cover_map I N)) ≫
              kernel.ι (ideal_power_cover_map I N)).hom) =
        LinearMap.range (kernel.ι (ideal_power_cover_map I N)).hom := by
    -- A surjective precomposition does not change the image of the kernel inclusion.
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(ideal_power_cover_map I (kernel (ideal_power_cover_map I N))).hom x, rfl⟩
    · rintro ⟨z, rfl⟩
      rcases hCoverSurjective z with ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  have hKernelRange :
      LinearMap.range (kernel.ι (ideal_power_cover_map I N)).hom =
        LinearMap.ker (ideal_power_cover_map I N).hom := by
    -- The kernel short complex converts the categorical kernel inclusion into the expected
    -- `range = ker` identity on underlying linear maps.
    simpa using ShortComplex.Exact.moduleCat_range_eq_ker hKernelExact
  change S.Exact
  rw [S.moduleCat_exact_iff_range_eq_ker]
  calc
    LinearMap.range
        ((ideal_power_cover_map I (kernel (ideal_power_cover_map I N)) ≫
            kernel.ι (ideal_power_cover_map I N)).hom)
      = LinearMap.range (kernel.ι (ideal_power_cover_map I N)).hom := hCompositeRange
    _ = LinearMap.ker (ideal_power_cover_map I N).hom := hKernelRange

/-- Helper for Lemma 15.89.2: the short complex
`K_{n+1} ⟶ K_n ⟶ S_n` is exact at `K_n`. -/
theorem ideal_power_recursive_cover_stage_exact
    (hM : Module.IsIdealPowerTorsion I M) (n : ℕ) :
    (ShortComplex.mk
      (ideal_power_recursive_differential I M n)
      (ideal_power_recursive_coverMap I M n)
      (by
        exact ideal_power_recursive_differential_comp_coverMap (I := I) (M := M) n)).Exact := by
  -- Specialize the kernel-cover exactness statement to the recursive syzygy `S_n`.
  simpa [ideal_power_recursive_differential, ideal_power_recursive_syzygy, Category.assoc] using
    ideal_power_cover_stage_exact_of_kernel_cover
      (I := I)
      (N := ideal_power_recursive_syzygy I M n)
      (ideal_power_recursive_syzygy_isIdealPowerTorsion (I := I) (M := M) hM n)

/-- Helper for Lemma 15.89.2: the recursive cover objects assemble into the intended chain
complex. -/
noncomputable def ideal_power_recursive_complex
    (I : Ideal R) (M : ModuleCat.{u} R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of
    (ideal_power_recursive_cover I M)
    (ideal_power_recursive_differential I M)
    (ideal_power_recursive_differential_sq I M)

/-- Helper for Lemma 15.89.2: the degree-`0` differential lands in the kernel of the initial
cover map, so it provides the compatibility witness needed to package the augmentation. -/
theorem ideal_power_recursive_augmentation_zero_condition
    (I : Ideal R) (M : ModuleCat.{u} R) :
    ideal_power_recursive_differential I M 0 ≫ ideal_power_recursive_coverMap I M 0 = 0 := by
  -- This is the degree-`0` instance of the same kernel relation used for every recursive
  -- differential, pushed through the left factor `coverMap₁`.
  exact ideal_power_recursive_differential_comp_coverMap (I := I) (M := M) 0

/-- Helper for Lemma 15.89.2: the recursive chain complex carries the obvious augmentation to
`M`, whose degree-`0` component is the first cover map. -/
noncomputable def ideal_power_recursive_augmentation
    (I : Ideal R) (M : ModuleCat.{u} R) :
    ideal_power_recursive_complex I M ⟶ moduleSingle[R] M :=
  (ChainComplex.toSingle₀Equiv
      (ideal_power_recursive_complex I M)
      M).symm
    ⟨ideal_power_recursive_coverMap I M 0, by
      -- The augmentation is determined by its degree-`0` component together with the chain-map
      -- compatibility against the first differential.
      simpa [ideal_power_recursive_complex, ChainComplex.of_d] using
        ideal_power_recursive_augmentation_zero_condition (I := I) (M := M)⟩

/-- Helper for Lemma 15.89.2: the differential of the recursive complex in degree `n` is the
recursively defined cover differential. -/
@[simp]
theorem ideal_power_recursive_complex_d
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    (ideal_power_recursive_complex I M).d (n + 1) n =
      ideal_power_recursive_differential I M n := by
  -- Unfold the `ChainComplex.of` differential in the successor case.
  simp [ideal_power_recursive_complex, ChainComplex.of_d]

/-- Helper for Lemma 15.89.2: the degree-`0` component of the recursive augmentation is the first
cover map. -/
@[simp]
theorem ideal_power_recursive_augmentation_f_zero
    (I : Ideal R) (M : ModuleCat.{u} R) :
    (ideal_power_recursive_augmentation I M).f 0 =
      ideal_power_recursive_coverMap I M 0 := by
  -- Read off the degree-`0` component from the defining `toSingle₀Equiv` packaging.
  simpa [ideal_power_recursive_augmentation] using
    (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
      (C := ideal_power_recursive_complex I M)
      (X := M)
      (f := ideal_power_recursive_coverMap I M 0)
      (hf := by
        simpa [ideal_power_recursive_complex, ChainComplex.of_d] using
          ideal_power_recursive_augmentation_zero_condition (I := I) (M := M)))

/-- Helper for Lemma 15.89.2: the recursive augmentation vanishes in positive degrees because the
target complex is concentrated in degree `0`. -/
@[simp]
theorem ideal_power_recursive_augmentation_f_succ
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    (ideal_power_recursive_augmentation I M).f (n + 1) = 0 := by
  -- Away from degree `0`, the target single complex is zero, so every incoming map vanishes.
  exact
    (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.down ℕ) (0 : ℕ) M (n + 1) (Nat.succ_ne_zero n)).eq_of_tgt _ _

/-- Helper for Lemma 15.89.2: the initial stage `K₁ ⟶ K₀ ⟶ M` is exact at `K₀`, and the
augmentation map `K₀ ⟶ M` is an epimorphism. -/
theorem ideal_power_recursive_zero_stage_exact_and_epi
    (hM : Module.IsIdealPowerTorsion I M) :
    (ShortComplex.mk
      (ideal_power_recursive_differential I M 0)
      (ideal_power_recursive_coverMap I M 0)
      (by
        exact ideal_power_recursive_augmentation_zero_condition (I := I) (M := M))).Exact ∧
      Epi (ideal_power_recursive_coverMap I M 0) := by
  constructor
  · -- The zeroth stage is a specialization of the recursive exactness statement.
    exact ideal_power_recursive_cover_stage_exact (I := I) (M := M) hM 0
  · -- The first cover map is the canonical surjection onto the original torsion module `M`.
    simpa [ideal_power_recursive_coverMap, ideal_power_recursive_syzygy] using
      ideal_power_cover_epi (I := I) (N := M) hM

/-- Helper for Lemma 15.89.2: the degree-zero differential of a single chain complex vanishes
after the canonical identification of degree `0` with the underlying module. -/
private theorem single0_objXSelf_comp_d_eq_zero
    (M : ModuleCat.{u} R) :
    ((moduleSingle[R] M).d 1 0) ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom = 0 := by
  -- The single complex has zero differential from degree `1` to degree `0`.
  rw [HomologicalComplex.single_obj_d]
  simp [ChainComplex.single₀ObjXSelf]
  rfl

/-- Helper for Lemma 15.89.2: on the degree-zero single chain complex, the canonical map from
zeroth opcycles to the module is the descended degree-zero term map. -/
private theorem single0_opcycles_self_inv_eq_descOpcycles
    (M : ModuleCat.{u} R) :
    (HomologicalComplex.singleObjOpcyclesSelfIso
      (ComplexShape.down ℕ) (0 : ℕ) M).inv =
    (moduleSingle[R] M).descOpcycles
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom
      1 (by simp) (single0_objXSelf_comp_d_eq_zero (R := R) M) := by
  -- Both maps out of zeroth opcycles are determined by their composites with `pOpcycles`.
  apply (cancel_epi ((moduleSingle[R] M).pOpcycles 0)).1
  calc
    (moduleSingle[R] M).pOpcycles 0 ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.down ℕ) (0 : ℕ) M).inv =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom := by
          simpa [ChainComplex.single₀ObjXSelf] using
            (HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv
              (c := ComplexShape.down ℕ) (j := (0 : ℕ)) (A := M))
    _ =
      (moduleSingle[R] M).pOpcycles 0 ≫
        (moduleSingle[R] M).descOpcycles
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) (0 : ℕ) M).hom
          1 (by simp) (single0_objXSelf_comp_d_eq_zero (R := R) M) := by
            symm
            simpa using
              (HomologicalComplex.p_descOpcycles
                (K := moduleSingle[R] M)
                (i := (0 : ℕ))
                (k := (HomologicalComplex.singleObjXSelf
                  (ComplexShape.down ℕ) (0 : ℕ) M).hom)
                (j := 1)
                (hj := by simp)
                (hk := single0_objXSelf_comp_d_eq_zero (R := R) M))


/-- Helper for Lemma 15.89.2: the recursive complex is exact in every positive degree. -/
theorem ideal_power_recursive_exactAt_succ
    (hM : Module.IsIdealPowerTorsion I M) (n : ℕ) :
    (ideal_power_recursive_complex I M).ExactAt (n + 1) := by
  have hStage :
      (ShortComplex.mk
        (ideal_power_recursive_differential I M (n + 1))
        (ideal_power_recursive_coverMap I M (n + 1))
        (by
          exact ideal_power_recursive_differential_comp_coverMap (I := I) (M := M) (n + 1))).Exact := by
    -- The stage `K_{n+2} ⟶ K_{n+1} ⟶ S_{n+1}` is exact by the recursive kernel-cover argument.
    exact ideal_power_recursive_cover_stage_exact (I := I) (M := M) hM (n + 1)
  have hStageRangeKer :
      LinearMap.range (ideal_power_recursive_differential I M (n + 1)).hom =
        LinearMap.ker (ideal_power_recursive_coverMap I M (n + 1)).hom := by
    -- Rewrite stage exactness on `ModuleCat` as equality of range and kernel.
    simpa using ShortComplex.Exact.moduleCat_range_eq_ker hStage
  have hKernelComparison :
      LinearMap.ker (ideal_power_recursive_differential I M n).hom =
        LinearMap.ker (ideal_power_recursive_coverMap I M (n + 1)).hom := by
    -- Postcomposing with the injective kernel inclusion does not change the kernel.
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hKernelIotaInjective :
          Function.Injective (kernel.ι (ideal_power_recursive_coverMap I M n)).hom := by
        simpa using
          (ModuleCat.mono_iff_injective
            (kernel.ι (ideal_power_recursive_coverMap I M n))).1 inferInstance
      have hx' :
          (kernel.ι (ideal_power_recursive_coverMap I M n)).hom
              ((ideal_power_recursive_coverMap I M (n + 1)).hom x) =
            (kernel.ι (ideal_power_recursive_coverMap I M n)).hom 0 := by
        simpa [ideal_power_recursive_differential] using hx
      exact hKernelIotaInjective hx'
    · intro hx
      rw [LinearMap.mem_ker] at hx ⊢
      simpa [ideal_power_recursive_differential, hx]
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n]
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  -- Route correction: first use exactness of the stage ending in `S_{n+1}`, then replace
  -- `ker(coverMap_{n+1})` by `ker(d_n)` via injectivity of the kernel inclusion.
    simpa [ideal_power_recursive_complex_d] using
    hStageRangeKer.trans hKernelComparison.symm
  · simp [ChainComplex.prev]
  · exact ChainComplex.next_nat_succ n

/-- Helper for Lemma 15.89.2: the degree-zero differential of the recursive complex composes
trivially with the degree-zero augmentation component. -/
theorem ideal_power_recursive_complex_d_comp_augmentation_f_zero
    (I : Ideal R) (M : ModuleCat.{u} R) :
    (ideal_power_recursive_complex I M).d 1 0 ≫
      (ideal_power_recursive_augmentation I M).f 0 = 0 := by
  -- Rewrite the chain-complex differential and augmentation component back to the recursive
  -- zero stage `K₁ ⟶ K₀ ⟶ M`.
  simpa [ideal_power_recursive_complex_d, ideal_power_recursive_augmentation_f_zero] using
    ideal_power_recursive_augmentation_zero_condition (I := I) (M := M)

/-- Helper for Lemma 15.89.2: the zero-stage exactness-and-epimorphy package expressed in the
augmentation notation used by the degree-zero quasi-isomorphism criterion. -/
theorem ideal_power_recursive_zero_stage_exact_and_epi_for_augmentation
    (hM : Module.IsIdealPowerTorsion I M) :
    (ShortComplex.mk
      ((ideal_power_recursive_complex I M).d 1 0)
      ((ideal_power_recursive_augmentation I M).f 0)
      (ideal_power_recursive_complex_d_comp_augmentation_f_zero (I := I) (M := M))).Exact ∧
      Epi ((ideal_power_recursive_augmentation I M).f 0) := by
  -- The source-faithful zero-stage statement already proves exactness and surjectivity for the
  -- same maps before they were repackaged into the augmentation notation.
  simpa [ideal_power_recursive_complex_d, ideal_power_recursive_augmentation_f_zero] using
    ideal_power_recursive_zero_stage_exact_and_epi (I := I) (M := M) hM

/-- Helper for Lemma 15.89.2: in degree `0`, the recursive augmentation is a quasi-isomorphism. -/
theorem ideal_power_recursive_quasiIsoAt_zero
    (hM : Module.IsIdealPowerTorsion I M) :
    QuasiIsoAt (ideal_power_recursive_augmentation I M) 0 := by
  -- Route correction: reduce degree `0` directly to the short-complex criterion rather than
  -- comparing `descOpcycles` and `homologyMap` by hand.
  rw [ChainComplex.quasiIsoAt₀_iff]
  refine (ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl).2 ?_
  -- The remaining exactness-and-epimorphy statement is exactly the recursive zero stage.
  exact ideal_power_recursive_zero_stage_exact_and_epi_for_augmentation
    (I := I) (M := M) hM

/-- Helper for Lemma 15.89.2: the recursive augmentation is a quasi-isomorphism. -/
theorem ideal_power_recursive_quasiIso
    (hM : Module.IsIdealPowerTorsion I M) :
    QuasiIso (ideal_power_recursive_augmentation I M) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
      -- Degree `0` is the source-faithful augmentation step handled by the short-complex route.
      exact ideal_power_recursive_quasiIsoAt_zero (I := I) (M := M) hM
  | succ n =>
      -- In positive degrees the target `single₀` complex is exact, so quasi-isomorphism reduces
      -- to exactness of the recursive source complex.
      exact
        (quasiIsoAt_iff_exactAt'
          (ideal_power_recursive_augmentation I M)
          (n + 1)
          (ChainComplex.exactAt_succ_single_obj (C := ModuleCat.{u} R) M n)).2
          (ideal_power_recursive_exactAt_succ (I := I) (M := M) hM n)

/-- Helper for Lemma 15.89.2: every term of the recursive complex is literally a direct sum of
quotients `R ⧸ I^n`. -/
theorem ideal_power_recursive_complex_isTermwiseDirectSumOfIdealPowerQuotients :
    (ideal_power_recursive_complex I M).IsTermwiseDirectSumOfIdealPowerQuotients I := by
  intro n
  -- Each degree is, by definition, the canonical cover object of the corresponding syzygy.
  refine ⟨ideal_power_cover_index I (ideal_power_recursive_syzygy I M n), fun p ↦ p.1, ?_⟩
  simpa [ideal_power_recursive_complex, ideal_power_recursive_cover] using
    ideal_power_cover_object_is_directSum
      (I := I) (ideal_power_recursive_syzygy I M n)

-- Proof sketch: for each `m : M`, choose a power `I^(n_m)` annihilating `m` and obtain a
-- canonical surjection from the direct sum of the cyclic quotients `R ⧸ I^(n_m)` onto `M`. Its
-- kernel is again `I`-power torsion, so iterating the same construction yields an exact infinite
-- resolution by such direct sums.
/-- Lemma 15.89.2: an `I`-power torsion `R`-module admits an infinite resolution whose terms are
direct sums of quotients `R ⧸ I^n` with the exponent `n` allowed to vary from summand to summand. -/
theorem exists_infinite_ideal_power_quotient_resolution
    (hM : Module.IsIdealPowerTorsion I M) :
    ∃ (F : ChainComplex (ModuleCat.{u} R) ℕ)
      (π : F ⟶ moduleSingle[R] M),
        QuasiIso π ∧ F.IsTermwiseDirectSumOfIdealPowerQuotients I := by
  -- Route correction: recurse on the single module `M` by taking the kernel of each canonical
  -- cover map, rather than trying to package a functorial resolution on the whole torsion
  -- subcategory.
  -- Package the stabilized recursive complex together with its augmentation and termwise shape.
  refine ⟨ideal_power_recursive_complex I M, ideal_power_recursive_augmentation I M, ?_, ?_⟩
  · exact ideal_power_recursive_quasiIso (I := I) (M := M) hM
  · exact ideal_power_recursive_complex_isTermwiseDirectSumOfIdealPowerQuotients
      (I := I) (M := M)

end
