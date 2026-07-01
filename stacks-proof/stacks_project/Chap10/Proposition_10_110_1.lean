import Mathlib
import stacks_project.Chap10.Definition_10_72_1
import stacks_project.Chap10.Definition_10_109_10
import stacks_project.Chap10.Definition_10_157_1
import stacks_project.Chap10.Lemma_10_72_5
import stacks_project.Chap10.Lemma_10_104_9
import stacks_project.Chap10.Lemma_10_106_3
import stacks_project.Chap10.Lemma_10_106_6
import stacks_project.Chap10.Lemma_10_109_6
import stacks_project.Chap10.Lemma_10_109_7
import stacks_project.Chap10.Lemma_10_109_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory ChainComplex
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/-
Domain-style sampling:
* primary domain: projective/global dimension bounds for finite modules over regular local rings;
* sampled owner declarations:
  `HasProjectiveDimensionLE`,
  `HasGlobalDimensionLE`,
  `hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE`,
  `moduleDepth`;
* best owner abstraction: the module-wise bound should first be stated through the canonical owner
  `HasProjectiveDimensionLE (ModuleCat.of R M) n`, while the finite-free-resolution theorem is the
  source-facing bridge supplied by Lemma `10.109.7`;
* source/core/bridge triage:
  the projective-dimension theorem below is `core/canonical`,
  Proposition `10.110.1 (1)` remains `source-facing`,
  and `hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE` is the `bridge/view`;
* primitive data: the ambient regular-local owner `[IsRegularLocalRing R]`, the finite module `M`,
  and the source-faithful numerical equalities `ringKrullDim R = d` and `moduleDepth R M = e`;
* derived API: the finite free resolution of length at most `d - e`.

The proposition does not need a second free-resolution owner. The chapter owner is projective
dimension, and the finite-free-resolution surface is derived from that owner in the local
Noetherian setting.
-/

/-- Helper for Proposition 10.110.1: a maximal Cohen-Macaulay syzygy in a finite free resolution
over a regular local ring becomes a projective syzygy in the associated projective resolution. -/
lemma syzygy_projective_of_maximalCohenMacaulay_syzygy_of_isRegularLocalRing
    {M₀ : Type u} [AddCommGroup M₀] [Module R M₀] [Module.Finite R M₀]
    {F : ChainComplex (ModuleCat R) ℕ} {π : F ⟶ moduleSingle[R] M₀}
    (hπ : ChainComplex.IsFiniteFreeResolution π) {n : ℕ}
    (hsyz : ChainComplex.SyzygyMaximalCohenMacaulay π n) :
    (ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := M₀) π).SyzygyProjective n := by
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  cases n with
  | zero =>
      -- In degree `0`, freeness of the module itself gives the required projectivity.
      let _ : Module.Free R M₀ :=
        free_of_maximalCohenMacaulay_of_isRegularLocalRing (R := R) (M := M₀) hsyz
      simpa [CategoryTheory.ProjectiveResolution.SyzygyProjective] using
        (show Projective (ModuleCat.of R M₀) from inferInstance)
  | succ n =>
      cases n with
      | zero =>
          -- In degree `1`, the first syzygy is the augmentation kernel.
          let _ : Module.Free R (LinearMap.ker (π.f 0).hom) :=
            free_of_maximalCohenMacaulay_of_isRegularLocalRing
              (R := R) (M := LinearMap.ker (π.f 0).hom) hsyz
          simpa [CategoryTheory.ProjectiveResolution.SyzygyProjective] using
            (show Projective (ModuleCat.of R (LinearMap.ker (π.f 0).hom)) from inferInstance)
      | succ k =>
          -- In higher degrees, the source syzygy is the kernel of the corresponding differential.
          let _ : Module.Free R (LinearMap.ker (F.d (k + 1) k).hom) :=
            free_of_maximalCohenMacaulay_of_isRegularLocalRing
              (R := R) (M := LinearMap.ker (F.d (k + 1) k).hom) hsyz
          simpa [CategoryTheory.ProjectiveResolution.SyzygyProjective] using
            (show Projective (ModuleCat.of R (LinearMap.ker (F.d (k + 1) k).hom)) from
              inferInstance)

/-- Helper for Proposition 10.110.1: a proper cyclic quotient over a regular local ring has finite
depth, hence its depth is represented by a natural number. -/
lemma exists_nat_moduleDepth_of_proper_quotient {I : Ideal R} (hI : I ≠ ⊤) :
    ∃ e : ℕ, moduleDepth R (R ⧸ I) = e := by
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R (R ⧸ I)) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := R ⧸ I)
  have hfiniteDepth : moduleDepth R (R ⧸ I) < ⊤ := by
    -- Depth is finite because the maximal ideal does not generate the whole proper quotient.
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top
        (R := R) (I := maximalIdeal R) (M := R ⧸ I) hsmul
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
  exact ⟨e, by simpa using he.symm⟩

/-- Helper for Proposition 10.110.1: every cyclic quotient `R ⧸ I` over a regular local ring of
dimension `d` has projective dimension at most `d`. -/
lemma cyclic_quotient_hasProjectiveDimensionLE_of_isRegularLocalRing
    {d : ℕ} (hdim : ringKrullDim R = d) (I : Ideal R) :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) d := by
  by_cases hI : I = ⊤
  · subst hI
    have hzero :
        Limits.IsZero (ModuleCat.of R (R ⧸ (⊤ : Ideal R))) := by
      exact (ModuleCat.isZero_iff_subsingleton (M := ModuleCat.of R (R ⧸ (⊤ : Ideal R)))).2
        Ideal.Quotient.subsingleton_quotient_top
    have hpd0 :
        HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ (⊤ : Ideal R))) 0 :=
      (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero
        (ModuleCat.of R (R ⧸ (⊤ : Ideal R)))).1 hzero.projective
    let _ : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ (⊤ : Ideal R))) 0 := hpd0
    -- The zero cyclic quotient has projective dimension `0`, hence also `≤ d`.
    exact inferInstance
  · obtain ⟨e, hdepth⟩ := exists_nat_moduleDepth_of_proper_quotient (R := R) hI
    have hpd :
        HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) (d - e) :=
      hasProjectiveDimensionLE_of_moduleDepth_of_isRegularLocalRing
        (R := R) (M := R ⧸ I) hdim hdepth
    let _ : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) (d - e) := hpd
    -- The owner bound is monotone in the integer parameter, so `d - e ≤ d` upgrades the result.
    exact inferInstance

-- Proof sketch: choose the maximal Cohen-Macaulay `(d - e)`th syzygy from Lemma `10.104.9`,
-- make that syzygy free by Lemma `10.106.6`, reinterpret the chosen free resolution as a
-- projective resolution, and then transport the resulting projective-dimension bound back from
-- `Shrink M` to `M`.
/-- Core/canonical form of Proposition 10.110.1 (1): if `R` is a regular local ring of dimension
`d` and `M` is a finite `R`-module of depth `e`, then `M` has projective dimension at most
`d - e`. -/
theorem hasProjectiveDimensionLE_of_moduleDepth_of_isRegularLocalRing
    {d e : ℕ} (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M = e) :
    HasProjectiveDimensionLE (ModuleCat.of R M) (d - e) := by
  let M₀ : Type u := Shrink.{u} M
  let eM : M₀ ≃ₗ[R] M := Shrink.linearEquiv R M
  let _ : Module.Finite R M₀ := Module.Finite.equiv eM.symm
  have hdepth₀ : moduleDepth R M₀ = e := by
    -- Shrinking only changes universes, so the depth equality transports across the linear
    -- equivalence.
    calc
      moduleDepth R M₀ = moduleDepth R M := moduleDepth_eq_of_equiv eM
      _ = e := hdepth
  obtain ⟨F, π, hπ, hsyz⟩ :=
    exists_maximalCohenMacaulay_syzygy_of_moduleDepth
      (R := R) (M := M₀) regularLocalRing_selfModule_cohenMacaulay hdim hdepth₀
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  let P : ProjectiveResolution (ModuleCat.of R M₀) :=
    ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := M₀) π
  have hfinite : ∀ n, Module.Finite R (P.complex.X n) := by
    -- The chosen finite free resolution already records finiteness of every term.
    intro n
    simpa [P] using ChainComplex.IsFiniteFreeResolution.finite π n
  have hsyz_proj : P.SyzygyProjective (d - e) := by
    -- The maximal Cohen-Macaulay top syzygy becomes free, hence projective.
    simpa [P] using
      syzygy_projective_of_maximalCohenMacaulay_syzygy_of_isRegularLocalRing
        (R := R) (M₀ := M₀) hπ hsyz
  have hfinite_length :
      ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms
        (ModuleCat.of R M₀) (d - e) := by
    -- Truncating the projective resolution at the projective syzygy gives the bounded finite
    -- projective resolution required by Lemma `10.109.6`.
    exact
      CategoryTheory.ProjectiveResolution
        .hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_of_syzygyProjective
          (R := R) (M := ModuleCat.of R M₀) (P := P) hfinite hsyz_proj
  have hpd₀ : HasProjectiveDimensionLE (ModuleCat.of R M₀) (d - e) := by
    exact
      (hasProjectiveDimensionLE_iff_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
        (R := R) (M := M₀) (d - e)).2 hfinite_length
  let _ : HasProjectiveDimensionLE (ModuleCat.of R M₀) (d - e) := hpd₀
  -- The projective-dimension bound is invariant under the shrink linear equivalence.
  exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv eM (d - e)

/-- Proposition 10.110.1 (1): if `R` is a regular local ring of dimension `d` and `M` is a finite
`R`-module of depth `e`, then `M` admits a finite free resolution of length at most `d - e`. -/
theorem hasFiniteFreeResolutionLengthLE_of_moduleDepth_of_isRegularLocalRing
    {d e : ℕ} (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M = e) :
    HasFiniteFreeResolutionLengthLE R M (d - e) := by
  exact
    (hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE (d - e)).mp
      (hasProjectiveDimensionLE_of_moduleDepth_of_isRegularLocalRing hdim hdepth)

-- Proof sketch: apply the canonical module-wise bound above to finite modules and then use the
-- finite/cyclic criterion for the owner `HasGlobalDimensionLE R d`.
/-- Proposition 10.110.1 (2): a regular local ring of dimension `d` has global dimension at most
`d`. -/
theorem hasGlobalDimensionLE_of_isRegularLocalRing
    {d : ℕ} (hdim : ringKrullDim R = d) :
    HasGlobalDimensionLE R d := by
  -- Lemma `10.109.12` reduces the global-dimension bound to the cyclic finite modules `R ⧸ I`.
  exact ((globalDimensionLE_tfae_finite_and_cyclic_modules d).out 2 0).mp <| by
    intro I
    exact cyclic_quotient_hasProjectiveDimensionLE_of_isRegularLocalRing (R := R) hdim I

end
