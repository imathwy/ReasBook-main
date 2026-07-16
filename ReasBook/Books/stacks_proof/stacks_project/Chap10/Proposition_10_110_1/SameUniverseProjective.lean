import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_72_1
import stacks_proof.stacks_project.Chap10.Definition_10_109_10
import stacks_proof.stacks_project.Chap10.Definition_10_157_1
import stacks_proof.stacks_project.Chap10.Lemma_10_72_5
import stacks_proof.stacks_project.Chap10.Lemma_10_104_9
import stacks_proof.stacks_project.Chap10.Lemma_10_106_3
import stacks_proof.stacks_project.Chap10.Lemma_10_106_6
import stacks_proof.stacks_project.Chap10.Lemma_10_107_14
import stacks_proof.stacks_project.Chap10.Lemma_10_109_6
import stacks_proof.stacks_project.Chap10.Lemma_10_109_7
import stacks_proof.stacks_project.Chap10.Lemma_10_109_12

universe u v

open CategoryTheory ChainComplex
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/-- Helper for Proposition 10.110.1: a maximal Cohen-Macaulay syzygy in a finite free resolution
over a regular local ring becomes a projective syzygy in the associated projective resolution. -/
lemma syzygy_projective_of_maximalCohenMacaulay_syzygy_of_isRegularLocalRing
    {M₀ : Type u} [AddCommGroup M₀] [Module R M₀] [Module.Finite R M₀]
    {F : ChainComplex (ModuleCat R) ℕ} {π : F ⟶ moduleSingle[R]M₀}
    (hπ : ChainComplex.IsFiniteFreeResolution π) {n : ℕ}
    (hsyz : ChainComplex.SyzygyMaximalCohenMacaulay π n) :
    let P : ProjectiveResolution (ModuleCat.of R M₀) :=
      ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := M₀) (F := F) π
    P.SyzygyProjective n := by
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

/-- Helper for Proposition 10.110.1: in the ring universe, the source-faithful
maximal-Cohen-Macaulay syzygy argument gives the canonical projective-dimension bound. -/
lemma hasProjectiveDimensionLE_of_moduleDepth_of_isRegularLocalRing_same_universe
    {M₀ : Type u} [AddCommGroup M₀] [Module R M₀] [Module.Finite R M₀]
    {d e : ℕ} (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M₀ = e) :
    HasProjectiveDimensionLE (ModuleCat.of R M₀) (d - e) := by
  obtain ⟨F, π, hπ, hsyz⟩ :=
    exists_maximalCohenMacaulay_syzygy_of_moduleDepth
      (R := R) (M := M₀) regularLocalRing_selfModule_cohenMacaulay hdim hdepth
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  let P : ProjectiveResolution (ModuleCat.of R M₀) :=
    ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := M₀) (F := F) π
  have hfinite : ∀ n, Module.Finite R (P.complex.X n) := by
    intro n
    -- The chosen finite free resolution already has finite terms in every degree.
    simpa [P] using ChainComplex.IsFiniteFreeResolution.finite π n
  have hsyz_projective : P.SyzygyProjective (d - e) := by
    -- The source syzygy is maximal Cohen-Macaulay, hence free and therefore projective.
    simpa [P] using
      syzygy_projective_of_maximalCohenMacaulay_syzygy_of_isRegularLocalRing
        (R := R) (M₀ := M₀) (F := F) hπ hsyz
  have hfinite_projective :
      ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms
        (ModuleCat.of R M₀) (d - e) := by
    -- Lemma `10.109.6` truncates the projective resolution at the projective top syzygy.
    simpa [P] using
      CategoryTheory.ProjectiveResolution.hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_of_syzygyProjective
        (R := R) (M := ModuleCat.of R M₀) (P := P) hfinite hsyz_projective
  -- Convert the bounded finite-projective resolution back to the canonical owner statement.
  exact
    (hasProjectiveDimensionLE_iff_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
      (R := R) (M := M₀) (d - e)).mpr hfinite_projective

/-- Helper for Proposition 10.110.1: a proper cyclic quotient over a regular local ring has finite
depth, hence its depth is represented by a natural number. -/
lemma exists_nat_moduleDepth_of_proper_quotient {I : Ideal R} (hI : I ≠ ⊤) :
    ∃ e : ℕ, moduleDepth R (R ⧸ I) = e := by
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hsmul :
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (R ⧸ I)) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := R ⧸ I)
  have hfiniteDepth : moduleDepth R (R ⧸ I) < ⊤ := by
    -- Depth is finite because the maximal ideal does not generate the whole proper quotient.
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top
        (R := R) (I := IsLocalRing.maximalIdeal R) (M := R ⧸ I) hsmul
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
  exact ⟨e, by simpa using he.symm⟩

end
