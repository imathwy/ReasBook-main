import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_71_1
import stacks_proof.stacks_project.Chap10.Lemma_10_71_4
import stacks_proof.stacks_project.Chap10.Lemma_10_78_6
import stacks_proof.stacks_project.Chap10.Lemma_10_109_3
import stacks_proof.stacks_project.Chap10.Lemma_10_109_6
import stacks_proof.stacks_project.Chap10.Proposition_10_110_1
import stacks_proof.stacks_project.Chap10.Proposition_10_110_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w w' w''

noncomputable section

open CategoryTheory ChainComplex
open IsLocalRing
open scoped TensorProduct

section

variable {R : Type u}
variable [CommRing R]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/- Domain-style sampling:
* primary domain: regular local rings under flat local homomorphisms of commutative rings;
* sampled owner declarations:
  `IsRegularLocalRing`,
  `RingHom.domain_isLocalRing`,
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`,
  `isNoetherianRing_of_faithfullyFlat`,
  `regularLocal_of_residueField_projectiveDimension_ne_top`;
* best owner abstraction: the core owner is `IsRegularLocalRing`; this numbered item is the
  source-facing descent statement for that owner along a flat local algebra map, not a new owner
  or a wrapper around a lower-level package;
* primitive data vs. derived API:
  primitive data are the target ring `S`, the flat local map `R → S`, and regularity of `S`;
  locality of `R`, faithful flatness of `S` over `R`, and Noetherianity of `R` are derived proof
  inputs, so the public theorem header should not keep separate `[IsLocalRing R]` or
  `[IsNoetherianRing R]` assumptions;
* source/core/bridge triage:
  the theorem below is `source-facing`,
  the owner predicate `IsRegularLocalRing` is `core/canonical`,
  and the residue-field/global-dimension criterion for regularity is the main `bridge/view`
  used by the proof sketch.

This file should therefore keep the theorem directly on `IsRegularLocalRing` and avoid introducing
any auxiliary wrapper for regularity descent.
-/

/-- Helper for Lemma 10.110.9: a regular local target ring supplies a concrete finite
global-dimension bound. -/
lemma regular_target_has_global_dimension_bound
    (S : Type v) [CommRing S] [IsRegularLocalRing S] :
    ∃ d : ℕ, HasGlobalDimensionLE S d := by
  let d : ℕ := Module.finrank (ResidueField S) (CotangentSpace S)
  -- The regular-local characterization identifies the cotangent-space dimension with Krull
  -- dimension, which is the input expected by Proposition `10.110.1`.
  have hfinrank :
      Module.finrank (ResidueField S) (CotangentSpace S) = ringKrullDim S :=
    (IsRegularLocalRing.iff_finrank_cotangentSpace (R := S)).mp inferInstance
  have hdim : ringKrullDim S = d := by
    simpa [d] using hfinrank.symm
  exact ⟨d, hasGlobalDimensionLE_of_isRegularLocalRing (R := S) hdim⟩

/-- Helper for Lemma 10.110.9: the augmentation of a finite free resolution of the residue field
is surjective in degree `0`. -/
lemma residueField_resolution_augmentation_surjective
    [IsLocalRing R]
    {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R] (ResidueField R)}
    (hπ : ChainComplex.IsFiniteFreeResolution π) :
    Function.Surjective (π.f 0).hom := by
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  -- The quasi-isomorphism to `single₀` makes the augmentation an epimorphism in degree `0`.
  exact (ModuleCat.epi_iff_surjective _).mp
    (quasiIso_single_epi_zero (R := R) (N := ResidueField R) (G := F) π)

/-- Helper for Lemma 10.110.9: a finite free resolution of the residue field is exact at the
augmentation term. -/
lemma residueField_resolution_augmentation_exact
    [IsLocalRing R]
    {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R] (ResidueField R)}
    (hπ : ChainComplex.IsFiniteFreeResolution π) :
    Function.Exact (F.d 1 0).hom (π.f 0).hom := by
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  have hπ_comm : F.d 1 0 ≫ π.f 0 = 0 := by
    -- The augmented complex relation is part of the chain-map structure.
    simpa using (π.comm 1 0).symm
  let S₀ : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (F.d 1 0) (π.f 0) hπ_comm
  have hS₀_exact : S₀.Exact := by
    -- Exactness at degree `0` comes from the quasi-isomorphism to `single₀`.
    simpa [S₀] using quasiIso_single_exact_zero (R := R) (N := ResidueField R) (G := F) π
  -- Convert the categorical short-complex exactness to the linear-map exactness API.
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₀).1 hS₀_exact

/-- Helper for Lemma 10.110.9: a finite free resolution of the residue field is exact in every
positive degree. -/
lemma residueField_resolution_exact_succ
    [IsLocalRing R]
    {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R] (ResidueField R)}
    (hπ : ChainComplex.IsFiniteFreeResolution π) (n : ℕ) :
    Function.Exact (F.d (n + 2) (n + 1)).hom (F.d (n + 1) n).hom := by
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  have hF_comm :
      F.d (n + 2) (n + 1) ≫ F.d (n + 1) n = 0 := by
    -- Positive-degree differentials of the resolution still compose to zero.
    simpa [Nat.add_assoc] using F.d_comp_d (n + 2) (n + 1) n
  let Sₙ : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (F.d (n + 2) (n + 1)) (F.d (n + 1) n) hF_comm
  have hSₙ_exact : Sₙ.Exact := by
    -- The quasi-isomorphism to `single₀` forces exactness in every positive degree.
    simpa [Sₙ, Nat.add_assoc] using
      quasiIso_single_exact_succ (R := R) (N := ResidueField R) (G := F) π n
  -- Convert the short-complex exactness back to linear maps.
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Sₙ).1 hSₙ_exact

/-- Helper for Lemma 10.110.9: the augmentation kernel in a finite free resolution of the residue
field is finitely generated over the Noetherian source ring. -/
lemma residueField_resolution_augmentation_kernel_finite
    [IsLocalRing R] [IsNoetherianRing R]
    {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R] (ResidueField R)}
    (hπ : ChainComplex.IsFiniteFreeResolution π) :
    Module.Finite R (LinearMap.ker (π.f 0).hom) := by
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  let _ : Module.Finite R (F.X 0) := ChainComplex.IsFiniteFreeResolution.finite π 0
  -- Kernels inside finite modules remain finite over a Noetherian ring.
  simpa using kernel_finite_of_domain_finite (R := R) (π.f 0)

/-- Helper for Lemma 10.110.9: every higher syzygy kernel in a finite free resolution of the
residue field is finitely generated over the Noetherian source ring. -/
lemma residueField_resolution_differential_kernel_finite
    [IsLocalRing R] [IsNoetherianRing R]
    {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R] (ResidueField R)}
    (hπ : ChainComplex.IsFiniteFreeResolution π) (n : ℕ) :
    Module.Finite R (LinearMap.ker (F.d (n + 1) n).hom) := by
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  let _ : Module.Finite R (F.X (n + 1)) := ChainComplex.IsFiniteFreeResolution.finite π (n + 1)
  -- The same Noetherian kernel argument applies in every positive degree.
  simpa using kernel_finite_of_domain_finite (R := R) (F.d (n + 1) n)

/-- Helper for Lemma 10.110.9: conjugating an `S`-linear map by `Shrink.linearEquiv` moves it to
the ring universe without changing its algebraic behavior. -/
private abbrev shrinkLinearMap
    {S : Type v} [CommRing S]
    {M : Type w} {N : Type w'} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [Small M] [Small N] (f : M →ₗ[S] N) :
    Shrink M →ₗ[S] Shrink N :=
  (Shrink.linearEquiv S N).symm.toLinearMap.comp
    (f.comp (Shrink.linearEquiv S M).toLinearMap)

/-- Helper for Lemma 10.110.9: surjectivity survives passage to the shrunken model of a finite
module. -/
private theorem shrinkLinearMap_surjective
    {S : Type v} [CommRing S]
    {M : Type w} {N : Type w'} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [Small M] [Small N] {f : M →ₗ[S] N} (hf : Function.Surjective f) :
    Function.Surjective (shrinkLinearMap (S := S) f) := by
  intro y
  -- Lift the target element to the original module, solve surjectively there, and shrink back.
  obtain ⟨x, hx⟩ := hf ((Shrink.linearEquiv S N) y)
  refine ⟨(Shrink.linearEquiv S M).symm x, ?_⟩
  apply (Shrink.linearEquiv S N).injective
  simpa [shrinkLinearMap] using hx

/-- Helper for Lemma 10.110.9: exactness is preserved when the whole sequence is conjugated into
the shrunken ring universe. -/
private theorem shrinkLinearMap_exact
    {S : Type v} [CommRing S]
    {M : Type w} {N : Type w'} {P : Type w''}
    [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N]
    [AddCommGroup P] [Module S P]
    [Small M] [Small N] [Small P]
    {f : M →ₗ[S] N} {g : N →ₗ[S] P} (hfg : Function.Exact f g) :
    Function.Exact (shrinkLinearMap (S := S) f) (shrinkLinearMap (S := S) g) := by
  let eM : M ≃ₗ[S] Shrink M := (Shrink.linearEquiv S M).symm
  let eN : N ≃ₗ[S] Shrink N := (Shrink.linearEquiv S N).symm
  let eP : P ≃ₗ[S] Shrink P := (Shrink.linearEquiv S P).symm
  have h₁₂ : shrinkLinearMap (S := S) f ∘ₗ eM = eN ∘ₗ f := by
    ext x
    simp [shrinkLinearMap, eM, eN]
  have h₂₃ : shrinkLinearMap (S := S) g ∘ₗ eN = eP ∘ₗ g := by
    ext x
    simp [shrinkLinearMap, eN, eP]
  -- The shrunken sequence is exact because it is conjugate to the original exact sequence.
  exact Function.Exact.of_ladder_linearEquiv_of_exact h₁₂ h₂₃ hfg

/-- Helper for Lemma 10.110.9: the kernel of a shrunken linear map is linearly equivalent to the
original kernel. -/
private noncomputable def shrinkLinearMapKerEquiv
    {S : Type v} [CommRing S]
    {M : Type w} {N : Type w'} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [Small M] [Small N] (f : M →ₗ[S] N) :
    LinearMap.ker (shrinkLinearMap (S := S) f) ≃ₗ[S] LinearMap.ker f where
  toFun x := ⟨(Shrink.linearEquiv S M) x.1, by
    -- Apply the target shrink equivalence to recover the original kernel equation.
    simpa [LinearMap.mem_ker, shrinkLinearMap] using x.2⟩
  invFun x := ⟨(Shrink.linearEquiv S M).symm x.1, by
    -- Conversely, shrinking a kernel element still lands in the shrunken kernel.
    simpa [LinearMap.mem_ker, shrinkLinearMap] using x.2⟩
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp
  map_add' x y := by
    ext
    simp
  map_smul' a x := by
    ext
    simp

/-- Helper for Lemma 10.110.9: categorical projectivity implies module-theoretic projectivity
for a larger-universe `S`-module after enlarging the ring universe once. -/
private lemma module_projective_of_categorical_projective_mixed_universe
    {S : Type v} [CommRing S] {M : Type (max v w)} [AddCommGroup M] [Module S M]
    (hM : Projective (ModuleCat.of S M)) :
    Module.Projective S M := by
  let _ : Small.{max v w} S :=
    small_of_injective (f := (ULift.up : S → ULift.{max v w} S)) ULift.up_injective
  -- Convert categorical lifts through epimorphisms into module-theoretic lifts through
  -- surjective linear maps.
  refine Module.Projective.of_lifting_property ?_
  intro A B _ _ _ _ f g hf
  let _ : Projective (ModuleCat.of S M) := hM
  have hf' : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  refine ⟨(Projective.factorThru (ModuleCat.ofHom g) (ModuleCat.ofHom f)).hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom
    (Projective.factorThru_comp (ModuleCat.ofHom g) (ModuleCat.ofHom f))

/-- Helper for Lemma 10.110.9: projective-dimension bounds transport across linear equivalences in
mixed universes once the ring is made small in both ambient module universes. -/
private lemma hasProjectiveDimensionLE_of_linearEquiv_mixed_universe
    {S : Type v} [CommRing S]
    {M : Type (max v w)} {N : Type (max v w')}
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (e : M ≃ₗ[S] N) {n : ℕ}
    (hpd : HasProjectiveDimensionLE (ModuleCat.of S M) n) :
    HasProjectiveDimensionLE (ModuleCat.of S N) n := by
  let _ : Small.{max v w} S :=
    small_of_injective (f := (ULift.up : S → ULift.{max v w} S)) ULift.up_injective
  let _ : Small.{max v w'} S :=
    small_of_injective (f := (ULift.up : S → ULift.{max v w'} S)) ULift.up_injective
  let _ : HasProjectiveDimensionLE (ModuleCat.of S M) n := hpd
  -- Once `S` is small in both module universes, the canonical ModuleCat transport lemma applies.
  exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
    (M := ModuleCat.of S M) (N := ModuleCat.of S N) e n

/-- Helper for Lemma 10.110.9: a finite `S`-module in any larger universe still inherits the
global-dimension bound of `S`. -/
lemma hasProjectiveDimensionLE_of_finite_of_hasGlobalDimensionLE
    {S : Type v} [CommRing S] {M : Type (max v w)} [AddCommGroup M] [Module S M]
    [Module.Finite S M] {d : ℕ} (hgd : HasGlobalDimensionLE S d) :
    HasProjectiveDimensionLE (ModuleCat.of S M) d := by
  let _ : Small.{v} M := Module.Finite.small (R := S) (M := M)
  let _ : HasGlobalDimensionLE S d := hgd
  have hpd_shrink : HasProjectiveDimensionLE (ModuleCat.of S (Shrink M)) d :=
    HasGlobalDimensionLE.hasProjectiveDimensionLE (ModuleCat.of S (Shrink M))
  -- The finite module is represented in the ring universe, where the global-dimension instance
  -- applies, and then transported back along `Shrink.linearEquiv`.
  exact hasProjectiveDimensionLE_of_linearEquiv_mixed_universe
    (S := S) (e := Shrink.linearEquiv S M) hpd_shrink

/-- Helper for Lemma 10.110.9: the first syzygy criterion from Lemma `10.109.3` remains valid for
finite modules after shrinking to the ring universe. -/
lemma projective_ker_of_surjective_of_hasProjectiveDimensionLE_one_finite_mixed_universe
    {S : Type v} [CommRing S] {M : Type (max v w)} [AddCommGroup M] [Module S M]
    [Module.Finite S M]
    {F₀ : Type (max v w')} [AddCommGroup F₀] [Module S F₀]
    [Module.Projective S F₀] [Module.Finite S F₀]
    (π : F₀ →ₗ[S] M) (hπ : Function.Surjective π)
    (hpd : HasProjectiveDimensionLE (ModuleCat.of S M) 1) :
    Module.Projective S (LinearMap.ker π) := by
  let _ : Small.{v} M := Module.Finite.small (R := S) (M := M)
  let _ : Small.{v} F₀ := Module.Finite.small (R := S) (M := F₀)
  let πs : Shrink F₀ →ₗ[S] Shrink M := shrinkLinearMap (S := S) π
  let _ : Module.Projective S (Shrink F₀) :=
    Module.Projective.of_equiv' ((Shrink.linearEquiv S F₀).symm)
  have hπs : Function.Surjective πs := by
    -- Surjectivity is unchanged by conjugating the map into the shrunken universe.
    simpa [πs] using shrinkLinearMap_surjective (S := S) (f := π) hπ
  have hpd_shrink : HasProjectiveDimensionLE (ModuleCat.of S (Shrink M)) 1 :=
    hasProjectiveDimensionLE_of_linearEquiv_mixed_universe
      (S := S) (e := (Shrink.linearEquiv S M).symm) hpd
  have hproj_shrink : Module.Projective S (LinearMap.ker πs) :=
    projective_ker_of_surjective_of_hasProjectiveDimensionLE_one
      (R := S) (M := Shrink M) πs hπs hpd_shrink
  let _ : Module.Projective S (LinearMap.ker πs) := hproj_shrink
  -- Transport the shrunken kernel projectivity back to the original kernel.
  exact Module.Projective.of_equiv' (shrinkLinearMapKerEquiv (S := S) π)

/-- Helper for Chap10 Lemma 10 110 9: an exact projective window of length `e + 1` has projective
top kernel when the target has projective dimension at most `e + 2`. -/
private theorem projective_top_kernel_of_exact_of_hasProjectiveDimensionLE_succ
    {S : Type v} [CommRing S]
    {e : ℕ} {M : Type v} [AddCommGroup M] [Module S M]
    {F : Fin (e + 2) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module.Projective S (F i)]
    (d : (i : Fin (e + 1)) → F i.succ →ₗ[S] F i.castSucc)
    (π : F 0 →ₗ[S] M)
    (hπ : Function.Surjective π)
    (h_exact₀ : Function.Exact (d 0) π)
    (h_exact : ∀ i : Fin e, Function.Exact (d i.succ) (d i.castSucc))
    (hpd : HasProjectiveDimensionLE (ModuleCat.of S M) (e + 2)) :
    Module.Projective S (LinearMap.ker (d (Fin.last e))) := by
  induction e generalizing M with
  | zero =>
      have hκ_mem : ∀ x, d 0 x ∈ LinearMap.ker π := by
        intro x
        -- Exactness at `F₀` makes the first differential land in the augmentation kernel.
        simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
          LinearMap.congr_fun h_exact₀.linearMap_comp_eq_zero x
      let κ : F 1 →ₗ[S] LinearMap.ker π :=
        LinearMap.codRestrict (LinearMap.ker π) (d 0) hκ_mem
      have hκ_ker : LinearMap.ker κ = LinearMap.ker (d 0) := by
        simpa [κ] using LinearMap.ker_codRestrict (LinearMap.ker π) (d 0) hκ_mem
      have hκ_surj : Function.Surjective κ := by
        intro x
        -- Exactness identifies the augmentation kernel with the range of the first differential.
        rcases (h_exact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hpd_kerπ : HasProjectiveDimensionLE (ModuleCat.of S (LinearMap.ker π)) 1 :=
        hasProjectiveDimensionLE_first_syzygy_of_surjective
          (R := S) (M := M) (π := π) hπ hpd
      have hprojκ : Module.Projective S (LinearMap.ker κ) :=
        projective_ker_of_surjective_of_hasProjectiveDimensionLE_one
          (R := S) (M := LinearMap.ker π) κ hκ_surj hpd_kerπ
      -- The codomain restriction did not change the kernel, so this is the requested top kernel.
      exact hκ_ker ▸ hprojκ
  | succ e ih =>
      have hκ_mem : ∀ x, d 0 x ∈ LinearMap.ker π := by
        intro x
        -- The first differential again factors through the augmentation kernel.
        simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
          LinearMap.congr_fun h_exact₀.linearMap_comp_eq_zero x
      let κ : F 1 →ₗ[S] LinearMap.ker π :=
        LinearMap.codRestrict (LinearMap.ker π) (d 0) hκ_mem
      have hκ_ker : LinearMap.ker κ = LinearMap.ker (d 0) := by
        simpa [κ] using LinearMap.ker_codRestrict (LinearMap.ker π) (d 0) hκ_mem
      have hκ_surj : Function.Surjective κ := by
        intro x
        -- The first syzygy is the image of `d₀`.
        rcases (h_exact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_exact : Function.Exact (d 1) κ := by
        -- Restricting the codomain to the kernel preserves the next exactness equation.
        exact LinearMap.exact_iff.mpr <| hκ_ker.trans (h_exact 0).linearMap_ker_eq
      have hpd' : HasProjectiveDimensionLE (ModuleCat.of S (LinearMap.ker π)) (e + 2) :=
        hasProjectiveDimensionLE_first_syzygy_of_surjective
          (R := S) (M := M) (π := π) hπ hpd
      let F' : Fin (e + 2) → Type v := fun i => F i.succ
      let d' : (i : Fin (e + 1)) → F' i.succ →ₗ[S] F' i.castSucc := fun i => d i.succ
      have h_exact' : ∀ i : Fin e, Function.Exact (d' i.succ) (d' i.castSucc) := by
        intro i
        -- The truncated tail inherits exactness from the original window.
        simpa [d'] using h_exact i.succ
      -- Shift to the first syzygy and apply the induction hypothesis to the truncated tail.
      simpa [F', d'] using
        ih (M := LinearMap.ker π) (F := F') (d := d') (π := κ)
          hκ_surj hκ_exact h_exact' hpd'

/-- Helper for Lemma 10.110.9: the higher-syzygy criterion from Lemma `10.109.3` remains valid for
finite exact windows after shrinking every module to the ring universe. -/
lemma projective_top_kernel_of_exact_of_hasProjectiveDimensionLE_finite_mixed_universe
    {S : Type v} [CommRing S]
    {e : ℕ} {M : Type (max v w)} [AddCommGroup M] [Module S M] [Module.Finite S M]
    {F : Fin (e + 2) → Type (max v w')}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    [∀ i, Module.Projective S (F i)] [∀ i, Module.Finite S (F i)]
    (d : (i : Fin (e + 1)) → F i.succ →ₗ[S] F i.castSucc)
    (π : F 0 →ₗ[S] M)
    (hπ : Function.Surjective π)
    (h_exact₀ : Function.Exact (d 0) π)
    (h_exact : ∀ i : Fin e, Function.Exact (d i.succ) (d i.castSucc))
    (hpd : HasProjectiveDimensionLE (ModuleCat.of S M) (e + 2)) :
    Module.Projective S (LinearMap.ker (d (Fin.last e))) := by
  let _ : Small.{v} M := Module.Finite.small (R := S) (M := M)
  let _ : ∀ i, Small.{v} (F i) := fun i ↦ Module.Finite.small (R := S) (M := F i)
  let ds : (i : Fin (e + 1)) → Shrink (F i.succ) →ₗ[S] Shrink (F i.castSucc) :=
    fun i ↦ shrinkLinearMap (S := S) (d i)
  let πs : Shrink (F 0) →ₗ[S] Shrink M := shrinkLinearMap (S := S) π
  let _ : ∀ i, Module.Projective S (Shrink (F i)) :=
    fun i ↦ Module.Projective.of_equiv' ((Shrink.linearEquiv S (F i)).symm)
  have hπs : Function.Surjective πs := by
    -- The augmentation remains surjective after shrinking.
    simpa [πs] using shrinkLinearMap_surjective (S := S) (f := π) hπ
  have h_exact₀s : Function.Exact (ds 0) πs := by
    -- Exactness of the initial window is invariant under the same conjugation.
    simpa [ds, πs] using shrinkLinearMap_exact (S := S) h_exact₀
  have h_exacts : ∀ i : Fin e, Function.Exact (ds i.succ) (ds i.castSucc) := by
    intro i
    -- Each higher exact window is transported independently to the common universe.
    simpa [ds] using shrinkLinearMap_exact (S := S) (h_exact i)
  have hpd_shrink : HasProjectiveDimensionLE (ModuleCat.of S (Shrink M)) (e + 2) :=
    hasProjectiveDimensionLE_of_linearEquiv_mixed_universe
      (S := S) (e := (Shrink.linearEquiv S M).symm) hpd
  have hproj_shrink :
      Module.Projective S (LinearMap.ker (ds (Fin.last e))) :=
    projective_top_kernel_of_exact_of_hasProjectiveDimensionLE_succ
      (S := S) (M := Shrink M) (F := fun i ↦ Shrink (F i))
      (d := ds) (π := πs) hπs h_exact₀s h_exacts hpd_shrink
  let _ : Module.Projective S (LinearMap.ker (ds (Fin.last e))) := hproj_shrink
  -- The final shrunken top kernel is linearly equivalent to the original one.
  simpa [ds] using Module.Projective.of_equiv'
    (shrinkLinearMapKerEquiv (S := S) (d (Fin.last e)))

/-- Helper for Lemma 10.110.9: if the kernel of the tensorized differential is projective, then
the tensor product of the original kernel is projective via `LinearMap.tensorKerEquiv`. -/
lemma tensor_product_projective_of_tensorized_kernel_projective
    {S : Type v} [CommRing S] [Algebra R S] [Module.Flat R S]
    {M : Type w} {N : Type w'} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hproj : Module.Projective S
      (LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S f))) :
    Module.Projective S (S ⊗[R] LinearMap.ker f) := by
  letI : Module.Projective S
      (LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S f)) := hproj
  -- The flatness isomorphism identifies `S ⊗ ker f` with the kernel of the tensorized map.
  exact Module.Projective.of_equiv' (LinearMap.tensorKerEquiv S S f).symm

/-- Helper for Lemma 10.110.9: a finite module with projective dimension at most `0` is
projective, even when its universe is larger than the ring universe. -/
lemma module_projective_of_finite_of_hasProjectiveDimensionLE_zero
    {S : Type v} [CommRing S] {M : Type (max v w)} [AddCommGroup M] [Module S M]
    [Module.Finite S M]
    (hpd : HasProjectiveDimensionLE (ModuleCat.of S M) 0) :
    Module.Projective S M := by
  have hproj_cat : Projective (ModuleCat.of S M) := by
    exact (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero
      (ModuleCat.of S M)).2 hpd
  -- After supplying the needed smallness instance on the ring, categorical and module
  -- projectivity agree for this larger-universe module.
  exact module_projective_of_categorical_projective_mixed_universe (S := S) hproj_cat

/-- Helper for Lemma 10.110.9: if the regular target ring has global dimension at most `d`, then
the `d`th syzygy of any chosen finite free resolution of `ResidueField R` is projective. -/
lemma residueField_resolution_syzygy_projective_of_target_global_dimension
    {S : Type v} [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] [IsNoetherianRing R]
    {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R] (ResidueField R)}
    (hπ : ChainComplex.IsFiniteFreeResolution π) {d : ℕ}
    (hgd : HasGlobalDimensionLE S d) :
    let P : ProjectiveResolution (ModuleCat.of R (ResidueField R)) :=
      ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := ResidueField R)
        (F := F) π
    P.SyzygyProjective d := by
  let P : ProjectiveResolution (ModuleCat.of R (ResidueField R)) :=
    ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := ResidueField R)
      (F := F) π
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  let _ : Module.Finite R (ResidueField R) := by infer_instance
  cases d with
  | zero =>
      let _ : Module.Finite S (S ⊗[R] ResidueField R) :=
        Module.Finite.base_change (R := R) (A := S) (M := ResidueField R)
      have hpd_tensor :
          HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[R] ResidueField R)) 0 :=
        hasProjectiveDimensionLE_of_finite_of_hasGlobalDimensionLE
          (S := S) (M := S ⊗[R] ResidueField R) hgd
      have hproj_tensor : Module.Projective S (S ⊗[R] ResidueField R) :=
        module_projective_of_finite_of_hasProjectiveDimensionLE_zero
          (S := S) (M := S ⊗[R] ResidueField R) hpd_tensor
      have hfinite_projective_tensor :
          Module.FiniteProjective S (S ⊗[R] ResidueField R) :=
        ⟨inferInstance, hproj_tensor⟩
      have hfinite_projective :
          Module.FiniteProjective R (ResidueField R) :=
        (finite_projective_iff_finite_projective_tensor_of_flat_localHom
          (R := R) (S := S) (M := ResidueField R)).mpr hfinite_projective_tensor
      let _ : Module.Projective R (ResidueField R) := hfinite_projective.2
      -- In degree zero the syzygy condition is just projectivity of the residue field.
      simpa [P, CategoryTheory.ProjectiveResolution.SyzygyProjective] using
        (inferInstance : Projective (ModuleCat.of R (ResidueField R)))
  | succ d =>
      cases d with
      | zero =>
          let _ : Module.Free R (F.X 0) :=
            ChainComplex.IsFreeResolution.free (R := R) (M := ResidueField R) π 0
          let _ : Module.Projective R (F.X 0) := Module.Projective.of_free
          let _ : Module.Finite R (F.X 0) := ChainComplex.IsFiniteFreeResolution.finite π 0
          let _ : Module.Finite S (S ⊗[R] ResidueField R) :=
            Module.Finite.base_change (R := R) (A := S) (M := ResidueField R)
          let _ : Module.Finite S (S ⊗[R] F.X 0) :=
            Module.Finite.base_change (R := R) (A := S) (M := F.X 0)
          let πS : S ⊗[R] F.X 0 →ₗ[S] S ⊗[R] ResidueField R :=
            TensorProduct.AlgebraTensorModule.lTensor S S (π.f 0).hom
          have hπS : Function.Surjective πS := by
            -- Tensoring the surjective augmentation with the flat target keeps it surjective.
            simpa [πS] using
              LinearMap.lTensor_surjective S
                (residueField_resolution_augmentation_surjective (R := R) hπ)
          have hpd_tensor :
              HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[R] ResidueField R)) 1 :=
            hasProjectiveDimensionLE_of_finite_of_hasGlobalDimensionLE
              (S := S) (M := S ⊗[R] ResidueField R) hgd
          have hproj_kernelS : Module.Projective S (LinearMap.ker πS) :=
            projective_ker_of_surjective_of_hasProjectiveDimensionLE_one_finite_mixed_universe
              (S := S) (M := S ⊗[R] ResidueField R) (F₀ := S ⊗[R] F.X 0)
              πS hπS hpd_tensor
          have hproj_tensor_kernel :
              Module.Projective S (S ⊗[R] LinearMap.ker (π.f 0).hom) :=
            tensor_product_projective_of_tensorized_kernel_projective
              (R := R) (S := S) (π.f 0).hom hproj_kernelS
          let _ : Module.Finite R (LinearMap.ker (π.f 0).hom) :=
            residueField_resolution_augmentation_kernel_finite (R := R) hπ
          let _ : Module.Finite S (S ⊗[R] LinearMap.ker (π.f 0).hom) :=
            Module.Finite.base_change
              (R := R) (A := S) (M := LinearMap.ker (π.f 0).hom)
          have hfinite_projective_tensor :
              Module.FiniteProjective S (S ⊗[R] LinearMap.ker (π.f 0).hom) :=
            ⟨inferInstance, hproj_tensor_kernel⟩
          have hfinite_projective :
              Module.FiniteProjective R (LinearMap.ker (π.f 0).hom) :=
            (finite_projective_iff_finite_projective_tensor_of_flat_localHom
              (R := R) (S := S) (M := LinearMap.ker (π.f 0).hom)).mpr
              hfinite_projective_tensor
          let _ : Module.Projective R (LinearMap.ker (π.f 0).hom) := hfinite_projective.2
          -- In degree one, the syzygy condition is projectivity of the augmentation kernel.
          simpa [P, CategoryTheory.ProjectiveResolution.SyzygyProjective] using
            (inferInstance :
              Projective (ModuleCat.of R (LinearMap.ker (π.f 0).hom)))
      | succ e =>
          let _ : Module.Finite S (S ⊗[R] ResidueField R) :=
            Module.Finite.base_change (R := R) (A := S) (M := ResidueField R)
          let Ft := fun i : Fin (e + 2) ↦ S ⊗[R] F.X i
          let dS : (i : Fin (e + 1)) → Ft i.succ →ₗ[S] Ft i.castSucc :=
            fun i ↦ TensorProduct.AlgebraTensorModule.lTensor S S
              (F.d i.succ i.castSucc).hom
          let πS : Ft 0 →ₗ[S] S ⊗[R] ResidueField R :=
            TensorProduct.AlgebraTensorModule.lTensor S S (π.f 0).hom
          let _ : ∀ i : Fin (e + 2), Module.Free R (F.X i) :=
            fun i ↦ ChainComplex.IsFreeResolution.free (R := R) (M := ResidueField R) π i
          let _ : ∀ i : Fin (e + 2), Module.Projective R (F.X i) :=
            fun _ ↦ Module.Projective.of_free
          let _ : ∀ i : Fin (e + 2), Module.Finite R (F.X i) :=
            fun i ↦ ChainComplex.IsFiniteFreeResolution.finite π i
          let _ : ∀ i : Fin (e + 2), Module.Finite S (Ft i) :=
            fun i ↦ Module.Finite.base_change (R := R) (A := S) (M := F.X i)
          let _ : ∀ i : Fin (e + 2), Module.Projective S (Ft i) := fun _ ↦ inferInstance
          have hπS : Function.Surjective πS := by
            -- The tensorized augmentation is still surjective.
            simpa [πS] using
              LinearMap.lTensor_surjective S
                (residueField_resolution_augmentation_surjective (R := R) hπ)
          have h_exact₀S : Function.Exact (dS 0) πS := by
            -- Flatness preserves exactness at the augmentation term.
            simpa [dS, πS] using
              Module.Flat.lTensor_exact S
                (residueField_resolution_augmentation_exact (R := R) hπ)
          have h_exactS : ∀ i : Fin e, Function.Exact (dS i.succ) (dS i.castSucc) := by
            intro i
            -- Every positive-degree exact window survives tensoring with the flat target.
            simpa [dS] using
              Module.Flat.lTensor_exact S
                (residueField_resolution_exact_succ (R := R) hπ (i : ℕ))
          have hpd_tensor :
              HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[R] ResidueField R)) (e + 2) :=
            hasProjectiveDimensionLE_of_finite_of_hasGlobalDimensionLE
              (S := S) (M := S ⊗[R] ResidueField R) hgd
          have hproj_kernelS : Module.Projective S (LinearMap.ker (dS (Fin.last e))) :=
            projective_top_kernel_of_exact_of_hasProjectiveDimensionLE_finite_mixed_universe
              (S := S) (M := S ⊗[R] ResidueField R) (F := Ft)
              (d := dS) (π := πS) hπS h_exact₀S h_exactS hpd_tensor
          have hproj_tensor_kernel :
              Module.Projective S (S ⊗[R] LinearMap.ker (F.d (e + 1) e).hom) := by
            -- The top tensorized differential is the tensor of the original top differential.
            simpa [dS] using
              tensor_product_projective_of_tensorized_kernel_projective
                (R := R) (S := S) (F.d (e + 1) e).hom hproj_kernelS
          let _ : Module.Finite R (LinearMap.ker (F.d (e + 1) e).hom) :=
            residueField_resolution_differential_kernel_finite (R := R) hπ e
          let _ : Module.Finite S (S ⊗[R] LinearMap.ker (F.d (e + 1) e).hom) :=
            Module.Finite.base_change
              (R := R) (A := S) (M := LinearMap.ker (F.d (e + 1) e).hom)
          have hfinite_projective_tensor :
              Module.FiniteProjective S (S ⊗[R] LinearMap.ker (F.d (e + 1) e).hom) :=
            ⟨inferInstance, hproj_tensor_kernel⟩
          have hfinite_projective :
              Module.FiniteProjective R (LinearMap.ker (F.d (e + 1) e).hom) :=
            (finite_projective_iff_finite_projective_tensor_of_flat_localHom
              (R := R) (S := S) (M := LinearMap.ker (F.d (e + 1) e).hom)).mpr
              hfinite_projective_tensor
          let _ : Module.Projective R (LinearMap.ker (F.d (e + 1) e).hom) :=
            hfinite_projective.2
          -- For higher degrees, the syzygy is the kernel of the corresponding resolution
          -- differential.
          simpa [P, CategoryTheory.ProjectiveResolution.SyzygyProjective] using
            (inferInstance :
              Projective (ModuleCat.of R (LinearMap.ker (F.d (e + 1) e).hom)))

/-- Helper for Lemma 10.110.9: the residue field of the source ring has finite projective
dimension once the target is regular local. -/
lemma residueField_hasProjectiveDimensionLE_of_target_regular
    {S : Type v} [CommRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    [IsRegularLocalRing S] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ d : ℕ, HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) d := by
  obtain ⟨d, hgd⟩ := regular_target_has_global_dimension_bound S
  let _ : Module.Finite R (ResidueField R) := by infer_instance
  -- Choose a finite free resolution of the residue field exactly as in the source proof.
  rcases module_exists_finite_free_resolution (R := R) (M := ResidueField R) with ⟨F, π, hπ⟩
  let P : ProjectiveResolution (ModuleCat.of R (ResidueField R)) :=
    ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := ResidueField R)
      (F := F) π
  have hfinite : ∀ n, Module.Finite R (P.complex.X n) := by
    intro n
    -- The chosen finite free resolution already has finite terms in every degree.
    simpa [P] using ChainComplex.IsFiniteFreeResolution.finite π n
  have hsyz : P.SyzygyProjective d := by
    -- The tensorized source-proof argument makes the top syzygy projective over `R`.
    simpa [P] using
      residueField_resolution_syzygy_projective_of_target_global_dimension
        (R := R) (S := S) (F := F) (π := π) hπ hgd
  have hfinite_projective :
      ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms
        (ModuleCat.of R (ResidueField R)) d := by
    -- Lemma `10.109.6` truncates the projective resolution at the projective top syzygy.
    simpa [P] using
      CategoryTheory.ProjectiveResolution.hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_of_syzygyProjective
        (R := R) (M := ModuleCat.of R (ResidueField R)) (P := P) hfinite hsyz
  -- Convert the bounded finite-projective resolution back to the canonical owner statement.
  exact ⟨d, (hasProjectiveDimensionLE_iff_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
    (R := R) (M := ResidueField R) d).mpr hfinite_projective⟩

-- Proof sketch: let `d` be a global-dimension bound on the regular target `S`. Choose a finite
-- free resolution of the residue field of `R`, tensor it with `S`, and use Lemma `10.109.3` to
-- show that the `d`th tensorized syzygy is projective over `S`. Lemma `10.78.6` descends this
-- finite projective syzygy to `R`, so the residue field of `R` has projective dimension at most
-- `d`. Proposition `10.110.5` then yields regularity of `R`.
/-- Chap10 Lemma 10 110 9: if `R → S` is a flat local homomorphism of local Noetherian rings and `S` is a
regular local ring, then `R` is a regular local ring. -/
@[stacks 00OF]
theorem isRegularLocalRing_of_flat_localHom_of_regularTarget
    (S : Type v) [CommRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    [IsRegularLocalRing S] :
    IsRegularLocalRing R := by
  let _ : IsLocalRing R := RingHom.domain_isLocalRing (algebraMap R S)
  let _ : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let _ : IsNoetherianRing R :=
    (isNoetherianRing_iff_ideal_fg R).2 fun I ↦ by
      -- Faithfully flat descent of finite generation gives Noetherianity of the source ring.
      exact Ideal.FG.of_FG_map_of_faithfullyFlat ((I.map (algebraMap R S)).fg_of_isNoetherianRing)
  obtain ⟨d, hpd⟩ :=
    residueField_hasProjectiveDimensionLE_of_target_regular (R := R) (S := S)
  let _ : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) d := hpd
  have hresidue :
      projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤ := by
    -- A concrete projective-dimension bound is exactly the finite-pdim criterion in
    -- Proposition `10.110.5`.
    exact
      (CategoryTheory.projectiveDimension_ne_top_iff (ModuleCat.of R (ResidueField R))).2
        ⟨d, inferInstance⟩
  -- The residue-field criterion finishes the regularity descent.
  exact regularLocal_of_residueField_projectiveDimension_ne_top (R := R) hresidue

end
