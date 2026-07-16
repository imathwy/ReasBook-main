import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_71_2
import stacks_proof.stacks_project.Chap10.Lemma_10_71_1
import stacks_proof.stacks_project.Chap10.Lemma_10_71_4
import stacks_proof.stacks_project.Chap10.Definition_10_103_8
import stacks_proof.stacks_project.Chap10.Definition_10_104_1
import stacks_proof.stacks_project.Chap10.Lemma_10_104_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ChainComplex

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/- Domain-style sampling:
* primary domain: finite free resolutions and maximal Cohen-Macaulay syzygies over Noetherian
  local Cohen-Macaulay rings;
* sampled owner declarations:
  `module_exists_finite_free_resolution`,
  `ChainComplex.IsFiniteFreeResolution`,
  `Module.MaximalCohenMacaulay`,
  `Module.CohenMacaulay`;
* best owner abstraction: a chosen finite free resolution
  `π : F ⟶ moduleSingle[R] M`, together with the textbook syzygy indexing convention;
* source/core/bridge triage:
  `ChainComplex.SyzygyMaximalCohenMacaulay` is the source-facing owner predicate for the textbook
  `(d - e)`th syzygy of an augmented free resolution;
  `ChainComplex.IsFiniteFreeResolution π` is the canonical owner of the chosen finite free
  resolution data;
  the main theorem is the source-facing existence statement obtained by choosing such a
  resolution and proving the chosen-resolution helper below.
-/

namespace ChainComplex

/-- The `n`th syzygy of an augmentation `π : F ⟶ moduleSingle[R] M` is maximal Cohen-Macaulay,
with the chapter's indexing convention: degree `0` is `M`, degree `1` is the augmentation kernel,
and degree `n + 2` is the kernel of the differential `F.X (n + 1) ⟶ F.X n`. -/
def SyzygyMaximalCohenMacaulay {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ moduleSingle[R]M) (n : ℕ) : Prop :=
  match n with
  | 0 => Module.MaximalCohenMacaulay R M
  | 1 => Module.MaximalCohenMacaulay R (LinearMap.ker (π.f 0).hom)
  | n + 2 => Module.MaximalCohenMacaulay R (LinearMap.ker (F.d (n + 1) n).hom)

end ChainComplex

/-- Helper for Chap10 Lemma 10 104 9: the syzygy type attached to an augmented resolution, with
the chapter's indexing convention. -/
private abbrev resolutionSyzygy {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ moduleSingle[R]M) : ℕ → Type u
  | 0 => M
  | 1 => LinearMap.ker (π.f 0).hom
  | n + 2 => LinearMap.ker (F.d (n + 1) n).hom

/-- Helper for Chap10 Lemma 10 104 9: each syzygy type carries its canonical additive group
structure. -/
private noncomputable instance resolutionSyzygy.addCommGroup {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ moduleSingle[R]M) (n : ℕ) : AddCommGroup (resolutionSyzygy π n) := by
  -- The cases are either the original module or a linear-map kernel.
  cases n with
  | zero =>
      infer_instance
  | succ n =>
      cases n with
      | zero =>
          infer_instance
      | succ n =>
          infer_instance

/-- Helper for Chap10 Lemma 10 104 9: each syzygy type carries its canonical module structure. -/
private noncomputable instance resolutionSyzygy.module {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ moduleSingle[R]M) (n : ℕ) : Module R (resolutionSyzygy π n) := by
  -- The module structures are inherited from `M` and from kernel submodules of the free terms.
  cases n with
  | zero =>
      infer_instance
  | succ n =>
      cases n with
      | zero =>
          infer_instance
      | succ n =>
          infer_instance

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 104 9: the first differential lands in the augmentation kernel. -/
private lemma resolution_d_one_zero_mem_augmentation_kernel
    {F : ChainComplex (ModuleCat R) ℕ} {π : F ⟶ moduleSingle[R]M} (x : F.X 1) :
    (F.d 1 0).hom x ∈ LinearMap.ker (π.f 0).hom := by
  -- The chain-map relation says that the augmentation kills the first differential.
  simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (π.comm 1 0).symm) x

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 104 9: every positive differential lands in the preceding
differential kernel. -/
private lemma resolution_d_succ_mem_differential_kernel
    {F : ChainComplex (ModuleCat R) ℕ} (n : ℕ) (x : F.X (n + 2)) :
    (F.d (n + 2) (n + 1)).hom x ∈ LinearMap.ker (F.d (n + 1) n).hom := by
  -- The square-zero relation for a chain complex gives the required kernel membership.
  have hcomp : F.d (n + 2) (n + 1) ≫ F.d (n + 1) n = 0 := by
    simpa [Nat.add_assoc] using F.d_comp_d (n + 2) (n + 1) n
  change (F.d (n + 1) n).hom ((F.d (n + 2) (n + 1)).hom x) = 0
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcomp) x

/-- Helper for Chap10 Lemma 10 104 9: the natural map from the `n`th free term to the `n`th
syzygy. -/
private noncomputable def syzygyToPrevious {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ moduleSingle[R]M) : (n : ℕ) → F.X n →ₗ[R] resolutionSyzygy π n
  | 0 => (π.f 0).hom
  | 1 => LinearMap.codRestrict (LinearMap.ker (π.f 0).hom) (F.d 1 0).hom
      (resolution_d_one_zero_mem_augmentation_kernel (π := π))
  | n + 2 => LinearMap.codRestrict (LinearMap.ker (F.d (n + 1) n).hom)
      (F.d (n + 2) (n + 1)).hom
      (resolution_d_succ_mem_differential_kernel (F := F) n)

/-- Helper for Chap10 Lemma 10 104 9: the inclusion of the next syzygy into the corresponding
free term. -/
private noncomputable def syzygyInclusion {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ moduleSingle[R]M) : (n : ℕ) → resolutionSyzygy π (n + 1) →ₗ[R] F.X n
  | 0 => (LinearMap.ker (π.f 0).hom).subtype
  | 1 => (LinearMap.ker (F.d 1 0).hom).subtype
  | n + 2 => (LinearMap.ker (F.d (n + 2) (n + 1)).hom).subtype

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 104 9: the syzygy inclusion is killed by the map to the previous
syzygy. -/
private lemma syzygyToPrevious_comp_syzygyInclusion
    {F : ChainComplex (ModuleCat R) ℕ} (π : F ⟶ moduleSingle[R]M) (n : ℕ) :
    (syzygyToPrevious π n).comp (syzygyInclusion π n) = 0 := by
  -- Each branch is exactly the defining kernel condition for the next syzygy.
  cases n with
  | zero =>
      ext x
      change (π.f 0).hom x.1 = 0
      exact x.2
  | succ n =>
      cases n with
      | zero =>
          ext x
          change (F.d 1 0).hom x.1 = 0
          exact x.2
      | succ n =>
          ext x
          change (F.d (n + 2) (n + 1)).hom x.1 = 0
          exact x.2

/-- Helper for Chap10 Lemma 10 104 9: the short complex
`K_{n+1} → F_n → K_n` attached to the syzygy tower. -/
private noncomputable def syzygyShortComplex {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ moduleSingle[R]M) (n : ℕ) : ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero (syzygyInclusion π n) (syzygyToPrevious π n)
    (syzygyToPrevious_comp_syzygyInclusion π n)

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 104 9: a quasi-isomorphic augmentation is surjective in degree
zero. -/
private lemma resolution_augmentation_surjective
    {F : ChainComplex (ModuleCat R) ℕ} {π : F ⟶ moduleSingle[R]M}
    (hπ : IsFiniteFreeResolution π) :
    Function.Surjective (π.f 0).hom := by
  letI : IsFiniteFreeResolution π := hπ
  -- Degree-zero quasi-isomorphism to `single₀` makes the augmentation an epimorphism.
  exact (ModuleCat.epi_iff_surjective _).mp
    (quasiIso_single_epi_zero (R := R) (N := M) (G := F) π)

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 104 9: the augmentation window of a finite free resolution is
exact. -/
private lemma resolution_augmentation_exact
    {F : ChainComplex (ModuleCat R) ℕ} {π : F ⟶ moduleSingle[R]M}
    (hπ : IsFiniteFreeResolution π) :
    Function.Exact (F.d 1 0).hom (π.f 0).hom := by
  letI : IsFiniteFreeResolution π := hπ
  have hπ_comm : F.d 1 0 ≫ π.f 0 = 0 := by
    simpa using (π.comm 1 0).symm
  let S₀ : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (F.d 1 0) (π.f 0) hπ_comm
  have hS₀_exact : S₀.Exact := by
    -- Exactness at degree zero is the standard consequence of resolving `single₀`.
    simpa [S₀] using quasiIso_single_exact_zero (R := R) (N := M) (G := F) π
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₀).1 hS₀_exact

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 104 9: a finite free resolution is exact in every positive
degree. -/
private lemma resolution_exact_succ
    {F : ChainComplex (ModuleCat R) ℕ} {π : F ⟶ moduleSingle[R]M}
    (hπ : IsFiniteFreeResolution π) (n : ℕ) :
    Function.Exact (F.d (n + 2) (n + 1)).hom (F.d (n + 1) n).hom := by
  letI : IsFiniteFreeResolution π := hπ
  let Sₙ : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (F.d (n + 2) (n + 1)) (F.d (n + 1) n)
      (F.d_comp_d (n + 2) (n + 1) n)
  have hSₙ_exact : Sₙ.Exact := by
    -- Positive-degree exactness follows because the target single complex is exact there.
    simpa [Sₙ, Nat.add_assoc] using
      quasiIso_single_exact_succ (R := R) (N := M) (G := F) π n
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Sₙ).1 hSₙ_exact

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 104 9: each map from a free term onto the previous syzygy is
surjective. -/
private lemma syzygyToPrevious_surjective
    {F : ChainComplex (ModuleCat R) ℕ} {π : F ⟶ moduleSingle[R]M}
    (hπ : IsFiniteFreeResolution π) (n : ℕ) :
    Function.Surjective (syzygyToPrevious π n) := by
  -- Surjectivity is exactness of the original augmented complex, rewritten through the
  -- codomain restriction defining the syzygy map.
  cases n with
  | zero =>
      simpa [syzygyToPrevious] using resolution_augmentation_surjective (π := π) hπ
  | succ n =>
      cases n with
      | zero =>
          intro y
          obtain ⟨x, hx⟩ := (resolution_augmentation_exact (π := π) hπ y.1).mp y.2
          refine ⟨x, ?_⟩
          apply Subtype.ext
          change (F.d 1 0).hom x = y.1
          exact hx
      | succ n =>
          intro y
          obtain ⟨x, hx⟩ := (resolution_exact_succ (π := π) hπ n y.1).mp y.2
          refine ⟨x, ?_⟩
          apply Subtype.ext
          change (F.d (n + 2) (n + 1)).hom x = y.1
          exact hx

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 104 9: the syzygy inclusion is injective. -/
private lemma syzygyInclusion_injective
    {F : ChainComplex (ModuleCat R) ℕ} (π : F ⟶ moduleSingle[R]M) (n : ℕ) :
    Function.Injective (syzygyInclusion π n) := by
  -- In every degree the map is a subtype inclusion of a linear-map kernel.
  cases n with
  | zero =>
      exact Submodule.injective_subtype (LinearMap.ker (π.f 0).hom)
  | succ n =>
      cases n with
      | zero =>
          exact Submodule.injective_subtype (LinearMap.ker (F.d 1 0).hom)
      | succ n =>
          exact Submodule.injective_subtype (LinearMap.ker (F.d (n + 2) (n + 1)).hom)

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 104 9: the syzygy row is exact at its free middle term. -/
private lemma syzygyRow_function_exact
    {F : ChainComplex (ModuleCat R) ℕ} (π : F ⟶ moduleSingle[R]M) (n : ℕ) :
    Function.Exact (syzygyInclusion π n) (syzygyToPrevious π n) := by
  -- Exactness here is the tautological exactness of a kernel inclusion followed by the map whose
  -- kernel it defines, with codomain restrictions removed by subtype extensionality.
  cases n with
  | zero =>
      intro x
      constructor
      · intro hx
        refine ⟨⟨x, ?_⟩, ?_⟩
        · exact hx
        · rfl
      · rintro ⟨y, rfl⟩
        change (π.f 0).hom y.1 = 0
        exact y.2
  | succ n =>
      cases n with
      | zero =>
          intro x
          constructor
          · intro hx
            refine ⟨⟨x, ?_⟩, ?_⟩
            · have hxval : (F.d 1 0).hom x = 0 := by
                exact congrArg Subtype.val hx
              exact hxval
            · rfl
          · rintro ⟨y, rfl⟩
            apply Subtype.ext
            change (F.d 1 0).hom y.1 = 0
            exact y.2
      | succ n =>
          intro x
          constructor
          · intro hx
            refine ⟨⟨x, ?_⟩, ?_⟩
            · have hxval : (F.d (n + 2) (n + 1)).hom x = 0 := by
                exact congrArg Subtype.val hx
              exact hxval
            · rfl
          · rintro ⟨y, rfl⟩
            apply Subtype.ext
            change (F.d (n + 2) (n + 1)).hom y.1 = 0
            exact y.2

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 104 9: each syzygy row in a finite free resolution is short
exact. -/
private lemma syzygyShortComplex_shortExact
    {F : ChainComplex (ModuleCat R) ℕ} {π : F ⟶ moduleSingle[R]M}
    (hπ : IsFiniteFreeResolution π) (n : ℕ) :
    (syzygyShortComplex π n).ShortExact := by
  -- Package the tautological kernel exactness together with surjectivity from the resolution.
  refine ModuleCat.shortComplex_shortExact (syzygyShortComplex π n) ?_ ?_ ?_
  · simpa [syzygyShortComplex] using syzygyRow_function_exact (π := π) n
  · simpa [syzygyShortComplex] using syzygyInclusion_injective (π := π) n
  · simpa [syzygyShortComplex] using syzygyToPrevious_surjective (π := π) hπ n

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 104 9: every syzygy in a finite free resolution is finite. -/
private lemma resolutionSyzygy_finite
    {F : ChainComplex (ModuleCat R) ℕ} {π : F ⟶ moduleSingle[R]M}
    (hπ : IsFiniteFreeResolution π) (n : ℕ) :
    Module.Finite R (resolutionSyzygy π n) := by
  letI : IsFiniteFreeResolution π := hπ
  -- Degree zero is finite by hypothesis; higher syzygies are kernels inside finite free terms.
  cases n with
  | zero =>
      infer_instance
  | succ n =>
      cases n with
      | zero =>
          let _ : Module.Finite R (F.X 0) := IsFiniteFreeResolution.finite π 0
          simpa [resolutionSyzygy] using kernel_finite_of_domain_finite (R := R) (π.f 0)
      | succ n =>
          let _ : Module.Finite R (F.X (n + 1)) := IsFiniteFreeResolution.finite π (n + 1)
          simpa [resolutionSyzygy] using
            kernel_finite_of_domain_finite (R := R) (F.d (n + 1) n)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 104 9: a finite subsingleton module has infinite depth. -/
private theorem moduleDepth_eq_top_of_subsingleton_for_entry
    (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N] [Subsingleton N] :
    moduleDepth R N = ⊤ := by
  -- In a zero module the maximal ideal already multiplies the whole module onto itself.
  have htopbot : (⊤ : Submodule R N) = ⊥ := by
    ext x
    simp [Subsingleton.elim x 0]
  have hsmul_bot : IsLocalRing.maximalIdeal R • (⊥ : Submodule R N) = ⊥ := by
    ext x
    simp
  have hsmul : IsLocalRing.maximalIdeal R • (⊤ : Submodule R N) = ⊤ := by
    rw [htopbot, hsmul_bot]
  change Ideal.depth (IsLocalRing.maximalIdeal R) N = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (IsLocalRing.maximalIdeal R) N hsmul

/-- Helper for Chap10 Lemma 10 104 9: a nonzero finite module has depth bounded by the ambient
Krull dimension. -/
private theorem moduleDepth_le_ringKrullDim_of_nontrivial_for_entry
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N] [Nontrivial N]
    {d : ℕ} (hdim : ringKrullDim R = d) :
    moduleDepth R N ≤ d := by
  -- The standard depth-support inequality and the support bound give the numerical estimate.
  have hdepth : WithBot.some (moduleDepth R N : ℕ∞) ≤ Module.supportDim R N :=
    depth_le_supportDim (R := R) (M := N)
  have hsupp : Module.supportDim R N ≤ ringKrullDim R :=
    Module.supportDim_le_ringKrullDim (R := R) (M := N)
  have hsupp_le_d : Module.supportDim R N ≤ d := by
    simpa [hdim] using hsupp
  have hle : WithBot.some (moduleDepth R N : ℕ∞) ≤ d :=
    le_trans hdepth hsupp_le_d
  exact WithBot.coe_le_coe.mp hle

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 104 9: a linear equivalence preserves the regular-sequence
lengths used to compute ideal depth. -/
private theorem regularSequenceLengths_eq_of_linearEquiv_for_entry
    {N P : Type u} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (I : Ideal R) (e : N ≃ₗ[R] P) :
    Ideal.regularSequenceLengths I N = Ideal.regularSequenceLengths I P := by
  -- Transport regular sequences across the equivalence in both directions.
  ext n
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 104 9: ideal depth is invariant under a linear equivalence of
finite modules. -/
private theorem idealDepth_eq_of_linearEquiv_for_entry
    {N P : Type u} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    [Module.Finite R N] [Module.Finite R P] (I : Ideal R) (e : N ≃ₗ[R] P) :
    Ideal.depth I N = Ideal.depth I P := by
  -- The top-smul branch and the regular-sequence branch both transport along the equivalence.
  have htop : I • (⊤ : Submodule R N) = ⊤ ↔ I • (⊤ : Submodule R P) = ⊤ := by
    constructor
    · intro h
      have hmap := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using hmap
    · intro h
      have hmap := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using hmap
  by_cases hN : I • (⊤ : Submodule R N) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I N hN,
      Ideal.depth_eq_top_of_smul_top I P (htop.mp hN)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N hN,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I P (mt htop.mpr hN),
      regularSequenceLengths_eq_of_linearEquiv_for_entry (R := R) (N := N) (P := P) I e]

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 104 9: module depth is invariant under linear equivalence of
finite modules. -/
private theorem moduleDepth_eq_of_linearEquiv_for_entry
    {N P : Type u} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    [Module.Finite R N] [Module.Finite R P] (e : N ≃ₗ[R] P) :
    moduleDepth R N = moduleDepth R P := by
  -- Specialize ideal-depth invariance to the maximal ideal of the local ring.
  simpa [moduleDepth] using
    idealDepth_eq_of_linearEquiv_for_entry (R := R) (N := N) (P := P)
      (IsLocalRing.maximalIdeal R) e

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 104 9: a Cohen-Macaulay local ring is nontrivial. -/
private theorem nontrivial_of_cohenMacaulay_self_for_entry
    (hCM : Module.CohenMacaulay R R) : Nontrivial R := by
  -- If the ring were zero, the self support dimension would be bottom, contradicting the
  -- Cohen-Macaulay equality with a concrete depth value.
  by_contra hR
  letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
  have hsupp : Module.supportDim R R = ⊥ :=
    Module.supportDim_eq_bot_of_subsingleton (R := R) (M := R)
  have hdepth : Module.supportDim R R = .some (moduleDepth R R) :=
    hCM.supportDim_eq_moduleDepth
  simpa [hsupp] using hdepth

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 104 9: the self-module of a Cohen-Macaulay local ring has depth
equal to the Krull dimension. -/
private theorem moduleDepth_self_eq_ringKrullDim_for_entry
    {d : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d) :
    moduleDepth R R = d := by
  -- Rewrite the Cohen-Macaulay self-module equality using the ring's support dimension.
  have hdepth : WithBot.some (moduleDepth R R : ℕ∞) = d := by
    simpa [Module.supportDim_self_eq_ringKrullDim, hdim] using hCM.supportDim_eq_moduleDepth.symm
  exact WithBot.coe_eq_coe.mp hdepth

/-- Helper for Chap10 Lemma 10 104 9: a positive finite power of the ring has depth equal to the
Cohen-Macaulay dimension. -/
private theorem moduleDepth_piFinSucc_eq_ringKrullDim_for_entry
    {d : ℕ} (n : ℕ) (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d) :
    moduleDepth R (Fin n.succ → R) = d := by
  letI : Nontrivial R := nontrivial_of_cohenMacaulay_self_for_entry (R := R) hCM
  have hRdepth : moduleDepth R R = d :=
    moduleDepth_self_eq_ringKrullDim_for_entry (R := R) hCM hdim
  -- Induct through the split exact sequence `0 → R → R × R^n → R^n → 0`.
  induction n with
  | zero =>
      simpa [hRdepth] using
        moduleDepth_eq_of_linearEquiv_for_entry (R := R)
          (N := Fin 1 → R) (P := R) (LinearEquiv.funUnique (Fin 1) R R)
  | succ n ih =>
      have hcomp :
          (LinearMap.snd R R (Fin n.succ → R)).comp
            (LinearMap.inl R R (Fin n.succ → R)) = 0 := by
        ext x
        rfl
      let T : ShortComplex (ModuleCat R) :=
        ModuleCat.shortComplexOfCompEqZero
          (LinearMap.inl R R (Fin n.succ → R))
          (LinearMap.snd R R (Fin n.succ → R))
          hcomp
      have hT : T.ShortExact :=
        ModuleCat.shortComplex_shortExact T
          Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective
      have hmid_ge : moduleDepth R (R × (Fin n.succ → R)) ≥ d := by
        have hmiddle := CategoryTheory.ShortComplex.ShortExact.moduleDepth_middle_ge_min
          (R := R) (S := T) hT
        simpa [T, hRdepth, ih] using hmiddle
      have hmid_le : moduleDepth R (R × (Fin n.succ → R)) ≤ d :=
        moduleDepth_le_ringKrullDim_of_nontrivial_for_entry (R := R)
          (N := R × (Fin n.succ → R)) hdim
      have hmid : moduleDepth R (R × (Fin n.succ → R)) = d :=
        le_antisymm hmid_le hmid_ge
      calc
        moduleDepth R (Fin n.succ.succ → R)
            = moduleDepth R (R × (Fin n.succ → R)) := by
              symm
              exact moduleDepth_eq_of_linearEquiv_for_entry (R := R)
                (N := R × (Fin n.succ → R)) (P := Fin n.succ.succ → R)
                (Fin.consLinearEquiv R (fun _ : Fin n.succ.succ => R))
        _ = d := hmid

/-- Helper for Chap10 Lemma 10 104 9: every nonzero finite free module over a Cohen-Macaulay
local ring has depth equal to the ambient Krull dimension. -/
private theorem moduleDepth_eq_ringKrullDim_of_nontrivial_finite_free_for_entry
    {d : ℕ} {P : Type u} [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P]
    [Nontrivial P] (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d) :
    moduleDepth R P = d := by
  let b : Module.Basis (Module.Free.ChooseBasisIndex R P) R P := Module.Free.chooseBasis R P
  let ι := Module.Free.ChooseBasisIndex R P
  letI : Finite ι := Module.Finite.finite_basis b
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let eBasis : (ι → R) ≃ₗ[R] P := b.equivFun.symm
  let eFin : (Fin (Fintype.card ι) → R) ≃ₗ[R] (ι → R) :=
    LinearEquiv.funCongrLeft R R (Fintype.equivFin ι)
  have hι_nonempty : Nonempty ι := by
    by_contra hι
    letI : IsEmpty ι := not_nonempty_iff.mp hι
    have hsub : Subsingleton P := by
      refine ⟨fun x y ↦ ?_⟩
      have hxy : eBasis.symm x = eBasis.symm y := Subsingleton.elim _ _
      exact eBasis.symm.injective hxy
    exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance
  have hcard_ne_zero : Fintype.card ι ≠ 0 :=
    Nat.ne_of_gt (Fintype.card_pos_iff.mpr hι_nonempty)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hcard_ne_zero
  -- Choose finite coordinates for the free module and invoke the `Fin`-indexed computation.
  calc
    moduleDepth R P = moduleDepth R (ι → R) := by
      symm
      exact moduleDepth_eq_of_linearEquiv_for_entry (R := R) (N := ι → R) (P := P) eBasis
    _ = moduleDepth R (Fin (Fintype.card ι) → R) := by
      symm
      exact moduleDepth_eq_of_linearEquiv_for_entry (R := R)
        (N := Fin (Fintype.card ι) → R) (P := ι → R) eFin
    _ = d := by
      rw [hn]
      exact moduleDepth_piFinSucc_eq_ringKrullDim_for_entry (R := R) n hCM hdim

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 104 9: a module whose finite depth equals the ring dimension is
maximal Cohen-Macaulay. -/
private theorem maximalCohenMacaulay_of_moduleDepth_eq_ringKrullDim_for_entry
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {d : ℕ} (hdim : ringKrullDim R = d) (hdepthN : moduleDepth R N = d) :
    Module.MaximalCohenMacaulay R N := by
  -- The class field is exactly the finite-depth equality after rewriting the dimension.
  refine { depth_eq_ringKrullDim := ?_ }
  simpa [hdepthN, hdim]

/-- Helper for Chap10 Lemma 10 104 9: the elementary `WithTop` inequality used to advance the
forward depth bound by one syzygy. -/
private lemma min_coe_succ_le_add_one_of_min_coe_le
    {d b : ℕ} {y : ℕ∞} (hy : min (d : ℕ∞) (b : ℕ∞) ≤ y) :
    min (d : ℕ∞) ((b + 1 : ℕ) : ℕ∞) ≤ y + 1 := by
  -- Split according to whether the current numerical bound has already reached the dimension.
  by_cases hb : b < d
  · have hb_le_d : b ≤ d := Nat.le_of_lt hb
    have hb_le_d_top : (b : ℕ∞) ≤ d := by
      exact_mod_cast hb_le_d
    have hb_y : (b : ℕ∞) ≤ y := by
      simpa [min_eq_right hb_le_d_top] using hy
    have hb_succ_le : ((b + 1 : ℕ) : ℕ∞) ≤ y + 1 := by
      simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
        add_le_add hb_y (le_rfl : (1 : ℕ∞) ≤ 1)
    exact le_trans (min_le_right _ _) hb_succ_le
  · have hd_le_b : d ≤ b := le_of_not_gt hb
    have hd_le_b_top : (d : ℕ∞) ≤ b := by
      exact_mod_cast hd_le_b
    have hd_y : (d : ℕ∞) ≤ y := by
      simpa [min_eq_left hd_le_b_top] using hy
    have hd_y_succ : (d : ℕ∞) ≤ y + 1 := by
      have hy_le_succ : y ≤ y + 1 := by
        simp
      exact le_trans hd_y hy_le_succ
    exact le_trans (min_le_left _ _) hd_y_succ

omit [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 104 9: finite free terms have depth at least the Cohen-Macaulay
dimension. -/
private lemma freeTerm_depth_ge_ringKrullDim
    {d : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    {F : ChainComplex (ModuleCat R) ℕ} {π : F ⟶ moduleSingle[R]M}
    (hπ : IsFiniteFreeResolution π) (n : ℕ) :
    letI : IsFiniteFreeResolution π := hπ
    letI : Module.Finite R (F.X n) := IsFiniteFreeResolution.finite π n
    (d : ℕ∞) ≤ moduleDepth R (F.X n) := by
  letI : IsFiniteFreeResolution π := hπ
  letI : Module.Finite R (F.X n) := IsFiniteFreeResolution.finite π n
  letI : Module.Free R (F.X n) := IsFreeResolution.free π n
  -- A finite free term is either zero, with infinite depth, or nonzero of depth exactly `d`.
  by_cases hsub : Subsingleton (F.X n)
  · have htop : moduleDepth R (F.X n) = ⊤ :=
      moduleDepth_eq_top_of_subsingleton_for_entry (R := R) (F.X n)
    rw [htop]
    exact le_top
  · letI : Nontrivial (F.X n) := not_subsingleton_iff_nontrivial.mp hsub
    rw [moduleDepth_eq_ringKrullDim_of_nontrivial_finite_free_for_entry
      (R := R) (P := F.X n) hCM hdim]

/-- Helper for Chap10 Lemma 10 104 9: the `n`th syzygy has depth at least
`min d (e + n)`. -/
private lemma syzygyDepth_lowerBound_of_isFiniteFreeResolution
    {d e : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hdepth : moduleDepth R M = e) {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R]M} (hπ : IsFiniteFreeResolution π) (n : ℕ) :
    letI : Module.Finite R (resolutionSyzygy π n) := resolutionSyzygy_finite (π := π) hπ n
    min (d : ℕ∞) ((e + n : ℕ) : ℕ∞) ≤ moduleDepth R (resolutionSyzygy π n) := by
  letI : Module.Finite R (resolutionSyzygy π n) := resolutionSyzygy_finite (π := π) hπ n
  -- Iterate the left-depth inequality along the short exact syzygy rows.
  induction n with
  | zero =>
      simpa [resolutionSyzygy, hdepth] using min_le_right (d : ℕ∞) (e : ℕ∞)
  | succ n ih =>
      let S : ShortComplex (ModuleCat R) := syzygyShortComplex π n
      have hS : S.ShortExact := by
        simpa [S] using syzygyShortComplex_shortExact (π := π) hπ n
      letI : Module.Finite R S.X₁ := by
        simpa [S, syzygyShortComplex] using resolutionSyzygy_finite (π := π) hπ (n + 1)
      letI : Module.Finite R S.X₃ := by
        simpa [S, syzygyShortComplex] using resolutionSyzygy_finite (π := π) hπ n
      letI : IsFiniteFreeResolution π := hπ
      letI : Module.Finite R (F.X n) := IsFiniteFreeResolution.finite π n
      letI : Module.Finite R (resolutionSyzygy π n) := resolutionSyzygy_finite (π := π) hπ n
      have hleft := CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min
        (R := R) (S := S) hS
      have hfree : (d : ℕ∞) ≤ moduleDepth R (F.X n) :=
        freeTerm_depth_ge_ringKrullDim (R := R) (M := M) hCM hdim (π := π) hπ n
      have hstep :
          min (d : ℕ∞) ((e + n + 1 : ℕ) : ℕ∞) ≤
            min (moduleDepth R (F.X n)) (moduleDepth R (resolutionSyzygy π n) + 1) := by
        refine le_min ?_ ?_
        · exact le_trans (min_le_left _ _) hfree
        · simpa [Nat.add_assoc] using
            min_coe_succ_le_add_one_of_min_coe_le (d := d) (b := e + n) (y := moduleDepth R (resolutionSyzygy π n)) ih
      have hleft' :
          min (moduleDepth R (F.X n)) (moduleDepth R (resolutionSyzygy π n) + 1) ≤
          moduleDepth R (resolutionSyzygy π (n + 1)) := by
        simpa [S, syzygyShortComplex] using hleft
      exact le_trans hstep hleft'

/-- Helper for Chap10 Lemma 10 104 9: if an extended natural is at least `a + 1`, then after
subtracting one it is at least `a`. -/
private lemma enat_le_sub_one_of_succ_le_for_entry {a : ℕ} {b : ℕ∞}
    (h : (((a + 1 : ℕ) : ℕ∞)) ≤ b) :
    ((a : ℕ) : ℕ∞) ≤ b - (1 : ℕ∞) := by
  -- Convert the successor lower bound to a strict inequality, then use the ENat predecessor API.
  have hsucc : (a : ℕ∞) + 1 ≤ b := by
    simpa [Nat.cast_add] using h
  have hlt : (a : ℕ∞) < b :=
    (ENat.add_one_le_iff (ENat.coe_ne_top a)).mp hsucc
  exact ENat.le_sub_one_of_lt hlt

/-- Helper for Chap10 Lemma 10 104 9: one short exact syzygy row propagates a depth lower bound
one step backward. -/
private lemma syzygyDepth_backward_step_of_next_bound
    {d a k : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    {F : ChainComplex (ModuleCat R) ℕ} {π : F ⟶ moduleSingle[R]M}
    (hπ : IsFiniteFreeResolution π) (ha : a ≤ d) :
    letI : Module.Finite R (resolutionSyzygy π (k + 1)) :=
      resolutionSyzygy_finite (π := π) hπ (k + 1)
    letI : Module.Finite R (resolutionSyzygy π k) := resolutionSyzygy_finite (π := π) hπ k
    (((a + 1 : ℕ) : ℕ∞)) ≤ moduleDepth R (resolutionSyzygy π (k + 1)) →
    ((a : ℕ) : ℕ∞) ≤ moduleDepth R (resolutionSyzygy π k) := by
  letI : Module.Finite R (resolutionSyzygy π (k + 1)) :=
    resolutionSyzygy_finite (π := π) hπ (k + 1)
  letI : Module.Finite R (resolutionSyzygy π k) := resolutionSyzygy_finite (π := π) hπ k
  intro hnext
  -- Apply the right-term depth inequality to the row `K_{k+1} -> F_k -> K_k`.
  let S : ShortComplex (ModuleCat R) := syzygyShortComplex π k
  have hS : S.ShortExact := by
    simpa [S] using syzygyShortComplex_shortExact (π := π) hπ k
  have hfin_left : Module.Finite R S.X₁ := by
    simpa [S, syzygyShortComplex] using resolutionSyzygy_finite (π := π) hπ (k + 1)
  have hfin_right : Module.Finite R S.X₃ := by
    simpa [S, syzygyShortComplex] using resolutionSyzygy_finite (π := π) hπ k
  letI : Module.Finite R S.X₁ := hfin_left
  letI : Module.Finite R S.X₃ := hfin_right
  letI : IsFiniteFreeResolution π := hπ
  letI : Module.Finite R (F.X k) := IsFiniteFreeResolution.finite π k
  have hright := CategoryTheory.ShortComplex.ShortExact.moduleDepth_right_ge_min
    (R := R) (S := S) hS
  have hfree : ((a : ℕ) : ℕ∞) ≤ moduleDepth R (F.X k) := by
    have hfree_d : (d : ℕ∞) ≤ moduleDepth R (F.X k) :=
      freeTerm_depth_ge_ringKrullDim (R := R) (M := M) hCM hdim (π := π) hπ k
    have ha_enat : ((a : ℕ) : ℕ∞) ≤ d := by
      exact_mod_cast ha
    exact le_trans ha_enat hfree_d
  have hleft_pred :
      ((a : ℕ) : ℕ∞) ≤ moduleDepth R (resolutionSyzygy π (k + 1)) - (1 : ℕ∞) :=
    enat_le_sub_one_of_succ_le_for_entry hnext
  have hrow_lower :
      ((a : ℕ) : ℕ∞) ≤
        min (moduleDepth R (F.X k))
          (moduleDepth R (resolutionSyzygy π (k + 1)) - (1 : ℕ∞)) := by
    exact le_min hfree hleft_pred
  have hrow :
      min (moduleDepth R (F.X k))
          (moduleDepth R (resolutionSyzygy π (k + 1)) - (1 : ℕ∞)) ≤
        moduleDepth R (resolutionSyzygy π k) := by
    simpa [S, syzygyShortComplex] using hright
  exact le_trans hrow_lower hrow

/-- Helper for Chap10 Lemma 10 104 9: the backward syzygy depth step is stable under a
propositionally equal spelling of the next index. -/
private lemma syzygyDepth_backward_step_of_next_bound_eq
    {d a k l : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    {F : ChainComplex (ModuleCat R) ℕ} {π : F ⟶ moduleSingle[R]M}
    (hπ : IsFiniteFreeResolution π) (ha : a ≤ d) (hidx : l = k + 1) :
    letI : Module.Finite R (resolutionSyzygy π l) := resolutionSyzygy_finite (π := π) hπ l
    letI : Module.Finite R (resolutionSyzygy π k) := resolutionSyzygy_finite (π := π) hπ k
    (((a + 1 : ℕ) : ℕ∞)) ≤ moduleDepth R (resolutionSyzygy π l) →
    ((a : ℕ) : ℕ∞) ≤ moduleDepth R (resolutionSyzygy π k) := by
  -- Replace the alternate next-index spelling by the canonical `k + 1` form before descending.
  subst l
  exact syzygyDepth_backward_step_of_next_bound
    (R := R) (M := M) hCM hdim (π := π) hπ ha

/-- Helper for Chap10 Lemma 10 104 9: a subsingleton tail syzygy forces a lower depth bound at
the original module after descending through the finite syzygy tower. -/
private lemma syzygyDepth_zero_ge_of_subsingleton_tail
    {d n : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    {F : ChainComplex (ModuleCat R) ℕ} {π : F ⟶ moduleSingle[R]M}
    (hπ : IsFiniteFreeResolution π) (hn : n ≤ d)
    [Subsingleton (resolutionSyzygy π n)] :
    (((d + 1 - n : ℕ) : ℕ∞)) ≤ moduleDepth R M := by
  letI : Module.Finite R (resolutionSyzygy π n) := resolutionSyzygy_finite (π := π) hπ n
  have htail_top : moduleDepth R (resolutionSyzygy π n) = ⊤ :=
    moduleDepth_eq_top_of_subsingleton_for_entry (R := R) (resolutionSyzygy π n)
  -- Descend a distance `m` from the tail, losing exactly one unit of depth at each row.
  have hdesc :
      ∀ m, m ≤ n →
        letI : Module.Finite R (resolutionSyzygy π (n - m)) :=
          resolutionSyzygy_finite (π := π) hπ (n - m)
        (((d + 1 - m : ℕ) : ℕ∞)) ≤
          moduleDepth R (resolutionSyzygy π (n - m)) := by
    intro m
    induction m with
    | zero =>
        letI : Module.Finite R (resolutionSyzygy π (n - 0)) :=
          resolutionSyzygy_finite (π := π) hπ (n - 0)
        intro _hm
        simpa [htail_top] using (le_top : ((d + 1 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞))
    | succ m ih =>
        letI : Module.Finite R (resolutionSyzygy π (n - (m + 1))) :=
          resolutionSyzygy_finite (π := π) hπ (n - (m + 1))
        intro hm_succ
        have hm_le_n : m ≤ n := Nat.le_trans (Nat.le_succ m) hm_succ
        have hm_lt_n : m < n := Nat.lt_of_succ_le hm_succ
        have hm_le_d : m ≤ d := Nat.le_trans hm_le_n hn
        let a := d + 1 - (m + 1)
        have ha : a ≤ d := by
          omega
        letI : Module.Finite R (resolutionSyzygy π (n - m)) :=
          resolutionSyzygy_finite (π := π) hπ (n - m)
        have hnext_raw := ih hm_le_n
        letI : Module.Finite R (resolutionSyzygy π ((n - (m + 1)) + 1)) :=
          resolutionSyzygy_finite (π := π) hπ ((n - (m + 1)) + 1)
        have hnext :
            (((a + 1 : ℕ) : ℕ∞)) ≤ moduleDepth R (resolutionSyzygy π (n - m)) := by
          have hbound : a + 1 = d + 1 - m := by
            omega
          simpa only [hbound] using hnext_raw
        have hindex : n - m = (n - (m + 1)) + 1 := by
          omega
        have hstep :=
          syzygyDepth_backward_step_of_next_bound_eq
            (R := R) (M := M) (k := n - (m + 1)) (l := n - m)
            hCM hdim (π := π) hπ ha hindex hnext
        simpa [a] using hstep
  -- Evaluate the descent after the full distance `n`, where `K_0` is the original module.
  have hzero := hdesc n le_rfl
  have hnn : n - n = 0 := Nat.sub_self n
  rw [hnn] at hzero
  simpa [resolutionSyzygy] using hzero

/-- Chap10 Lemma 10 104 9: the target syzygy at index `d - e` is nonzero. -/
private theorem targetSyzygy_nontrivial_of_moduleDepth
    {d e : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hdepth : moduleDepth R M = e) {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R]M} (hπ : IsFiniteFreeResolution π) :
    Nontrivial (resolutionSyzygy π (d - e)) := by
  -- First record that `M` is nonzero and hence its finite depth is bounded by the ring dimension.
  have hM_nontrivial : Nontrivial M := by
    by_contra hM
    letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
    have htop : moduleDepth R M = ⊤ :=
      moduleDepth_eq_top_of_subsingleton_for_entry (R := R) M
    simpa [hdepth] using htop
  have he_le_d : e ≤ d := by
    letI : Nontrivial M := hM_nontrivial
    have hle : moduleDepth R M ≤ d :=
      moduleDepth_le_ringKrullDim_of_nontrivial_for_entry (R := R) (N := M) hdim
    simpa [hdepth] using hle
  -- If the target syzygy were zero, backward descent would force `depth M ≥ e + 1`.
  by_contra htarget
  let n := d - e
  have hsub : Subsingleton (resolutionSyzygy π n) := by
    exact not_nontrivial_iff_subsingleton.mp (by simpa [n] using htarget)
  have hn_le_d : n ≤ d := by
    simp [n]
  letI : Subsingleton (resolutionSyzygy π n) := hsub
  have hM_ge :
      (((d + 1 - n : ℕ) : ℕ∞)) ≤ moduleDepth R M :=
    syzygyDepth_zero_ge_of_subsingleton_tail (R := R) (M := M) hCM hdim
      (π := π) hπ hn_le_d
  have hsucc_le :
      (((e + 1 : ℕ) : ℕ∞)) ≤ ((e : ℕ) : ℕ∞) := by
    have hnat : d + 1 - n = e + 1 := by
      omega
    simpa [hdepth, hnat] using hM_ge
  exact (Nat.not_succ_le_self e) (ENat.coe_le_coe.mp hsucc_le)

/-- Helper for Chap10 Lemma 10 104 9: every chosen finite free resolution has maximal Cohen-Macaulay
`(d - e)`th syzygy when `moduleDepth R M = e`. -/
private theorem isFiniteFreeResolution_syzygy_maximalCohenMacaulay_of_moduleDepth
    {d e : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hdepth : moduleDepth R M = e) {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R]M} (hπ : IsFiniteFreeResolution π) :
    ChainComplex.SyzygyMaximalCohenMacaulay π (d - e) := by
  -- The main skeleton is: bound the target syzygy depth below by `d`, bound it above by the
  -- support-dimension estimate using nontriviality, and then assemble the MCM class.
  have hM_nontrivial : Nontrivial M := by
    by_contra hM
    letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
    have htop : moduleDepth R M = ⊤ :=
      moduleDepth_eq_top_of_subsingleton_for_entry (R := R) M
    simpa [hdepth] using htop
  have he_le_d : e ≤ d := by
    letI : Nontrivial M := hM_nontrivial
    have hle : moduleDepth R M ≤ d :=
      moduleDepth_le_ringKrullDim_of_nontrivial_for_entry (R := R) (N := M) hdim
    simpa [hdepth] using hle
  let n := d - e
  letI : Module.Finite R (resolutionSyzygy π n) :=
    resolutionSyzygy_finite (π := π) hπ n
  letI : Nontrivial (resolutionSyzygy π n) := by
    simpa [n] using
      targetSyzygy_nontrivial_of_moduleDepth (R := R) (M := M) hCM hdim hdepth hπ
  have hlower :
      (d : ℕ∞) ≤ moduleDepth R (resolutionSyzygy π n) := by
    have hbound :=
      syzygyDepth_lowerBound_of_isFiniteFreeResolution
        (R := R) (M := M) hCM hdim hdepth hπ n
    have hsum : e + n = d := by
      simpa [n, Nat.add_comm] using Nat.add_sub_of_le he_le_d
    simpa [hsum] using hbound
  have hupper : moduleDepth R (resolutionSyzygy π n) ≤ d :=
    moduleDepth_le_ringKrullDim_of_nontrivial_for_entry (R := R)
      (N := resolutionSyzygy π n) hdim
  have hdepth_target : moduleDepth R (resolutionSyzygy π n) = d :=
    le_antisymm hupper hlower
  have hMCM : Module.MaximalCohenMacaulay R (resolutionSyzygy π n) :=
    maximalCohenMacaulay_of_moduleDepth_eq_ringKrullDim_for_entry
      (R := R) (N := resolutionSyzygy π n) hdim hdepth_target
  -- Finally unfold the public syzygy predicate at the fixed target index.
  change ChainComplex.SyzygyMaximalCohenMacaulay π n
  cases hn : n with
  | zero =>
      rw [hn] at hMCM
      simpa [ChainComplex.SyzygyMaximalCohenMacaulay, resolutionSyzygy] using hMCM
  | succ n' =>
      cases n' with
      | zero =>
          rw [hn] at hMCM
          simpa [ChainComplex.SyzygyMaximalCohenMacaulay, resolutionSyzygy] using hMCM
      | succ n'' =>
          rw [hn] at hMCM
          simpa [ChainComplex.SyzygyMaximalCohenMacaulay, resolutionSyzygy] using hMCM

-- Proof sketch: choose any finite free resolution of `M`, then invoke the chosen-resolution
-- helper above to obtain the maximal Cohen-Macaulay syzygy at the source-prescribed stage.
/-- Companion form for Chap10 Lemma 10 104 9: if `R` is a local Noetherian Cohen-Macaulay ring of dimension `d` and
`M` is a finite `R`-module of depth `e`, then `M` admits a finite free resolution whose
`(d - e)`th syzygy is maximal Cohen-Macaulay. Equivalently, truncating that resolution after
`d - e` steps gives an exact complex
`0 → K → F_{d - e - 1} → ⋯ → F₀ → M → 0`
with the `Fᵢ` finite free and `K` maximal Cohen-Macaulay. With the chapter's convention, the `0`th
syzygy is `M` itself, the `1`st syzygy is `ker (F₀ ⟶ M)`, and the `(n + 2)`nd syzygy is
`ker (F_{n+1} ⟶ F_n)`. -/
@[stacks 00NG]
theorem exists_maximalCohenMacaulay_syzygy_of_moduleDepth
    {d e : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hdepth : moduleDepth R M = e) :
    ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R] M),
      IsFiniteFreeResolution π ∧
      SyzygyMaximalCohenMacaulay π (d - e) := by
  -- Choose a finite free resolution and transfer the remaining work to the chosen-resolution
  -- helper.
  rcases module_exists_finite_free_resolution (R := R) (M := M) with ⟨F, π, hπ⟩
  refine ⟨F, π, hπ, ?_⟩
  exact isFiniteFreeResolution_syzygy_maximalCohenMacaulay_of_moduleDepth
    (R := R) (M := M) hCM hdim hdepth hπ

/-- Companion form for Chap10 Lemma 10 104 9: every chosen finite free resolution of `M` has
maximal Cohen-Macaulay `(d - e)`th syzygy. -/
theorem maximalCohenMacaulay_syzygy_of_isFiniteFreeResolution_of_moduleDepth
    {d e : ℕ} (hCM : Module.CohenMacaulay R R) (hdim : ringKrullDim R = d)
    (hdepth : moduleDepth R M = e) {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R]M} (hπ : IsFiniteFreeResolution π) :
    SyzygyMaximalCohenMacaulay π (d - e) := by
  -- Reuse the private chosen-resolution helper directly; this is the source-facing fixed
  -- resolution form of the lemma.
  exact isFiniteFreeResolution_syzygy_maximalCohenMacaulay_of_moduleDepth
    (R := R) (M := M) hCM hdim hdepth hπ

end
