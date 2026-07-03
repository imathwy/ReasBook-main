import Mathlib
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_10_110_1 (from Chap10) -/
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

/-! ### Lemma_10_110_2 (from Chap10) -/
universe u

section

open CategoryTheory

variable {R : Type u} [CommRing R]

/-
Source/core/bridge triage:
- `source-facing`: the local-global criterion saying that a Noetherian ring has finite global
  dimension exactly when its maximal-ideal localizations admit one uniform bound;
- `core/canonical`: the chapter owner abstractions `HasGlobalDimensionLE R n` and
  `IsFiniteGlobalDimensionRing R`;
- `bridge/view`: the localization instance from Lemma `10.109.13`, applied to
  `Localization.AtPrime m.asIdeal`.

Primitive data is the owner bound `HasGlobalDimensionLE R n`. The family of bounds on maximal
localizations is derived API coming from that owner, not a second notion of finite global
dimension.
-/

variable [IsNoetherianRing R]

-- Proof sketch: one direction is localization stability of a global-dimension bound, applied to
-- each maximal localization. For the converse, use Lemma `10.109.12` to reduce
-- `HasGlobalDimensionLE R n` to cyclic quotients `R ⧸ I`, and apply the mathlib local criterion
-- `ModuleCat.hasProjectiveDimensionLE_iff_forall_maximalSpectrum` to each cyclic quotient. The
-- given maximal-localization bounds supply the localized projective-dimension estimates directly.
/-- Lemma 10.110.2: a Noetherian ring has finite global dimension if and only if there is a
uniform integer `n` such that every localization `R_𝔪` at a maximal ideal `𝔪` has global
dimension at most `n`. -/
theorem isFiniteGlobalDimensionRing_iff_exists_uniform_bound_localizationAtMaximal :
    IsFiniteGlobalDimensionRing R ↔
      ∃ n : ℕ, ∀ m : MaximalSpectrum R,
        HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) n := by
  constructor
  · intro _
    exact ⟨globalDimension R, fun _ ↦ inferInstance⟩
  · rintro ⟨n, hn⟩
    have hcyclic : ∀ I : Ideal R, HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) n := by
      intro I
      exact ((ModuleCat.of R (R ⧸ I)).hasProjectiveDimensionLE_iff_forall_maximalSpectrum n).2
        fun m ↦ by
          let _ : HasGlobalDimensionLE (Localization.AtPrime m.asIdeal) n := hn m
          simpa [Localization.AtPrime] using
            (inferInstance : HasProjectiveDimensionLE
              ((ModuleCat.of R (R ⧸ I)).localizedModule m.asIdeal.primeCompl) n)
    have hglobal : HasGlobalDimensionLE R n :=
      ((globalDimensionLE_tfae_finite_and_cyclic_modules n).out 2 0).mp hcyclic
    exact ⟨⟨n, hglobal⟩⟩

end

/-! ### Lemma_10_110_3 (from Chap10) -/
universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/-
Domain triage:
* primary domain: homological bounds for the residue field of a Noetherian local ring;
* sampled owner declarations:
  `CategoryTheory.projectiveDimension`,
  `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`,
  `IsRegularLocalRing.iff_finrank_cotangentSpace`,
  `projectiveDimension_le_iff`;
* owner abstraction: the canonical owners are `projectiveDimension` on `ModuleCat R` and
  `CotangentSpace R` for the embedding-dimension side;
* layer: `source-facing`, since the textbook item is the lower bound comparing these two canonical
  invariants rather than defining a new owner object.
-/

-- Proof sketch: choose a basis of the cotangent space `CotangentSpace R = maximalIdeal R / (maximalIdeal R)^2`
-- and the corresponding Koszul complex. Compare it with a minimal finite free resolution of
-- `ResidueField R`; after tensoring with the residue field, the comparison maps are injective in
-- each degree, forcing the resolution to be nonzero through degree
-- `Module.finrank (ResidueField R) (CotangentSpace R)`.
/-- Helper for Lemma 10.110.3: the residue-field module is nonzero in `ModuleCat R`. -/
lemma residueField_module_not_isZero :
    ¬ Limits.IsZero (ModuleCat.of R (ResidueField R)) := by
  -- A field is nontrivial, so its image in `ModuleCat` cannot be a zero object.
  intro hzero
  have hsub :
      Subsingleton (ResidueField R) :=
    (ModuleCat.isZero_iff_subsingleton (M := ModuleCat.of R (ResidueField R))).1 hzero
  have hnontrivial : Nontrivial (ResidueField R) := inferInstance
  exact (not_subsingleton_iff_nontrivial.mpr hnontrivial) hsub

/-- Helper for Lemma 10.110.3: a successor projective-dimension bound on the residue field
produces a bounded finite free resolution of the preceding length. -/
lemma residueField_hasFiniteFreeResolutionLengthLE_of_hasProjectiveDimensionLT_succ
    {d : ℕ}
    (hpd : HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) (d + 1)) :
    HasFiniteFreeResolutionLengthLE R (ResidueField R) d := by
  -- Rewrite `< d + 1` as `≤ d`, then invoke the finite-free-resolution bridge from
  -- Lemma `10.109.7`.
  have hle : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) d := by
    simpa [CategoryTheory.HasProjectiveDimensionLE] using hpd
  exact
    (hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE
      (R := R) (M := ResidueField R) d).1 hle

/-- Helper for Lemma 10.110.3: unpack a bounded finite free resolution of the residue field into a
chosen augmented chain complex with termwise free and finite modules. -/
lemma exists_residueField_finiteFreeResolution_data
    {d : ℕ}
    (hres : HasFiniteFreeResolutionLengthLE R (ResidueField R) d) :
    ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R] (ResidueField R)),
      ChainComplex.IsFiniteFreeResolution π ∧
        ChainComplex.IsTermwiseFree F ∧
        ChainComplex.IsTermwiseFinite F ∧
        ∀ n : ℕ, d < n → Limits.IsZero (F.X n) := by
  rcases hres with ⟨F, π, hπ, hbound⟩
  refine ⟨F, π, hπ, ?_, ?_, hbound⟩
  · -- Forget the finiteness decoration and read termwise freeness from the resolution owner.
    intro n
    exact ChainComplex.IsFreeResolution.free (R := R) (M := ResidueField R) π n
  · -- The finite-free-resolution owner also records finiteness of every term.
    intro n
    exact ChainComplex.IsFiniteFreeResolution.finite π n

/-- Helper for Lemma 10.110.3: a bounded finite free resolution of the residue field already
vanishes in the first degree strictly above its length bound. -/
lemma residueField_finiteFreeResolution_succ_isZero
    {d : ℕ}
    (hres : HasFiniteFreeResolutionLengthLE R (ResidueField R) d) :
    ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R] (ResidueField R)),
      ChainComplex.IsFiniteFreeResolution π ∧
        ChainComplex.IsTermwiseFree F ∧
        ChainComplex.IsTermwiseFinite F ∧
        Limits.IsZero (F.X (d + 1)) := by
  obtain ⟨F, π, hπ, hFfree, hFfinite, hbound⟩ :=
    exists_residueField_finiteFreeResolution_data (R := R) hres
  refine ⟨F, π, hπ, hFfree, hFfinite, ?_⟩
  -- Apply the stored bound in the first degree above the allowed resolution length.
  exact hbound (d + 1) (Nat.lt_succ_self d)

/-- Helper for Lemma 10.110.3: once the cotangent space has dimension `d + 1`, we can choose a
`Fin (d + 1)`-indexed basis and lift it to generators of the maximal ideal. -/
lemma cotangent_basis_lift_generates_maximalIdeal
    {d : ℕ}
    (hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) = d + 1) :
    ∃ b : Module.Basis (Fin (d + 1)) (ResidueField R) (CotangentSpace R),
      ∃ x : Fin (d + 1) → maximalIdeal R,
        (∀ i, (maximalIdeal R).toCotangent (x i) = b i) ∧
          Submodule.span R (Set.range x) = ⊤ := by
  let _ : Module.Finite (ResidueField R) (CotangentSpace R) :=
    Module.finite_of_finrank_eq_succ hfinrank
  let b : Module.Basis (Fin (d + 1)) (ResidueField R) (CotangentSpace R) :=
    Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R) hfinrank
  choose x hx using fun i : Fin (d + 1) ↦ (maximalIdeal R).toCotangent_surjective (b i)
  have himage :
      (maximalIdeal R).toCotangent '' Set.range x =
        Set.range fun i : Fin (d + 1) ↦ (maximalIdeal R).toCotangent (x i) := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  have hspan_image :
      Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' Set.range x) = ⊤ := by
    -- The chosen lifts hit each basis vector, so their images already span the cotangent space.
    rw [himage]
    simpa [hx] using b.span_eq
  have hspan :
      Submodule.span R (Set.range x) = ⊤ := by
    -- In a Noetherian local ring, generating the cotangent space is equivalent to generating `𝔪`.
    exact
      (CotangentSpace.span_image_eq_top_iff (R := R) (s := Set.range x)).1 hspan_image
  exact ⟨b, x, hx, hspan⟩

/-- Helper for Lemma 10.110.3: the top exterior power of a `(d + 1)`-dimensional cotangent space
is nontrivial. -/
lemma top_exterior_cotangentSpace_nontrivial
    {d : ℕ}
    (hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) = d + 1) :
    Nontrivial (⋀[ResidueField R]^(d + 1) (CotangentSpace R)) := by
  let _ : Module.Finite (ResidueField R) (CotangentSpace R) :=
    Module.finite_of_finrank_eq_succ hfinrank
  let _ : Module.Free (ResidueField R) (CotangentSpace R) := inferInstance
  let _ : Module.Free (ResidueField R) (⋀[ResidueField R]^(d + 1) (CotangentSpace R)) :=
    inferInstance
  let _ : Module.Finite (ResidueField R) (⋀[ResidueField R]^(d + 1) (CotangentSpace R)) :=
    inferInstance
  have htop :
      Module.finrank (ResidueField R) (⋀[ResidueField R]^(d + 1) (CotangentSpace R)) = 1 := by
    -- The top exterior power has basis indexed by the singleton subsets of the chosen basis.
    rw [exteriorPower.finrank_eq]
    simp [hfinrank]
  exact Module.nontrivial_of_finrank_eq_succ (R := ResidueField R) htop

/-- Helper for Lemma 10.110.3: a finite free module admits standard coordinates `R^n` for some
natural number `n`. -/
lemma exists_fin_standard_coordinates
    (M : ModuleCat R) [Module.Free R M] [Module.Finite R M] :
    ∃ n : ℕ, Nonempty (M ≅ ModuleCat.of R (Fin n → R)) := by
  classical
  let b₀ : Module.Basis (Module.Free.ChooseBasisIndex R M) R M := Module.Free.chooseBasis R M
  let ι := Module.Free.ChooseBasisIndex R M
  letI : Finite ι := Module.Finite.finite_basis b₀
  letI : Fintype ι := Fintype.ofFinite ι
  let b : Module.Basis (Fin (Fintype.card ι)) R M := b₀.reindex (Fintype.equivFin ι)
  -- Reindex the chosen basis by `Fin` so the module matches the coordinate owner
  -- used in `FiniteFreeComplex`.
  exact ⟨Fintype.card ι, ⟨b.equivFun.toModuleIso⟩⟩

/-- Helper for Lemma 10.110.3: in degree `i`, a bounded termwise finite free complex has a chosen
coordinate rank compatible with `FiniteFreeComplex`. -/
noncomputable def bounded_resolution_rank
    {e : ℕ} (F : ChainComplex (ModuleCat R) ℕ)
    (hFfree : ChainComplex.IsTermwiseFree F)
    (hFfinite : ChainComplex.IsTermwiseFinite F)
    (i : Fin (e + 1)) : ℕ :=
  letI := hFfree i
  letI := hFfinite i
  Classical.choose (exists_fin_standard_coordinates (R := R) (M := F.X i))

/-- Helper for Lemma 10.110.3: in degree `i`, a bounded termwise finite free complex has chosen
`Fin`-coordinates for its term. -/
noncomputable def bounded_resolution_termIso
    {e : ℕ} (F : ChainComplex (ModuleCat R) ℕ)
    (hFfree : ChainComplex.IsTermwiseFree F)
    (hFfinite : ChainComplex.IsTermwiseFinite F)
    (i : Fin (e + 1)) :
    F.X i ≅ ModuleCat.of R (Fin (bounded_resolution_rank (R := R) F hFfree hFfinite i) → R) :=
  letI := hFfree i
  letI := hFfinite i
  Classical.choice
    (Classical.choose_spec (exists_fin_standard_coordinates (R := R) (M := F.X i)))

/-- Helper for Lemma 10.110.3: a bounded termwise finite free complex can be repackaged as a
`FiniteFreeComplex` without changing its underlying chain complex. -/
noncomputable def finiteFreeComplex_of_bounded_resolution
    {e : ℕ} (F : ChainComplex (ModuleCat R) ℕ)
    (hFfree : ChainComplex.IsTermwiseFree F)
    (hFfinite : ChainComplex.IsTermwiseFinite F)
    (hbound : ∀ n : ℕ, e < n → Limits.IsZero (F.X n)) :
    FiniteFreeComplex R e :=
  { toChainComplex := F
    isZero_toChainComplex_X := hbound
    rank := bounded_resolution_rank (R := R) F hFfree hFfinite
    termIso := bounded_resolution_termIso (R := R) F hFfree hFfinite }

/-- Helper for Lemma 10.110.3: the packaged bounded resolution has the original chain complex as
its underlying owner. -/
@[simp] lemma finiteFreeComplex_of_bounded_resolution_toChainComplex
    {e : ℕ} (F : ChainComplex (ModuleCat R) ℕ)
    (hFfree : ChainComplex.IsTermwiseFree F)
    (hFfinite : ChainComplex.IsTermwiseFinite F)
    (hbound : ∀ n : ℕ, e < n → Limits.IsZero (F.X n)) :
    (finiteFreeComplex_of_bounded_resolution (R := R) F hFfree hFfinite hbound).toChainComplex = F :=
  rfl

/-- Helper for Lemma 10.110.3: the induction measure for minimalizing a bounded finite free
resolution is the total displayed rank in positive degrees. -/
private def positiveRankSum {e : ℕ} (C : FiniteFreeComplex R e) : ℕ :=
  ∑ j : Fin e, C.rank j.succ

/-- Helper for Lemma 10.110.3: exactness at a positive degree of a chain complex of modules is the
exactness of the adjacent differentials as linear maps. -/
private lemma exactAt_iff_function_exact
    (K : ChainComplex (ModuleCat R) ℕ) {j : ℕ} (hj : 1 ≤ j) :
    K.ExactAt j ↔ Function.Exact (K.d (j + 1) j).hom (K.d j (j - 1)).hom := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hmid : 1 + k = k + 1 := by
    omega
  have hsucc : k + 1 + 1 = k + 2 := by
    omega
  have hpred : k + 1 - 1 = k := by
    omega
  -- Rewrite `ExactAt` through the explicit three-term window around `k + 1`.
  rw [hmid, hsucc, hpred]
  rw [HomologicalComplex.exactAt_iff' K (k + 2) (k + 1) k (by simp) (by simp)]
  -- In `ModuleCat`, categorical exactness is exactly exactness of linear maps.
  simpa [HomologicalComplex.sc'] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (K.sc' (k + 2) (k + 1) k))

/-- Helper for Lemma 10.110.3: if the total positive-degree rank is zero, then every individual
positive-degree displayed rank vanishes. -/
private lemma rank_succ_eq_zero_of_positiveRankSum_eq_zero
    {e : ℕ} (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0)
    (j : Fin e) :
    C.rank j.succ = 0 := by
  -- Each positive-degree rank is a nonnegative summand in the total rank sum.
  have hle : C.rank j.succ ≤ positiveRankSum (R := R) C := by
    simpa [positiveRankSum] using
      (Finset.single_le_sum
        (f := fun k : Fin e ↦ C.rank k.succ)
        (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ j))
  rw [hzero] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- Helper for Lemma 10.110.3: a displayed rank-zero term of a finite free complex is a zero
object. -/
private lemma term_isZero_of_rank_eq_zero
    {e : ℕ} (C : FiniteFreeComplex R e) (j : Fin (e + 1)) (hj : C.rank j = 0) :
    Limits.IsZero (C.toChainComplex.X j) := by
  -- Transport the zero-object claim across the chosen `Fin`-coordinate isomorphism in degree `j`.
  exact (C.termIso j).isZero_iff.mpr <|
    by simpa [hj] using ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Fin 0 → R))

/-- Helper for Lemma 10.110.3: if all positive displayed ranks vanish, then the packaged bounded
resolution is concentrated in degree `0`. -/
private lemma positive_degree_sum_zero_iso_single_zero
    {e : ℕ} (C : FiniteFreeComplex R e)
    (hzero : positiveRankSum (R := R) C = 0) :
    Nonempty
      (C.toChainComplex ≅
        ((ChainComplex.single₀ (ModuleCat R)).obj
          (ModuleCat.of R (Fin (C.rank ⟨0, Nat.zero_lt_succ e⟩) → R)))) := by
  let X0 : ModuleCat R := ModuleCat.of R (Fin (C.rank ⟨0, Nat.zero_lt_succ e⟩) → R)
  have hposZero : ∀ j : ℕ, 0 < j → Limits.IsZero (C.toChainComplex.X j) := by
    intro j hj
    by_cases hle : j ≤ e
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      let jPred : Fin e := ⟨n, by omega⟩
      have hrank : C.rank jPred.succ = 0 :=
        rank_succ_eq_zero_of_positiveRankSum_eq_zero (C := C) hzero jPred
      -- Every positive displayed rank vanishes, so the corresponding term is zero.
      simpa [jPred] using term_isZero_of_rank_eq_zero (C := C) (j := jPred.succ) hrank
    · exact C.isZero_toChainComplex_X j (Nat.lt_of_not_ge hle)
  let toSingle : C.toChainComplex ⟶ (ChainComplex.single₀ (ModuleCat R)).obj X0 :=
    (ChainComplex.toSingle₀Equiv C.toChainComplex X0).symm
      ⟨(C.termIso ⟨0, Nat.zero_lt_succ e⟩).hom, by
        -- The source of `d 1 0` is already zero, so the augmentation compatibility is automatic.
        exact (hposZero 1 (by omega)).eq_of_src _ _⟩
  let fromSingle : (ChainComplex.single₀ (ModuleCat R)).obj X0 ⟶ C.toChainComplex :=
    (ChainComplex.fromSingle₀Equiv C.toChainComplex X0).symm
      ((C.termIso ⟨0, Nat.zero_lt_succ e⟩).inv)
  refine ⟨{ hom := toSingle, inv := fromSingle, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · apply HomologicalComplex.hom_ext
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · -- In degree `0`, the two equivalence constructors recover the chosen coordinate isomorphism.
      ext x
      simpa [toSingle, fromSingle, X0] using
        ((C.termIso ⟨0, Nat.zero_lt_succ e⟩).toLinearEquiv.symm_apply_apply x)
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      -- In positive degrees, both endomorphisms of the zero object coincide automatically.
      exact (hposZero (n + 1) (Nat.succ_pos _)).eq_of_src _ _
  · apply HomologicalComplex.hom_ext
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · -- In degree `0`, the backward and forward maps cancel on the chosen basis identification.
      ext x
      simpa [toSingle, fromSingle, X0] using
        ((C.termIso ⟨0, Nat.zero_lt_succ e⟩).toLinearEquiv.apply_symm_apply x)
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      have hsingle :
          Limits.IsZero (((ChainComplex.single₀ (ModuleCat R)).obj X0).X (n + 1)) := by
        exact HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 X0 (n + 1) (by simp)
      -- Positive degrees of `single₀` are zero, so the component equality is unique.
      exact hsingle.eq_of_src _ _

/-- Helper for Lemma 10.110.3: exactness together with a zero next term makes the owner
differential injective. -/
private lemma owner_diff_injective_of_exactAt_and_next_isZero
    {e : ℕ} (C : FiniteFreeComplex R e) (i : Fin e)
    (hexact : C.toChainComplex.ExactAt (i.1 + 1))
    (hnext : Limits.IsZero (C.toChainComplex.X (i.1 + 2))) :
    Function.Injective ((C.toChainComplex.d (i.1 + 1) i.1).hom) := by
  have hfun :
      Function.Exact ((C.toChainComplex.d (i.1 + 2) (i.1 + 1)).hom)
        ((C.toChainComplex.d (i.1 + 1) i.1).hom) :=
    (exactAt_iff_function_exact (K := C.toChainComplex) (j := i.1 + 1) (by omega)).1 hexact
  have hzero_morph : C.toChainComplex.d (i.1 + 2) (i.1 + 1) = 0 := by
    -- The incoming differential has zero source, so it is the zero map.
    exact hnext.eq_of_src _ _
  have hzero : (C.toChainComplex.d (i.1 + 2) (i.1 + 1)).hom = 0 := by
    simpa using congrArg ModuleCat.Hom.hom hzero_morph
  -- Rewriting the preceding differential to zero reduces exactness to injectivity.
  rw [hzero, LinearMap.exact_zero_iff_injective (P := C.toChainComplex.X (i.1 + 2))] at hfun
  exact hfun

/-- Helper for Lemma 10.110.3: evaluating the target coordinate isomorphism inverse on
`diffAt i v` rewrites it back to the owner differential in chain-complex coordinates. -/
private lemma diffAt_termIso_inv_apply
    {e : ℕ} (C : FiniteFreeComplex R e) (i : Fin e) (v : C.term i.succ) :
    (C.termIso i.castSucc).inv.hom (C.diffAt i v) =
      (C.toChainComplex.d (i.1 + 1) i.1).hom ((C.termIso i.succ).inv.hom v) := by
  have hcomp :
      ModuleCat.ofHom (C.diffAt i) ≫ (C.termIso i.castSucc).inv =
        (C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 := by
    -- Record the conjugation identity once, rather than forcing `simp` to rediscover it.
    change
      (C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 ≫
          (C.termIso i.castSucc).hom ≫ (C.termIso i.castSucc).inv =
        (C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1
    simp [Category.assoc]
  -- Evaluating the recorded morphism equality on `v` yields the pointwise transport formula.
  change ((ModuleCat.ofHom (C.diffAt i) ≫ (C.termIso i.castSucc).inv).hom v) =
    (((C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1).hom v)
  rw [hcomp]
  rfl

/-- Helper for Lemma 10.110.3: if the next term of a finite free complex is zero, exactness
forces the displayed differential to be injective. -/
private lemma diffAt_injective_of_exactAt_and_next_isZero
    {e : ℕ} (C : FiniteFreeComplex R e) (i : Fin e)
    (hexact : C.toChainComplex.ExactAt (i.1 + 1))
    (hnext : Limits.IsZero (C.toChainComplex.X (i.1 + 2))) :
    Function.Injective (C.diffAt i) := by
  have howner :
      Function.Injective ((C.toChainComplex.d (i.1 + 1) i.1).hom) :=
    owner_diff_injective_of_exactAt_and_next_isZero (C := C) (i := i) hexact hnext
  intro x y hxy
  -- Transport the displayed differential equality to owner coordinates and use owner injectivity.
  have hterm :
      (C.toChainComplex.d (i.1 + 1) i.1).hom ((C.termIso i.succ).inv.hom x) =
        (C.toChainComplex.d (i.1 + 1) i.1).hom ((C.termIso i.succ).inv.hom y) := by
    have hx₁ :
        (C.toChainComplex.d (i.1 + 1) i.1).hom ((C.termIso i.succ).inv.hom x) =
          (C.termIso i.castSucc).inv.hom (C.diffAt i x) := by
      simpa using (diffAt_termIso_inv_apply (C := C) (i := i) (v := x)).symm
    have hx₂ :
        (C.termIso i.castSucc).inv.hom (C.diffAt i x) =
          (C.termIso i.castSucc).inv.hom (C.diffAt i y) := by
      simpa using congrArg (fun z ↦ (C.termIso i.castSucc).inv.hom z) hxy
    have hx₃ :
        (C.termIso i.castSucc).inv.hom (C.diffAt i y) =
          (C.toChainComplex.d (i.1 + 1) i.1).hom ((C.termIso i.succ).inv.hom y) := by
      simpa using diffAt_termIso_inv_apply (C := C) (i := i) (v := y)
    exact hx₁.trans (hx₂.trans hx₃)
  have hxy' :
      (C.termIso i.succ).inv.hom x = (C.termIso i.succ).inv.hom y := howner hterm
  have hy₁ :
      (C.termIso i.succ).hom.hom ((C.termIso i.succ).inv.hom x) = x := by
    simpa using (C.termIso i.succ).toLinearEquiv.apply_symm_apply x
  have hy₂ :
      (C.termIso i.succ).hom.hom ((C.termIso i.succ).inv.hom x) =
        (C.termIso i.succ).hom.hom ((C.termIso i.succ).inv.hom y) := by
    simpa using congrArg (fun z ↦ (C.termIso i.succ).hom.hom z) hxy'
  have hy₃ :
      (C.termIso i.succ).hom.hom ((C.termIso i.succ).inv.hom y) = y := by
    simpa using (C.termIso i.succ).toLinearEquiv.apply_symm_apply y
  exact hy₁.symm.trans (hy₂.trans hy₃)

/-- Helper for Lemma 10.110.3: exactness of a biproduct row in positive degree descends to the
first summand. -/
lemma exactAt_fst_of_biprod_exactAt_local
    {K L : ChainComplex (ModuleCat R) ℕ} {j : ℕ}
    (hj : 1 ≤ j)
    (h : (biprod K L).ExactAt j) :
    K.ExactAt j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hmid : 1 + k = k + 1 := by
    omega
  rw [hmid] at h ⊢
  rw [HomologicalComplex.exactAt_iff_exact_up_to_refinements
      (biprod K L) (k + 2) (k + 1) k (by simp) (by simp)] at h
  rw [HomologicalComplex.exactAt_iff_exact_up_to_refinements
      K (k + 2) (k + 1) k (by simp) (by simp)]
  intro A x₂ hx₂
  -- Insert the cycle into the left summand and use exactness of the split row there.
  have hx₂' :
      x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1) ≫ (biprod K L).d (k + 1) k = 0 := by
    have hcomm := (biprod.inl : K ⟶ biprod K L).comm (k + 1) k
    calc
      x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1) ≫ (biprod K L).d (k + 1) k =
          x₂ ≫ (K.d (k + 1) k ≫ (biprod.inl : K ⟶ biprod K L).f k) := by
            simpa [Category.assoc] using congrArg (fun m ↦ x₂ ≫ m) hcomm
      _ = (x₂ ≫ K.d (k + 1) k) ≫ (biprod.inl : K ⟶ biprod K L).f k := by
            simp [Category.assoc]
      _ = 0 := by
            simp [hx₂]
  obtain ⟨A', π, hπ, y₁, hy₁⟩ := h (x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1)) hx₂'
  refine ⟨A', π, hπ, y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2), ?_⟩
  -- Project the resulting boundary back to the first summand.
  calc
    π ≫ x₂ = π ≫ x₂ ≫ (biprod.inl : K ⟶ biprod K L).f (k + 1) ≫
        (biprod.fst : biprod K L ⟶ K).f (k + 1) := by
          simp [Category.assoc]
    _ = y₁ ≫ (biprod K L).d (k + 2) (k + 1) ≫
        (biprod.fst : biprod K L ⟶ K).f (k + 1) := by
          simpa [Category.assoc] using congrArg
            (fun m ↦ m ≫ (biprod.fst : biprod K L ⟶ K).f (k + 1)) hy₁
    _ = y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2) ≫ K.d (k + 2) (k + 1) := by
          have hcomm := (biprod.fst : biprod K L ⟶ K).comm (k + 2) (k + 1)
          simpa [Category.assoc] using congrArg (fun m ↦ y₁ ≫ m) hcomm.symm
    _ = (y₁ ≫ (biprod.fst : biprod K L ⟶ K).f (k + 2)) ≫ K.d (k + 2) (k + 1) := by
          simp [Category.assoc]

/-- Helper for Lemma 10.110.3: exactness of a split degree-`0` row with differential
`f ⊞ 𝟙` descends to exactness on the first summand. -/
lemma exact_zero_fst_of_biprod_identity_exact
    {A₁ A₀ K P : ModuleCat R}
    {f : A₁ ⟶ A₀} {g : A₀ ⟶ K}
    (hfg : f ≫ g = 0)
    (hexact :
      (ShortComplex.mk (biprod.map f (𝟙 P)) (biprod.desc g (0 : P ⟶ K)) (by
        refine biprod.hom_ext' (biprod.map f (𝟙 P) ≫ biprod.desc g (0 : P ⟶ K)) 0 ?_ ?_
        · simp [Category.assoc, hfg]
        · simp [Category.assoc])).Exact) :
    (ShortComplex.mk f g hfg).Exact := by
  have hdesc : biprod.desc g (0 : P ⟶ K) = biprod.fst ≫ g := by
    refine biprod.hom_ext' (biprod.desc g (0 : P ⟶ K)) (biprod.fst ≫ g) ?_ ?_
    · simp [Category.assoc]
    · simp [Category.assoc]
  have hmap_fst : biprod.map f (𝟙 P) ≫ biprod.fst = biprod.fst ≫ f := by
    refine biprod.hom_ext' (biprod.map f (𝟙 P) ≫ biprod.fst) (biprod.fst ≫ f) ?_ ?_
    · simp [Category.assoc]
    · simp [Category.assoc]
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hexact ⊢
  intro x
  constructor
  · intro hx
    let x' := (biprod.inl : A₀ ⟶ A₀ ⊞ P).hom x
    have hinl_fst : (biprod.inl : A₀ ⟶ A₀ ⊞ P) ≫ biprod.fst = 𝟙 A₀ := by
      simp
    have hx_inl : (biprod.fst : A₀ ⊞ P ⟶ A₀).hom x' = x := by
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hinl_fst) x
    have hx' : (biprod.desc g (0 : P ⟶ K)).hom x' = 0 := by
      -- The inserted element lives in the first summand, so the split augmentation reduces to `g`.
      calc
        (biprod.desc g (0 : P ⟶ K)).hom x' =
            g.hom ((biprod.fst : A₀ ⊞ P ⟶ A₀).hom x') := by
              exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hdesc) x'
        _ = g.hom x := by rw [hx_inl]
        _ = 0 := hx
    obtain ⟨y, hy⟩ := (hexact x').1 hx'
    refine ⟨(biprod.fst : A₁ ⊞ P ⟶ A₁).hom y, ?_⟩
    have hmap_fst_apply :
        (biprod.fst : A₀ ⊞ P ⟶ A₀).hom ((biprod.map f (𝟙 P)).hom y) =
          f.hom ((biprod.fst : A₁ ⊞ P ⟶ A₁).hom y) := by
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hmap_fst) y
    -- Project the preimage equation back to the first summand.
    have hy' := congrArg (fun z ↦ (biprod.fst : A₀ ⊞ P ⟶ A₀).hom z) hy
    calc
      f.hom ((biprod.fst : A₁ ⊞ P ⟶ A₁).hom y) =
          (biprod.fst : A₀ ⊞ P ⟶ A₀).hom ((biprod.map f (𝟙 P)).hom y) := by
            simpa using hmap_fst_apply.symm
      _ = (biprod.fst : A₀ ⊞ P ⟶ A₀).hom x' := hy'
      _ = x := hx_inl
  · rintro ⟨y, rfl⟩
    -- Membership in the image of `f` immediately gives a cycle for `g`.
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hfg) y

/-- Helper for Lemma 10.110.3: exactness of a split degree-`0` row on a biproduct target
descends to exactness on the first summand. -/
lemma exact_zero_fst_of_biprod_map_exact
    {A₁ A₀ K P₁ P₀ : ModuleCat R}
    {f : A₁ ⟶ A₀} {u : P₁ ⟶ P₀} {g : A₀ ⟶ K}
    (hfg : f ≫ g = 0)
    (hexact :
      (ShortComplex.mk (biprod.map f u) (biprod.desc g (0 : P₀ ⟶ K)) (by
        refine biprod.hom_ext' (biprod.map f u ≫ biprod.desc g (0 : P₀ ⟶ K)) 0 ?_ ?_
        · simp [Category.assoc, hfg]
        · simp [Category.assoc])).Exact) :
    (ShortComplex.mk f g hfg).Exact := by
  have hdesc : biprod.desc g (0 : P₀ ⟶ K) = biprod.fst ≫ g := by
    refine biprod.hom_ext' (biprod.desc g (0 : P₀ ⟶ K)) (biprod.fst ≫ g) ?_ ?_
    · simp [Category.assoc]
    · simp [Category.assoc]
  have hmap_fst : biprod.map f u ≫ biprod.fst = biprod.fst ≫ f := by
    refine biprod.hom_ext' (biprod.map f u ≫ biprod.fst) (biprod.fst ≫ f) ?_ ?_
    · simp [Category.assoc]
    · simp [Category.assoc]
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hexact ⊢
  intro x
  constructor
  · intro hx
    let x' := (biprod.inl : A₀ ⟶ A₀ ⊞ P₀).hom x
    have hinl_fst : (biprod.inl : A₀ ⟶ A₀ ⊞ P₀) ≫ biprod.fst = 𝟙 A₀ := by
      simp
    have hx_inl : (biprod.fst : A₀ ⊞ P₀ ⟶ A₀).hom x' = x := by
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hinl_fst) x
    have hx' : (biprod.desc g (0 : P₀ ⟶ K)).hom x' = 0 := by
      -- The inserted cycle lies in the first biproduct summand, so the split augmentation
      -- evaluates to `g` there.
      calc
        (biprod.desc g (0 : P₀ ⟶ K)).hom x' =
            g.hom ((biprod.fst : A₀ ⊞ P₀ ⟶ A₀).hom x') := by
              exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hdesc) x'
        _ = g.hom x := by rw [hx_inl]
        _ = 0 := hx
    obtain ⟨y, hy⟩ := (hexact x').1 hx'
    refine ⟨(biprod.fst : A₁ ⊞ P₁ ⟶ A₁).hom y, ?_⟩
    have hmap_fst_apply :
        (biprod.fst : A₀ ⊞ P₀ ⟶ A₀).hom ((biprod.map f u).hom y) =
          f.hom ((biprod.fst : A₁ ⊞ P₁ ⟶ A₁).hom y) := by
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hmap_fst) y
    have hy' := congrArg (fun z ↦ (biprod.fst : A₀ ⊞ P₀ ⟶ A₀).hom z) hy
    -- Project the chosen preimage back to the first summand to recover a preimage for `x`.
    calc
      f.hom ((biprod.fst : A₁ ⊞ P₁ ⟶ A₁).hom y) =
          (biprod.fst : A₀ ⊞ P₀ ⟶ A₀).hom ((biprod.map f u).hom y) := by
            simpa using hmap_fst_apply.symm
      _ = (biprod.fst : A₀ ⊞ P₀ ⟶ A₀).hom x' := hy'
      _ = x := hx_inl
  · rintro ⟨y, rfl⟩
    -- A genuine image element is automatically a cycle because `g ∘ f = 0`.
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hfg) y

/-- Helper for Lemma 10.110.3: if the split augmentation `[g, 0]` is surjective, then `g` is
already surjective on the first summand. -/
lemma surjective_fst_of_biprod_desc_zero
    {A K P : ModuleCat R}
    {g : A ⟶ K}
    (hsurj : Function.Surjective (biprod.desc g (0 : P ⟶ K)).hom) :
    Function.Surjective g.hom := by
  have hdesc : biprod.desc g (0 : P ⟶ K) = biprod.fst ≫ g := by
    refine biprod.hom_ext' (biprod.desc g (0 : P ⟶ K)) (biprod.fst ≫ g) ?_ ?_
    · simp [Category.assoc]
    · simp [Category.assoc]
  intro z
  obtain ⟨y, hy⟩ := hsurj z
  refine ⟨(biprod.fst : A ⊞ P ⟶ A).hom y, ?_⟩
  -- The second summand contributes nothing to `[g, 0]`, so projecting the chosen preimage works.
  calc
    g.hom ((biprod.fst : A ⊞ P ⟶ A).hom y) = (biprod.desc g (0 : P ⟶ K)).hom y := by
      exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hdesc) y).symm
    _ = z := hy

/-- Helper for Lemma 10.110.3: if the second biproduct summand is zero, any map out of the
biproduct is determined by its first component. -/
lemma biprod_desc_eq_desc_zero_of_isZero
    {A P K : ModuleCat R}
    (hP : Limits.IsZero P)
    (g : A ⊞ P ⟶ K) :
    g = biprod.desc ((biprod.inl : A ⟶ A ⊞ P) ≫ g) (0 : P ⟶ K) := by
  -- Compare the two morphisms on the two coproduct injections.
  refine biprod.hom_ext' g _ ?_ ?_
  · simp [Category.assoc]
  · exact hP.eq_of_src _ _

/-- Helper for Lemma 10.110.3: if the identity-disk summand is supported strictly above degree
`0`, then its degree-`0` term is zero. -/
lemma identityDiskComplex_X_zero_isZero_of_pos
    {e : ℕ} (i : Fin e)
    (hi : 0 < i.1) :
    Limits.IsZero ((FiniteFreeComplex.identityDiskComplex (R := R) i).X 0) := by
  have hX :
      ((FiniteFreeComplex.identityDiskComplex (R := R) i).X 0) =
        ModuleCat.of R (Fin (if 0 = i.1 + 1 ∨ 0 = i.1 then 1 else 0) → R) := by
    rfl
  rw [hX]
  -- Once degree `0` is off the support, the term is the empty free module.
  have hsucc_ne : ¬ 0 = i.1 + 1 := by
    omega
  have hzero_ne : ¬ 0 = i.1 := by
    omega
  have hzero_term :
      Limits.IsZero (ModuleCat.of R (Fin (if 0 = i.1 then 1 else 0) → R)) := by
    simpa [hzero_ne] using
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Fin 0 → R)))
  simpa [hsucc_ne] using hzero_term

/-- Helper for Lemma 10.110.3: every positive-degree component of a map to `single₀` is zero. -/
lemma moduleSingle_component_eq_zero_succ
    {F : ChainComplex (ModuleCat R) ℕ}
    (φ : F ⟶ moduleSingle[R](ResidueField R))
    (n : ℕ) :
    φ.f (n + 1) = 0 := by
  -- The target complex `single₀` vanishes away from degree `0`, so any higher component is unique.
  apply IsZero.eq_of_tgt
  apply HomologicalComplex.isZero_single_obj_X
  simp

/-- Helper for Lemma 10.110.3: the projected augmentation after splitting off an
`identityDiskComplex` summand is obtained by composing with the first biproduct inclusion. -/
noncomputable abbrev projected_augmentation
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    C'.toChainComplex ⟶ moduleSingle[R] (ResidueField R) :=
  (biprod.inl :
      C'.toChainComplex ⟶
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) ≫
    eIso.inv ≫ ρ

/-- Helper for Lemma 10.110.3: the augmentation on the split biproduct is the original
augmentation transported across the chosen chain-complex isomorphism. -/
noncomputable abbrev split_augmentation
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i) ⟶
      moduleSingle[R] (ResidueField R) :=
  eIso.inv ≫ ρ

/-- Helper for Lemma 10.110.3: transporting the original augmentation across the split
isomorphism preserves exactness in every positive degree. -/
lemma projected_augmentation_exactAt_succ_of_biprod_identityDisk
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i))
    (n : ℕ) :
    C'.toChainComplex.ExactAt (n + 1) := by
  letI : QuasiIso ρ := hρ.toIsFreeResolution.toQuasiIso
  have hExactC : C.toChainComplex.ExactAt (n + 1) := by
    -- The original augmentation is a quasi-isomorphism to `single₀`, hence exact in positive
    -- degrees.
    exact
      (quasiIsoAt_iff_exactAt' ρ (n + 1)
        (ChainComplex.exactAt_succ_single_obj (ModuleCat.of R (ResidueField R)) n)).1
        inferInstance
  have hExactSplit :
      (biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)).ExactAt
        (n + 1) := by
    -- Transport exactness across the chosen chain-complex isomorphism before projecting.
    exact hExactC.of_iso eIso
  -- Exactness of the biproduct row descends to the first summand.
  exact
    exactAt_fst_of_biprod_exactAt_local (R := R)
      (hj := Nat.succ_le_succ (Nat.zero_le n)) hExactSplit

/-- Helper for Lemma 10.110.3: after transporting the augmentation across a split-off
`identityDiskComplex`, the degree-`0` component becomes `[g, 0]` after rewriting the chain-
complex biproduct term through `HomologicalComplex.biprodXIso`. -/
lemma split_augmentation_f_zero_eq_biprodXIso_hom_desc_zero_of_biprod_identityDisk
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    (split_augmentation (R := R) C C' i ρ eIso).f 0 =
      (HomologicalComplex.biprodXIso C'.toChainComplex
        (FiniteFreeComplex.identityDiskComplex (R := R) i) 0).hom ≫
        biprod.desc ((projected_augmentation (R := R) C C' i ρ eIso).f 0)
          (0 :
            ((FiniteFreeComplex.identityDiskComplex (R := R) i).X 0) ⟶
              ModuleCat.of R (ResidueField R)) := sorry

/-- Helper for Lemma 10.110.3: the projected augmentation is exact in degree `0`. -/
lemma projected_augmentation_exact_zero_of_biprod_identityDisk
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    Function.Exact
      (C'.toChainComplex.d 1 0).hom
      ((projected_augmentation (R := R) C C' i ρ eIso).f 0).hom := by
  -- TODO: first use
  -- `split_augmentation_f_zero_eq_biprodXIso_hom_desc_zero_of_biprod_identityDisk`
  -- to rewrite the split degree-`0` augmentation through the chain-level biproduct term
  -- isomorphism, then descend exactness of the split short complex to the first summand.
  sorry

/-- Helper for Lemma 10.110.3: the projected augmentation remains surjective in degree `0`. -/
lemma projected_augmentation_epi_zero_of_biprod_identityDisk
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    Function.Surjective ((projected_augmentation (R := R) C C' i ρ eIso).f 0).hom := by
  -- TODO: use the same `biprodXIso`-transported degree-`0` rewrite as in the exactness lemma,
  -- then project surjectivity from the split augmentation to the first summand.
  sorry

/-- Helper for Lemma 10.110.3: removing an `identityDiskComplex` summand from a bounded finite
free resolution preserves the residue-field resolution property. -/
lemma split_identityDisk_preserves_residueField_resolution
    {e : ℕ} (C C' : FiniteFreeComplex R e) (i : Fin e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (eIso :
      C.toChainComplex ≅
        biprod C'.toChainComplex (FiniteFreeComplex.identityDiskComplex (R := R) i)) :
    ChainComplex.IsFiniteFreeResolution
      (projected_augmentation (R := R) C C' i ρ eIso) := by
  -- TODO: after proving the degree-`0` exactness and surjectivity lemmas through the
  -- `biprodXIso` transport bridge, rebuild the quasi-isomorphism exactly as in
  -- `hasFiniteFreeResolutionLengthLE_succ_of_finite_free_presentation`.
  sorry

/-- Helper for Lemma 10.110.3: a bounded finite free resolution of the residue field can be
minimalized so that every matrix entry of every differential lies in the maximal ideal. -/
lemma exists_minimal_residueField_finiteFreeComplex
    {e : ℕ} (C : FiniteFreeComplex R e)
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ) :
    ∃ (Cmin : FiniteFreeComplex R e)
      (ρmin : Cmin.toChainComplex ⟶ moduleSingle[R] (ResidueField R)),
      ChainComplex.IsFiniteFreeResolution ρmin ∧
        ∀ i : Fin e, ∀ a : Fin (Cmin.rank i.succ), ∀ b : Fin (Cmin.rank i.castSucc),
          FiniteFreeComplex.diffEntry Cmin i a b ∈ maximalIdeal R := by
  -- TODO: run strong induction on `positiveRankSum`. If some `diffEntry` is a unit, split off the
  -- corresponding `identityDiskComplex` using
  -- `FiniteFreeComplex.exists_iso_biprod_identityDisk_of_isUnit_diffEntry`, then preserve the
  -- residue-field augmentation with `split_identityDisk_preserves_residueField_resolution` and
  -- recurse on the reduced complex. If no unit entry exists, every differential entry already lies
  -- in the maximal ideal and the current complex is minimal.
  sorry

/-- Helper for Lemma 10.110.3: a minimal finite free resolution contradicts the nonvanishing of
the top reduced Koszul differential in degree `d + 2`. -/
lemma minimal_resolution_koszul_top_degree_contradiction
    {d : ℕ}
    (hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) = d + 2)
    (C : FiniteFreeComplex R (d + 1))
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (hminimal :
      ∀ i : Fin (d + 1), ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R) :
    False := by
  -- TODO: choose a basis of `CotangentSpace R`, form the source-faithful Koszul complex on lifted
  -- generators of `maximalIdeal R`, build the augmentation-compatible comparison to the minimal
  -- resolution, and prove by induction that the reduced comparison maps are injective in every
  -- degree. The nontrivial top exterior power then forces the degree `d + 2` term of the minimal
  -- resolution to be nonzero, contradicting boundedness.
  sorry

/-- Helper for Lemma 10.110.3: if the residue field is projective as an `R`-module, then the
maximal ideal of the local ring vanishes. -/
lemma maximalIdeal_eq_bot_of_projective_residueField
    (hproj : Module.Projective R (ResidueField R)) :
    maximalIdeal R = ⊥ := by
  let π : R →ₗ[R] ResidueField R := (Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap
  have hπ_surj : Function.Surjective π := by
    simpa [π] using (Ideal.Quotient.mk_surjective (I := maximalIdeal R))
  obtain ⟨σ, hσ⟩ :=
    (Module.Projective.iff_split_of_projective (R := R) (M := R)
      (P := ResidueField R) π hπ_surj).mp hproj
  let e : R := 1 - σ 1
  have hσ1 : Ideal.Quotient.mk (maximalIdeal R) (σ 1) = 1 := by
    -- The splitting sends the residue class of `1` back to a lift of `1`.
    simpa [π] using DFunLike.congr_fun hσ (1 : ResidueField R)
  have he_mem : e ∈ maximalIdeal R := by
    -- The defect `1 - σ(1)` lies in the kernel of the residue map, hence in `𝔪`.
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    calc
      Ideal.Quotient.mk (maximalIdeal R) e
          = 1 - Ideal.Quotient.mk (maximalIdeal R) (σ 1) := by
            simp [e]
      _ = 0 := by
            simp [hσ1]
  have hmul_right : ∀ {x : R}, x ∈ maximalIdeal R → x = x * e := by
    intro x hx
    have hxq : IsLocalRing.residue R x = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have hσx : σ (IsLocalRing.residue R x) = x * σ 1 := by
      calc
        σ (IsLocalRing.residue R x) = σ (x • (1 : ResidueField R)) := by
          simp [Algebra.smul_def]
        _ = x • σ 1 := by
          rw [map_smul]
        _ = x * σ 1 := by
          simp [smul_eq_mul]
    have hxσ0 : x * σ 1 = 0 := by
      simpa [hσx] using congrArg σ hxq
    calc
      x = x * 1 := by simp
      _ = x * (e + σ 1) := by
        simp [e, sub_eq_add_neg, add_comm, add_left_comm]
      _ = x * e + x * σ 1 := by
        ring
      _ = x * e := by
        simp [hxσ0]
  have he_idem : IsIdempotentElem e := by
    -- Applying the kernel relation to `e` itself shows that `e` is idempotent.
    simpa [IsIdempotentElem] using (hmul_right he_mem).symm
  have hunit : IsUnit (1 - e) := by
    -- In a local ring, an element of `𝔪` has unit complement.
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits e
      ((IsLocalRing.mem_maximalIdeal e).1 he_mem)
  have he_zero : e = 0 := by
    -- Multiply `(1 - e) * e = 0` by the inverse of the unit `1 - e`.
    rcases hunit with ⟨u, hu⟩
    have hmul_zero : ((↑u : R) * e) = 0 := by
      simpa [hu] using he_idem.one_sub_mul_self
    have := congrArg (fun y : R => ↑u⁻¹ * y) hmul_zero
    simpa [mul_assoc] using this
  apply eq_bot_iff.mpr
  intro x hx
  -- Once `e = 0`, the kernel relation `x = x * e` forces every `x ∈ 𝔪` to vanish.
  calc
    x = x * e := hmul_right hx
    _ = 0 := by simp [he_zero]

/-- Helper for Lemma 10.110.3: a projective residue field forces cotangent-space dimension `0`. -/
lemma finrank_cotangentSpace_eq_zero_of_projective_residueField
    (hproj : Module.Projective R (ResidueField R)) :
    Module.finrank (ResidueField R) (CotangentSpace R) = 0 := by
  have hfield : IsField R := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    exact maximalIdeal_eq_bot_of_projective_residueField (R := R) hproj
  let _ : Field R := hfield.toField
  -- Over a field the maximal ideal is zero, so the cotangent space is trivial.
  simpa using finrank_cotangentSpace_eq_zero (R := R)

/-- Helper for Lemma 10.110.3: once the cotangent-space dimension is `d + 1`, the remaining
source-faithful task is the Koszul-versus-minimal-resolution contradiction for a bounded finite
free resolution of length `d`. -/
lemma finiteFreeResolutionLengthLE_contradicts_cotangentSpace_dimension_succ
    {d : ℕ}
    (hres : HasFiniteFreeResolutionLengthLE R (ResidueField R) d)
    (hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) = d + 1) :
    False := by
  cases d with
  | zero =>
      -- In length `0`, the residue field would be finite free, hence projective. The quotient map
      -- `R → κ` would then split, forcing `𝔪 = 0` and therefore cotangent-space dimension `0`.
      have hfree : Module.Free R (ResidueField R) :=
        (hasFiniteFreeResolutionLengthLE_zero_iff (R := R) (M := ResidueField R)).1 hres |>.1
      let _ : Module.Free R (ResidueField R) := hfree
      have hproj : Module.Projective R (ResidueField R) := inferInstance
      have hzero :
          Module.finrank (ResidueField R) (CotangentSpace R) = 0 :=
        finrank_cotangentSpace_eq_zero_of_projective_residueField (R := R) hproj
      have hcontra : (0 : ℕ) = 1 := by
        simpa [hzero] using hfinrank
      norm_num at hcontra
  | succ d =>
      obtain ⟨b, x, hx, hspanx⟩ :=
        cotangent_basis_lift_generates_maximalIdeal (R := R) hfinrank
      have htop_nontrivial :
          Nontrivial (⋀[ResidueField R]^(d + 2) (CotangentSpace R)) :=
        top_exterior_cotangentSpace_nontrivial (R := R) hfinrank
      obtain ⟨F, π, hπ, hFfree, hFfinite, hbound⟩ :=
        exists_residueField_finiteFreeResolution_data (R := R) hres
      have htop_zero : Limits.IsZero (F.X (d + 2)) := by
        -- Keep the full bounded-resolution witness from the source proof; the top-degree
        -- vanishing needed for the contradiction is one immediate consequence of that bound.
        exact hbound (d + 2) (Nat.lt_succ_self (d + 1))
      let C : FiniteFreeComplex R (d + 1) :=
        finiteFreeComplex_of_bounded_resolution (R := R) F hFfree hFfinite hbound
      let ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R) := by
        -- The packaged complex keeps the same augmentation because its underlying chain complex
        -- is definitionally the chosen resolution `F`.
        simpa [C, finiteFreeComplex_of_bounded_resolution] using π
      have hρ : ChainComplex.IsFiniteFreeResolution ρ := by
        -- The resolution owner transfers unchanged across the packaging step.
        simpa [ρ, C, finiteFreeComplex_of_bounded_resolution] using hπ
      obtain ⟨Cmin, ρmin, hρmin, hminimal⟩ :=
        exists_minimal_residueField_finiteFreeComplex (R := R) C ρ hρ
      -- Route correction: the split-preservation layer is now separated from the remaining source-
      -- faithful blockers. What remains is exactly the minimalization induction and then the
      -- Koszul comparison for the resulting minimal resolution.
      exact
        minimal_resolution_koszul_top_degree_contradiction (R := R) hfinrank Cmin ρmin hρmin
          hminimal

/-- Helper for Lemma 10.110.3: the source proof's Koszul/minimal-resolution comparison should
show that the residue field cannot have projective dimension strictly smaller than the cotangent-
space dimension. -/
lemma residueField_not_hasProjectiveDimensionLT_finrank_cotangentSpace :
    ¬ HasProjectiveDimensionLT
        (ModuleCat.of R (ResidueField R))
        (Module.finrank (ResidueField R) (CotangentSpace R)) := by
  -- Split on the cotangent-space dimension. The zero case is purely owner-level, and the
  -- successor case reduces to the source-faithful finite-free-resolution contradiction.
  cases hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) with
  | zero =>
      intro hpd
      exact residueField_module_not_isZero
        ((CategoryTheory.hasProjectiveDimensionLT_zero_iff_isZero
          (X := ModuleCat.of R (ResidueField R))).1 hpd)
  | succ d =>
      intro hpd
      have hres :
          HasFiniteFreeResolutionLengthLE R (ResidueField R) d :=
        residueField_hasFiniteFreeResolutionLengthLE_of_hasProjectiveDimensionLT_succ
          hpd
      -- Route correction: keep the source proof in resolution language until the final Koszul
      -- comparison, rather than packaging the blocker as a raw `Ext` statement.
      exact finiteFreeResolutionLengthLE_contradicts_cotangentSpace_dimension_succ
        hres hfinrank

/-- Lemma 10.110.3: for a Noetherian local ring `R`, the projective dimension of the residue field
`ResidueField R` is at least the dimension of the cotangent space `CotangentSpace R = 𝔪 / 𝔪²`
over the residue field. -/
theorem finrank_cotangentSpace_le_projectiveDimension_residueField :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤
      projectiveDimension (ModuleCat.of R (ResidueField R)) := by
  -- Route correction: isolate the source proof's Koszul comparison as the negation of
  -- `HasProjectiveDimensionLT` in the critical degree, then convert that owner-level statement to
  -- the desired lower bound via `projectiveDimension_ge_iff`.
  rw [CategoryTheory.projectiveDimension_ge_iff]
  exact residueField_not_hasProjectiveDimensionLT_finrank_cotangentSpace (R := R)

end

/-! ### Lemma_10_110_4 (from Chap10) -/
open CategoryTheory IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-
Source/core/bridge triage:
* primary domain: projective dimension of the residue field versus Krull dimension for Noetherian
  local rings;
* sampled owner declarations:
  `CategoryTheory.projectiveDimension`,
  `CategoryTheory.projectiveDimension_eq_bot_iff`,
  `CategoryTheory.projectiveDimension_ne_top_iff`,
  `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`;
* core/canonical owners: `projectiveDimension (ModuleCat.of R (ResidueField R))` and
  `ringKrullDim R`;
* layer: the textbook statement below is `source-facing`, while the finite-projective-dimension
  inequality that follows is a `bridge/view` reformulation for downstream use.

Primitive data are only the ambient local Noetherian ring and the canonical invariant
`projectiveDimension` of the residue-field module. There is no additional local owner object to
package here, so the refinement should keep the source-facing comparison theorem and expose only a
thin bridge in the canonical `projectiveDimension ≠ ⊤` language.
-/

-- Proof sketch: choose a finite free resolution of `ResidueField R` of length `n`, replace it by a
-- minimal one over the local ring, apply the Buchsbaum--Eisenbud criterion to the top differential
-- to obtain a regular sequence of length `n`, and then bound that length by `ringKrullDim R` using
-- the depth-dimension inequality for Noetherian local rings.
/-- Lemma 10.110.4: if the residue field of a Noetherian local ring `R` has projective dimension
`n` over `R`, then the Krull dimension of `R` is at least `n`. -/
theorem projectiveDimension_residueField_le_ringKrullDim
    {n : ℕ} (hpd : projectiveDimension (ModuleCat.of R (ResidueField R)) = n) :
    n ≤ ringKrullDim R := sorry

-- Proof sketch: unpack `projectiveDimension ≠ ⊤` into the finite-value case for the residue field
-- and then apply the source-facing theorem above.
/-- Bridge/view: if the residue field of a Noetherian local ring has finite projective dimension,
then that projective dimension is bounded above by the Krull dimension of the ring. -/
theorem projectiveDimension_residueField_le_ringKrullDim_of_ne_top
    (hpd : projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤) :
    projectiveDimension (ModuleCat.of R (ResidueField R)) ≤ ringKrullDim R := sorry

end

/-! ### Proposition_10_110_5 (from Chap10) -/
open CategoryTheory
open IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- 
Domain-style sampling:
* primary domain: homological characterizations of regular local rings for Noetherian local rings;
* sampled owner declarations:
  `projectiveDimension`,
  `projectiveDimension_ne_top_iff`,
  `IsFiniteGlobalDimensionRing`,
  `IsRegularLocalRing.iff_finrank_cotangentSpace`;
* best owner abstraction: the canonical owners are the residue-field invariant
  `projectiveDimension (ModuleCat.of R (ResidueField R))`, the ring-level owner
  `IsFiniteGlobalDimensionRing R`, and the local-regularity owner `IsRegularLocalRing R`;
* primitive data vs. derived API:
  the three owner predicates/invariants above are primitive for this proposition;
  the TFAE statement and the equalities involving `globalDimension R`, `ringKrullDim R`, and the
  cotangent-space finrank are derived API;
* source/core/bridge triage:
  the TFAE theorem is `source-facing`,
  the owner abstractions above are `core/canonical`,
  and the two equality theorems are `bridge/view` consequences.

This file should therefore stay owner-facing and avoid introducing any extra local wrapper for
"finite projective dimension of the residue field" or for regular locality.
-/

-- Proof sketch: use Proposition `10.110.1` to prove that a regular local ring has finite global
-- dimension, the definition of finite global dimension to deduce finite projective dimension for
-- the residue field, and Lemmas `10.110.3` and `10.110.4` together with the characterization of
-- regular local rings from Definition `10.60.10` to recover regularity from finite projective
-- dimension of the residue field.
/-- Proposition 10.110.5: for a Noetherian local ring `R`, the following are equivalent: the
residue field `ResidueField R` has finite projective dimension as an `R`-module, `R` has finite
global dimension, and `R` is a regular local ring. -/
theorem residueField_finiteProjectiveDimension_finiteGlobalDimension_regularLocal_tfae :
    List.TFAE
      [ projectiveDimension (ModuleCat.of R (ResidueField R)) ≠ ⊤,
        IsFiniteGlobalDimensionRing R,
        IsRegularLocalRing R ] := sorry

variable [IsFiniteGlobalDimensionRing R]

-- Proof sketch: finite global dimension gives `globalDimension R` as a projective-dimension bound
-- for every module. Apply the main TFAE theorem to obtain regularity, use Proposition `10.110.1`
-- to bound the global dimension above by `ringKrullDim R`, and use the residue-field lower bound
-- from Lemma `10.110.3` together with the dimension bound from Lemma `10.110.4` to get the
-- reverse inequality.
/-- Under finite global dimension, the global dimension of a Noetherian local ring equals its Krull
dimension. -/
theorem globalDimension_eq_ringKrullDim_of_finiteGlobalDimension :
    globalDimension R = ringKrullDim R := sorry

-- Proof sketch: by the previous theorem, `globalDimension R = ringKrullDim R`. The finite-global-
-- dimension hypothesis implies finite projective dimension for the residue field, so Lemmas
-- `10.110.3` and `10.110.4` force `ringKrullDim R` and the cotangent-space dimension to coincide.
/-- Under finite global dimension, the Krull dimension of a Noetherian local ring equals the
dimension of its cotangent space `maximalIdeal R / (maximalIdeal R)^2` over the residue field. -/
theorem ringKrullDim_eq_finrank_cotangentSpace_of_finiteGlobalDimension :
    ringKrullDim R = Module.finrank (ResidueField R) (CotangentSpace R) := sorry

end

/-! ### Lemma_10_110_6 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- 
Domain-style sampling:
* primary domain: Noetherian local commutative algebra, relating the owner predicates
  `IsRegularLocalRing` and `IsFiniteGlobalDimensionRing`;
* sampled owner declarations:
  `IsRegularLocalRing`,
  `IsFiniteGlobalDimensionRing`,
  `residueField_finiteProjectiveDimension_finiteGlobalDimension_regularLocal_tfae`,
  `IsRegularRing.isRegularLocalRing_atPrime`;
* best owner abstraction: the core owners are `IsRegularLocalRing R`, `IsFiniteGlobalDimensionRing R`,
  and, for primewise propagation, `IsRegularRing R`;
* primitive data vs. derived API: the two owner predicates are primitive here, while the
  source-facing equivalence below and the localization theorem are derived API obtained from
  Proposition `10.110.5` and the regular-ring owner field.
* source/core/bridge triage:
  `isRegularLocalRing_iff_isFiniteGlobalDimensionRing` is `source-facing`,
  the owner predicates above are `core/canonical`,
  and `isRegularLocalRing_localizationAtPrime` is a `bridge/view` consequence of the regular-ring
  owner.

This file should therefore reuse those owners directly and avoid a parallel local proof/API layer.
-/

/-- Lemma 10.110.6: a Noetherian local ring is a regular local ring if and only if it has finite
global dimension. -/
theorem isRegularLocalRing_iff_isFiniteGlobalDimensionRing :
    IsRegularLocalRing R ↔ IsFiniteGlobalDimensionRing R := by
  simpa using
    (residueField_finiteProjectiveDimension_finiteGlobalDimension_regularLocal_tfae).out 2 1

variable [IsRegularLocalRing R]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Every localization of a regular local ring at a prime ideal is again a regular local ring. -/
theorem isRegularLocalRing_localizationAtPrime (p : PrimeSpectrum R) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
  IsRegularRing.isRegularLocalRing_atPrime p

end

/-! ### Definition_10_110_7 (from Chap10) -/
universe u

variable (R : Type u) [CommRing R]

/-
Source/core/bridge triage:
* source-facing: `IsRegularRing R`, the textbook global regularity condition;
* core/canonical: `IsRegularLocalRing (Localization.AtPrime p.asIdeal)` on each prime
  localization;
* bridge/view: the local-to-global instance sending a regular local ring to a regular ring.

Primitive data are exactly the Noetherian hypothesis and the primewise regular-local owner field.
No extra wrapper data are needed: primewise regularity and Noetherianity are the whole owner, and
all further API should be derived from that owner.
-/
/-- Definition 10.110.7: a Noetherian ring is regular if every localization at a prime ideal is a
regular local ring. -/
class IsRegularRing : Prop extends IsNoetherianRing R where
  isRegularLocalRing_atPrime :
    ∀ p : PrimeSpectrum R, IsRegularLocalRing (Localization.AtPrime p.asIdeal)

variable {R}

/-- A regular ring is Noetherian. -/
instance isNoetherianRing_of_regularRing [h : IsRegularRing R] : IsNoetherianRing R :=
  h.toIsNoetherian

namespace IsRegularRing

/-- A regular ring satisfies LinearRepresentations_Serre_1977's condition `(R_k)` for every `k`. -/
theorem serreConditionR (k : ℕ) [IsRegularRing R] : SerreConditionR R k :=
  { toIsNoetherian := inferInstance
    isRegularLocalRing_localizationAtPrime := fun p _ ↦
      IsRegularRing.isRegularLocalRing_atPrime p }

end IsRegularRing

-- Proof sketch: regular local rings remain regular after localization at prime ideals, so a
-- regular local ring satisfies the defining primewise condition for `IsRegularRing`.
/-- A regular local ring is regular in the global sense. -/
instance [IsRegularLocalRing R] : IsRegularRing R := sorry

/-! ### Lemma_10_110_8 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- 
Domain-style sampling:
* primary domain: homological and local characterizations of regular Noetherian rings;
* sampled owner declarations:
  `IsFiniteGlobalDimensionRing`,
  `IsRegularRing`,
  `globalDimension`,
  `isFiniteGlobalDimensionRing_iff_exists_uniform_bound_localizationAtMaximal`,
  `isRegularLocalRing_iff_isFiniteGlobalDimensionRing`;
* best owner abstraction: the core owners are `IsFiniteGlobalDimensionRing R` and
  `IsRegularRing R`; the fixed-`n` statements in this file should therefore use those owners
  directly, with only the equalities and localization bounds kept as source-facing clauses;
* primitive data vs. derived API: the owner predicates above are primitive, while the four fixed-
  `n` textbook clauses are derived API;
* source/core/bridge triage:
  `source-facing`: the fixed-`n` TFAE theorem and its four textbook clauses;
  `core/canonical`: `IsFiniteGlobalDimensionRing R`, `IsRegularRing R`, and the local equality
    theorem from Proposition `10.110.5`;
  `bridge/view`: the maximal-local finite-global-dimension criterion
    `isFiniteGlobalDimensionRing_iff_exists_uniform_bound_localizationAtMaximal` and the local
    equivalence `isRegularLocalRing_iff_isFiniteGlobalDimensionRing`.
-/

-- Proof sketch: apply the canonical maximal-local criterion
-- `isFiniteGlobalDimensionRing_iff_exists_uniform_bound_localizationAtMaximal` and the local
-- equivalence `isRegularLocalRing_iff_isFiniteGlobalDimensionRing` to each localization
-- `Localization.AtPrime m.asIdeal`. Proposition `10.110.5` identifies the corresponding local
-- global dimensions with local Krull dimensions, and Definition `10.110.7` upgrades the resulting
-- primewise regularity to `IsRegularRing R`. The equalities at some maximal or prime localization
-- then pin down the common integer `n`.
/-- Lemma 10.110.8: for a Noetherian ring `R`, the following are equivalent: `R` has finite global
dimension `n`, `R` is a regular ring of dimension `n`, every localization at a maximal ideal is a
regular local ring of dimension at most `n` with equality for at least one maximal ideal, and
every localization at a prime ideal is a regular local ring of dimension at most `n` with
equality for at least one prime ideal. -/
theorem finiteGlobalDimension_regularRing_localizations_tfae (n : ℕ) :
    List.TFAE
      [ ∃ _ : IsFiniteGlobalDimensionRing R, globalDimension R = n
      , IsRegularRing R ∧ ringKrullDim R = n
      , (∀ m : MaximalSpectrum R,
            IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
              ringKrullDim (Localization.AtPrime m.asIdeal) ≤ n) ∧
          ∃ m : MaximalSpectrum R, ringKrullDim (Localization.AtPrime m.asIdeal) = n
      , (∀ p : PrimeSpectrum R,
            IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
              ringKrullDim (Localization.AtPrime p.asIdeal) ≤ n) ∧
          ∃ p : PrimeSpectrum R, ringKrullDim (Localization.AtPrime p.asIdeal) = n ] := sorry

end
