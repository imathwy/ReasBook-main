import Mathlib
import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap10.Lemma_10_109_4
import StacksProject_2024.Chap10.Lemma_10_71_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
* primary domain: projective dimension together with bounded finite-projective resolutions of
  `ModuleCat R`;
* sampled owner declarations:
  `FiniteProjectiveModuleCat`,
  `finiteProjectiveModuleProperty`,
  `HasProjectiveDimensionLE`,
  `HasFiniteProjectiveResolutionLengthLE`;
* best owner abstraction: the bounded resolution is source-facing, but its terms should live in the
  canonical owner `FiniteProjectiveModuleCat R`, and the ambient module should be `M : ModuleCat R`
  rather than a raw type with repeated module structure fields;
* layer triage:
  `FiniteProjectiveModuleCat R` is `core/canonical`,
  `ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms` below is `source-facing`,
  the final equivalence with `HasProjectiveDimensionLE` is a `bridge/view`;
* primitive data: the finite exact sequence ending in `M`;
* derived API: finiteness and projectivity of the terms, supplied by the owner category rather than
  stored as separate primitive fields.
-/

namespace ModuleCat

/-- A finite projective resolution of `M` of length at most `d` whose terms are finite
`R`-modules. In degree `0`, this means that `M` itself is finite projective. -/
def HasFiniteProjectiveResolutionLengthLEWithFiniteTerms
    (M : ModuleCat.{u} R) (d : ℕ) : Prop :=
  match d with
  | 0 => Module.Projective R M ∧ Module.Finite R M
  | n + 1 =>
      ∃ (P : Fin (n + 2) → FiniteProjectiveModuleCat R)
        (δ : (i : Fin (n + 1)) → P i.succ ⟶ P i.castSucc)
        (π : (P 0).obj ⟶ M),
          Function.Surjective π ∧
            Function.Exact (δ 0).hom π ∧
            (∀ i : Fin n, Function.Exact (δ i.succ).hom (δ i.castSucc).hom) ∧
            Function.Injective (δ (Fin.last n)).hom

-- Proof sketch: unfold `HasFiniteProjectiveResolutionLengthLEWithFiniteTerms`; the `d = 0` branch
-- is defined to be the conjunction of projectivity and finite generation of `M`.
/-- In degree `0`, a finite-term projective resolution is exactly the assertion that `M` is a
finite projective `R`-module. -/
theorem hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff
    (M : ModuleCat.{u} R) :
    HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M 0 ↔
      Module.Projective R M ∧ Module.Finite R M :=
  Iff.rfl

variable {M : ModuleCat.{u} R}

-- Proof sketch: forgetting the full-subcategory structure keeps the same bounded exact sequence,
-- and the projectivity of each term is already available from the finite-projective packaging.
/-- Helper for Chap10 Lemma 10 109 6: a bounded resolution by finite projective objects forgets to a
bounded projective resolution in `ModuleCat R`. -/
theorem hasFiniteProjectiveResolutionLengthLE_of_withFiniteTerms {d : ℕ}
    (hM : HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M d) :
    HasFiniteProjectiveResolutionLengthLE (M := M) d := by
  cases d with
  | zero =>
      -- In degree `0`, the finite-term resolution stores finite projectivity of `M` itself.
      let _ : Module.Projective R M := hM.1
      simpa [HasFiniteProjectiveResolutionLengthLE] using
        (show Projective M from inferInstance)
  | succ n =>
      rcases hM with ⟨P, δ, π, hπ, hExact₀, hExact, hInj⟩
      let δ' :
          (i : Fin (n + 1)) → (fun i ↦ (P i).obj) i.succ ⟶ (fun i ↦ (P i).obj) i.castSucc :=
        fun i ↦ (finiteProjectiveModuleProperty R).ι.map (δ i)
      -- We keep the same maps and simply forget that the terms lie in the full subcategory.
      refine ⟨fun i ↦ (P i).obj, ?_, δ', π, hπ, ?_, ?_, ?_⟩
      · intro i
        infer_instance
      · simpa [δ'] using hExact₀
      · intro i
        simpa [δ'] using hExact i
      · simpa [δ'] using hInj

/-- Helper for Chap10 Lemma 10 109 6: a finite projective `ModuleCat R` object determines an object of
`FiniteProjectiveModuleCat R`. -/
abbrev toFiniteProjective (X : ModuleCat.{u} R)
    [Module.Finite R X] [Module.Projective R X] :
    FiniteProjectiveModuleCat R :=
  ⟨X, ⟨inferInstance, inferInstance⟩⟩

/-- Helper for Chap10 Lemma 10 109 6: a finite module with categorical projectivity defines an object of
`FiniteProjectiveModuleCat R`. -/
abbrev toFiniteProjectiveOfProjective (X : ModuleCat.{u} R)
    [Module.Finite R X] (hX : Projective X) :
    FiniteProjectiveModuleCat R :=
  let _ : Module.Projective R X := module_projective_of_categorical_projective (R := R) hX
  toFiniteProjective X

/-- Helper for Chap10 Lemma 10 109 6: a finite projective presentation whose kernel has a
finite-term projective resolution gives a finite-term projective resolution of the target. -/
theorem hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_succ_of_finite_projective_presentation
    {M' P₀ : ModuleCat.{u} R} (π : P₀ ⟶ M')
    [Module.Finite R P₀] [Module.Projective R P₀]
    (hπ : Function.Surjective π.hom) {n : ℕ}
    (hker :
      HasFiniteProjectiveResolutionLengthLEWithFiniteTerms
        (ModuleCat.of R (LinearMap.ker π.hom)) n) :
    HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M' (n + 1) := by
  cases n with
  | zero =>
      rw [hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff] at hker
      let _ : Module.Projective R (ModuleCat.of R (LinearMap.ker π.hom)) := hker.1
      let _ : Module.Finite R (ModuleCat.of R (LinearMap.ker π.hom)) := hker.2
      let P' : Fin 2 → FiniteProjectiveModuleCat R :=
        Fin.cons
          (toFiniteProjective P₀)
          (fun _ : Fin 1 ↦ toFiniteProjective (ModuleCat.of R (LinearMap.ker π.hom)))
      let κ : P' (Fin.succ 0) ⟶ P' (Fin.castSucc 0) :=
        ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.ker π.hom).subtype)
      let δ' : (i : Fin 1) → P' i.succ ⟶ P' i.castSucc :=
        Fin.cases κ (fun i : Fin 0 ↦ Fin.elim0 i)
      -- The base case is the short exact sequence
      -- `0 → ker π → P₀ → M' → 0`.
      refine ⟨P', δ', π, hπ, ?_, ?_, ?_⟩
      · simpa [δ', κ] using LinearMap.exact_subtype_ker_map π.hom
      · intro i
        exact Fin.elim0 i
      · intro x y hxy
        exact Subtype.ext hxy
  | succ n =>
      rcases hker with ⟨P, δ, πK, hπK, hExact₀, hExact, hInj⟩
      let κBase : (P 0).obj ⟶ P₀ :=
        πK ≫ ModuleCat.ofHom (LinearMap.ker π.hom).subtype
      let P' : Fin (n + 3) → FiniteProjectiveModuleCat R :=
        Fin.cons (toFiniteProjective P₀) P
      let κ : P' (Fin.succ 0) ⟶ P' (Fin.castSucc 0) :=
        ObjectProperty.homMk κBase
      let δ' : (i : Fin (n + 2)) → P' i.succ ⟶ P' i.castSucc :=
        Fin.cases κ fun i ↦ δ i
      -- We prepend the finite projective presentation `P₀ ⟶ M'` to the kernel resolution.
      refine ⟨P', δ', π, hπ, ?_, ?_, ?_⟩
      · have hκ_exact :
            Function.Exact ((LinearMap.ker π.hom).subtype.comp πK.hom) π.hom :=
          (Function.Surjective.comp_exact_iff_exact
            (f := (LinearMap.ker π.hom).subtype) (g := π.hom) hπK).2
            (LinearMap.exact_subtype_ker_map π.hom)
        simpa [δ', κ, κBase] using hκ_exact
      · intro i
        cases i using Fin.cases with
        | zero =>
            -- The first shifted exactness follows because the kernel subtype map is injective.
            have hsub_inj : Function.Injective (LinearMap.ker π.hom).subtype :=
              Submodule.injective_subtype (LinearMap.ker π.hom)
            have hExact₀' :
                Function.Exact ((δ 0).hom).hom
                  ((LinearMap.ker π.hom).subtype.comp πK.hom) :=
              (Function.Injective.comp_exact_iff_exact
                (f := ((δ 0).hom).hom) (g := πK.hom)
                (i := (LinearMap.ker π.hom).subtype) hsub_inj).2 hExact₀
            simpa [δ', κ, κBase] using hExact₀'
        | succ i =>
            -- Farther left, exactness is inherited from the kernel resolution.
            simpa [δ'] using hExact i
      · -- The top differential is unchanged by prepending one degree.
        simpa [δ'] using hInj

/-- Helper for Chap10 Lemma 10 109 6: an exact finite projective prefix whose top kernel is
finite projective gives a finite-term projective resolution of the target. -/
theorem hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_of_shifted_exact_of_finite_projective_top_kernel
    {e : ℕ} {M' : ModuleCat.{u} R}
    {F : Fin (e + 2) → ModuleCat.{u} R}
    (hFfinite : ∀ i, Module.Finite R (F i))
    (hFprojective : ∀ i, Module.Projective R (F i))
    (δ : (i : Fin (e + 1)) → F i.succ ⟶ F i.castSucc)
    (π : F 0 ⟶ M')
    (hπ : Function.Surjective π.hom)
    (hExact₀ : Function.Exact (δ 0).hom π.hom)
    (hExact : ∀ i : Fin e, Function.Exact (δ i.succ).hom (δ i.castSucc).hom)
    (htopFinite : Module.Finite R (ModuleCat.of R (LinearMap.ker (δ (Fin.last e)).hom)))
    (htopProjective :
      Module.Projective R (ModuleCat.of R (LinearMap.ker (δ (Fin.last e)).hom))) :
    HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M' (e + 2) := by
  induction e generalizing M' with
  | zero =>
      let κ : F 1 ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom <|
          LinearMap.codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hκ_surj : Function.Surjective κ.hom := by
        -- Exactness at `F₀` identifies the first syzygy with the image of `δ₀`.
        intro x
        rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_ker : LinearMap.ker κ.hom = LinearMap.ker (δ 0).hom := by
        -- Restricting the codomain to `ker π` preserves the kernel of `δ₀`.
        simpa [κ] using
          LinearMap.ker_codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hker₀ :
          HasFiniteProjectiveResolutionLengthLEWithFiniteTerms
            (ModuleCat.of R (LinearMap.ker κ.hom)) 0 := by
        have hfinite : Module.Finite R (ModuleCat.of R (LinearMap.ker κ.hom)) :=
          hκ_ker.symm ▸ htopFinite
        have hprojective : Module.Projective R (ModuleCat.of R (LinearMap.ker κ.hom)) :=
          hκ_ker.symm ▸ htopProjective
        exact ⟨hprojective, hfinite⟩
      let _ : Module.Finite R (F 1) := hFfinite 1
      let _ : Module.Projective R (F 1) := hFprojective 1
      have hker :
          HasFiniteProjectiveResolutionLengthLEWithFiniteTerms
            (ModuleCat.of R (LinearMap.ker π.hom)) 1 :=
        hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_succ_of_finite_projective_presentation
          (R := R) κ hκ_surj hker₀
      let _ : Module.Finite R (F 0) := hFfinite 0
      let _ : Module.Projective R (F 0) := hFprojective 0
      -- Prepending `F₀ ⟶ M'` recovers the desired two-step finite-term resolution.
      exact
        hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_succ_of_finite_projective_presentation
          (R := R) π hπ hker
  | succ e ih =>
      let κ : F 1 ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom <|
          LinearMap.codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hκ_surj : Function.Surjective κ.hom := by
        -- Exactness at `F₀` identifies `ker π` with the image of the first differential.
        intro x
        rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_exact : Function.Exact (δ 1).hom κ.hom := by
        -- Since the kernel subtype is injective, exactness survives the codomain restriction.
        have hsub_inj : Function.Injective (LinearMap.ker π.hom).subtype :=
          Submodule.injective_subtype (LinearMap.ker π.hom)
        have hExact₁ :
            Function.Exact (δ 1).hom ((LinearMap.ker π.hom).subtype.comp κ.hom) := by
          simpa [κ] using hExact 0
        exact (Function.Injective.comp_exact_iff_exact
          (f := (δ 1).hom) (g := κ.hom) hsub_inj).1 hExact₁
      let F' : Fin (e + 2) → ModuleCat.{u} R := fun i ↦ F i.succ
      let δ' : (i : Fin (e + 1)) → F' i.succ ⟶ F' i.castSucc := fun i ↦ δ i.succ
      have hExact' : ∀ i : Fin e, Function.Exact (δ' i.succ).hom (δ' i.castSucc).hom := by
        intro i
        -- The shifted tail inherits exactness from the original exact prefix.
        simpa [δ'] using hExact i.succ
      have hker :
          HasFiniteProjectiveResolutionLengthLEWithFiniteTerms
            (ModuleCat.of R (LinearMap.ker π.hom)) (e + 2) := by
        -- After shifting once, the top kernel is the same kernel as before.
        simpa [δ', Fin.succ_last] using
          ih (M' := ModuleCat.of R (LinearMap.ker π.hom))
            (F := F') (hFfinite := fun i ↦ hFfinite i.succ)
            (hFprojective := fun i ↦ hFprojective i.succ)
            (δ := δ') (π := κ) hκ_surj hκ_exact hExact'
            htopFinite htopProjective
      let _ : Module.Finite R (F 0) := hFfinite 0
      let _ : Module.Projective R (F 0) := hFprojective 0
      -- One finite projective presentation step returns from the first syzygy to `M'`.
      exact
        hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_succ_of_finite_projective_presentation
          (R := R) π hπ hker

end ModuleCat

namespace CategoryTheory.ProjectiveResolution

section

variable {M : ModuleCat.{u} R}

/-- Helper for Chap10 Lemma 10 109 6: if a projective resolution has finite terms and projective `d`th
syzygy, then truncating at that syzygy yields a bounded resolution by finite projective modules. -/
theorem hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_of_syzygyProjective
    (P : ProjectiveResolution M) [IsNoetherianRing R] [Module.Finite R M]
    (hfinite : ∀ n, Module.Finite R (P.complex.X n))
    {d : ℕ} (hsyz : P.SyzygyProjective d) :
    ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M d := by
  cases d with
  | zero =>
      -- In degree `0`, the syzygy condition is exactly projectivity of `M`, while finiteness of
      -- `M` is an ambient hypothesis of the finite-module statement.
      have hproj : Module.Projective R M :=
        module_projective_of_categorical_projective (R := R) hsyz
      exact ⟨hproj, inferInstance⟩
  | succ d =>
      cases d with
      | zero =>
          have hπ : Function.Surjective (P.π.f 0).hom :=
            (ModuleCat.epi_iff_surjective _).mp inferInstance
          let _ : Module.Finite R (P.complex.X 0) := hfinite 0
          let _ : Module.Finite R (ModuleCat.of R (LinearMap.ker (P.π.f 0).hom)) :=
            kernel_finite_of_domain_finite (R := R) (P.π.f 0)
          let _ : Module.Projective R (ModuleCat.of R (LinearMap.ker (P.π.f 0).hom)) :=
            module_projective_of_categorical_projective (R := R) hsyz
          let P₀ : Fin 2 → FiniteProjectiveModuleCat R :=
            Fin.cons
              (ModuleCat.toFiniteProjectiveOfProjective (P.complex.X 0) (P.projective 0))
              (fun _ : Fin 1 ↦
                ModuleCat.toFiniteProjective (ModuleCat.of R (LinearMap.ker (P.π.f 0).hom)))
          let κ : P₀ (Fin.succ 0) ⟶ P₀ (Fin.castSucc 0) :=
            ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.ker (P.π.f 0).hom).subtype)
          let δ₀ : (i : Fin 1) → P₀ i.succ ⟶ P₀ i.castSucc :=
            Fin.cases κ (fun i : Fin 0 ↦ Fin.elim0 i)
          -- The length-one case is the defining short exact sequence
          -- `0 → ker(P₀ ⟶ M) → P₀ → M → 0`.
          refine ⟨P₀, δ₀, P.π.f 0, hπ, ?_, ?_, ?_⟩
          · simpa [δ₀] using LinearMap.exact_subtype_ker_map (P.π.f 0).hom
          · intro i
            exact Fin.elim0 i
          · simpa [δ₀] using
              Submodule.injective_subtype (LinearMap.ker (P.π.f 0).hom)
      | succ e =>
          have hπ : Function.Surjective (P.π.f 0).hom :=
            (ModuleCat.epi_iff_surjective _).mp inferInstance
          let K : ModuleCat.{u} R :=
            ModuleCat.of R (LinearMap.ker (P.complex.d (e + 1) e).hom)
          have hK_finite : Module.Finite R K := by
            -- The truncated top term is finite because it is a kernel inside a finite module.
            simpa [K] using
              kernel_finite_of_domain_finite (R := R) (P.complex.d (e + 1) e)
          have hK_projective : Module.Projective R K := by
            -- The source proof truncates at the projective `d`th syzygy.
            simpa [K] using module_projective_of_categorical_projective (R := R) hsyz
          have hExact :
              ∀ i : Fin e,
                Function.Exact
                  (P.complex.d i.succ.succ i.succ.castSucc).hom
                  (P.complex.d i.succ.castSucc i.castSucc.castSucc).hom := by
            intro i
            -- Consecutive exactness in the projective resolution supplies the shifted tail.
            simpa using projectiveResolution_exact_succ_linearMap (R := R) P (i : ℕ)
          -- Route correction: the earlier `Fin.snoc` construction got stuck transporting
          -- exactness through full-subcategory `eqToHom`s.  We instead use the abstract
          -- finite exact-prefix helper, whose maps are the original projective-resolution maps.
          exact
            ModuleCat.hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_of_shifted_exact_of_finite_projective_top_kernel
              (R := R) (M' := M) (F := fun i : Fin (e + 2) ↦ P.complex.X i)
              (hFfinite := fun i ↦ hfinite i)
              (hFprojective := fun i ↦
                module_projective_of_categorical_projective (R := R) (P.projective i))
              (δ := fun i : Fin (e + 1) ↦ P.complex.d i.succ i.castSucc)
              (π := P.π.f 0) hπ
              (projectiveResolution_exact_zero_linearMap (R := R) P)
              hExact hK_finite hK_projective

end

end CategoryTheory.ProjectiveResolution

section

variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: a finite free resolution gives a projective resolution whose terms are finite;
-- Lemma `10.109.4` then makes the `d`th syzygy projective, and the preceding helper truncates
-- the finite free resolution at that projective syzygy.
/-- Helper for Chap10 Lemma 10 109 6: a projective-dimension bound yields a bounded resolution by finite
projective modules. -/
theorem hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_of_hasProjectiveDimensionLE
    [IsNoetherianRing R] [Module.Finite R M] {d : ℕ}
    (hpd : HasProjectiveDimensionLE (ModuleCat.of R M) d) :
    ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms (ModuleCat.of R M) d := by
  cases d with
  | zero =>
      -- In degree `0`, projective dimension `≤ 0` means that `M` itself is projective.
      have hproj : Projective (ModuleCat.of R M) :=
        (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero (ModuleCat.of R M)).2 hpd
      exact ⟨module_projective_of_categorical_projective (R := R) hproj, inferInstance⟩
  | succ d =>
      rcases module_exists_finite_free_resolution (R := R) (M := M) with ⟨F, π, hF⟩
      letI : ChainComplex.IsFiniteFreeResolution π := hF
      let P : ProjectiveResolution (ModuleCat.of R M) :=
        ChainComplex.IsFreeResolution.toProjectiveResolution π
      have hfinite : ∀ n, Module.Finite R (P.complex.X n) := by
        intro n
        simpa [P] using ChainComplex.IsFiniteFreeResolution.finite π n
      have hsyz : P.SyzygyProjective (d + 1) :=
        CategoryTheory.ProjectiveResolution.syzygyProjective_of_hasProjectiveDimensionLE
          (R := R) (M := ModuleCat.of R M) (P := P) hpd
      -- The chosen finite free resolution is source-faithful; we now truncate it at the
      -- projective syzygy guaranteed by Lemma `10.109.4`.
      simpa using
        CategoryTheory.ProjectiveResolution.hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_of_syzygyProjective
          (R := R) (M := ModuleCat.of R M) (P := P) hfinite hsyz

-- Proof sketch: combine Lemma `10.109.4`, which identifies projective dimension `≤ d` with the
-- existence of a bounded projective resolution, with Lemma `10.71.1`, which provides a finite
-- free resolution of `M`; the `d`th syzygy is then finite as a submodule of a finite free module
-- over a Noetherian ring, so the projective top term may be replaced by that finite syzygy.
/-- Chap10 Lemma 10 109 6: for a finite module `M` over a Noetherian ring `R`, having projective
dimension at most `d` is equivalent to admitting a resolution
`0 ⟶ P_d ⟶ P_{d-1} ⟶ ⋯ ⟶ P₀ ⟶ M ⟶ 0`
in which every `Pᵢ` is a finite projective `R`-module. -/
@[stacks 0CXE]
theorem hasProjectiveDimensionLE_iff_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
    [IsNoetherianRing R] [Module.Finite R M] (d : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R M) d ↔
      ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms (ModuleCat.of R M) d := by
  constructor
  · -- The forward implication is the textbook free-resolution construction over a Noetherian ring.
    exact hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_of_hasProjectiveDimensionLE
      (R := R) (M := M)
  · intro hfinite
    -- Forgetting the finite-term packaging recovers the bounded projective resolution of
    -- Lemma `10.109.4`, hence the same projective-dimension bound.
    exact hasProjectiveDimensionLE_of_hasFiniteProjectiveResolutionLengthLE
      (M := ModuleCat.of R M)
      (ModuleCat.hasFiniteProjectiveResolutionLengthLE_of_withFiniteTerms (R := R) hfinite)

end
end
