import Mathlib
import StacksProject_2024.Chap10.Lemma_10_109_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

section

variable {R : Type v} [Ring R]

/-
Domain-style sampling:
* primary domain: projective dimension in `ModuleCat R`, together with projective resolutions and
  source-facing bounded exact sequences.
* inspected owner declarations:
  `CategoryTheory.ProjectiveResolution`,
  `CategoryTheory.projectiveResolution`,
  `CategoryTheory.HasProjectiveDimensionLE`,
  `CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero`,
  `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`.
* best owner abstraction: `P : ProjectiveResolution M` for `M : ModuleCat R`.
* layer triage:
  `ProjectiveResolution.SyzygyProjective` is `core/canonical`,
  `HasFiniteProjectiveResolutionLengthLE` is `source-facing`,
  the TFAE below is a `bridge/view` between them and `HasProjectiveDimensionLE`.
* primitive data: the owner object `P : ProjectiveResolution M`.
* derived API: projectivity of the `d`th syzygy and the bounded finite-sequence reformulation of
  `HasProjectiveDimensionLE`.
-/

namespace CategoryTheory.ProjectiveResolution

variable {M : ModuleCat.{v} R}

/-- The textbook syzygy condition attached to a projective resolution in degree `d`. For `d = 0`
this says that `M` is projective, for `d = 1` it says that `ker(P₀ ⟶ M)` is projective, and for
`d ≥ 2` it says that `ker(P_{d-1} ⟶ P_{d-2})` is projective. -/
def SyzygyProjective (P : ProjectiveResolution M) (d : ℕ) : Prop :=
  match d with
  | 0 => Projective M
  | 1 => Projective (ModuleCat.of R (LinearMap.ker (P.π.f 0).hom))
  | n + 2 => Projective (ModuleCat.of R (LinearMap.ker (P.complex.d (n + 1) n).hom))

-- Proof sketch: unfold `SyzygyProjective` and read off the `d = 0` branch.
/-- In degree `0`, the syzygy-projective condition is exactly projectivity of `M`. -/
theorem syzygyProjective_zero_iff (P : ProjectiveResolution M) :
    P.SyzygyProjective 0 ↔ Projective M :=
  Iff.rfl

end CategoryTheory.ProjectiveResolution

variable (M : ModuleCat.{v} R)

/-- `M` admits a finite projective resolution of length at most `d`. For `d = 0` this means that
`M` itself is projective; for `d = n + 1` it is an exact sequence
`0 ⟶ P_{n+1} ⟶ P_n ⟶ ⋯ ⟶ P₀ ⟶ M ⟶ 0`
with every `Pᵢ` projective. -/
def HasFiniteProjectiveResolutionLengthLE (d : ℕ) : Prop :=
  match d with
  | 0 => Projective M
  | n + 1 =>
      ∃ (P : Fin (n + 2) → ModuleCat.{v} R),
        (∀ i, Projective (P i)) ∧
          ∃ (δ : (i : Fin (n + 1)) → P i.succ ⟶ P i.castSucc)
            (π : P 0 ⟶ M),
            Function.Surjective π ∧
              Function.Exact (δ 0) π ∧
              (∀ i : Fin n, Function.Exact (δ i.succ) (δ i.castSucc)) ∧
              Function.Injective (δ (Fin.last n))

-- Proof sketch: unfold `HasFiniteProjectiveResolutionLengthLE`; the `d = 0` branch is defined to
-- be projectivity of `M`.
/-- A finite projective resolution of length at most `0` is exactly projectivity of `M`. -/
theorem hasFiniteProjectiveResolutionLengthLE_zero_iff :
    HasFiniteProjectiveResolutionLengthLE M 0 ↔ Projective M :=
  Iff.rfl

/-- Helper for Lemma 10.109.4: a finite projective resolution of positive length starts with a
projective presentation whose kernel still has a finite projective resolution of one shorter
length. -/
theorem exists_projective_presentation_with_finite_kernel_resolution {n : ℕ}
    (hM : HasFiniteProjectiveResolutionLengthLE M (n + 1)) :
    ∃ (P₀ : ModuleCat.{v} R) (π : P₀ ⟶ M),
      Projective P₀ ∧
        Function.Surjective π ∧
          HasFiniteProjectiveResolutionLengthLE (ModuleCat.of R (LinearMap.ker π.hom)) n := by
  cases n with
  | zero =>
      rcases hM with ⟨P, hP, δ, π, hπ, hExact, _, hInj⟩
      refine ⟨P 0, π, hP 0, hπ, ?_⟩
      let κ : P 1 ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom (LinearMap.codRestrict (LinearMap.ker π.hom) (δ 0).hom (fun x ↦ by
          -- Exactness at `P₀` identifies the image of `δ₀` with `ker π`.
          simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
            LinearMap.congr_fun hExact.linearMap_comp_eq_zero x))
      have hκ_surj : Function.Surjective κ := by
        intro x
        rcases (hExact x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_inj : Function.Injective κ := by
        intro x y hxy
        exact hInj (by simpa [κ] using congrArg Subtype.val hxy)
      let e : P 1 ≅ ModuleCat.of R (LinearMap.ker π.hom) :=
        (LinearEquiv.ofBijective κ.hom ⟨hκ_inj, hκ_surj⟩).toModuleIso
      -- The leftmost projective module is isomorphic to the kernel, so the kernel is projective.
      simpa [HasFiniteProjectiveResolutionLengthLE] using Projective.of_iso e (hP (Fin.last 1))
  | succ n =>
      rcases hM with ⟨P, hP, δ, π, hπ, hExact₀, hExact, hInj⟩
      refine ⟨P 0, π, hP 0, hπ, ?_⟩
      let κ : P 1 ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom (LinearMap.codRestrict (LinearMap.ker π.hom) (δ 0).hom (fun x ↦ by
          -- Exactness at `P₀` shows that `δ₀` factors through `ker π`.
          simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
            LinearMap.congr_fun hExact₀.linearMap_comp_eq_zero x))
      have hκ_surj : Function.Surjective κ := by
        intro x
        rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_ker : LinearMap.ker κ.hom = LinearMap.ker (δ 0).hom := by
        simpa [κ] using LinearMap.ker_codRestrict (LinearMap.ker π.hom) (δ 0).hom (fun x ↦ by
          simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
            LinearMap.congr_fun hExact₀.linearMap_comp_eq_zero x)
      let P' : Fin (n + 2) → ModuleCat.{v} R := fun i ↦ P i.succ
      let δ' : (i : Fin (n + 1)) → P' i.succ ⟶ P' i.castSucc := fun i ↦ δ i.succ
      refine ⟨P', ?_, δ', κ, hκ_surj, ?_, ?_, ?_⟩
      · intro i
        -- The truncated family inherits projectivity degreewise.
        exact hP i.succ
      · -- Exactness of `δ₁` against the restricted presentation map is the shifted first exactness.
        exact LinearMap.exact_iff.mpr <| hκ_ker.trans (hExact 0).linearMap_ker_eq
      · intro i
        -- Every later exactness statement is inherited verbatim from the original sequence.
        simpa [δ', Fin.castSucc_succ] using hExact i.succ
      · -- The top differential of the truncated finite resolution is the original top differential.
        simpa [δ'] using hInj

/-- Helper for Lemma 10.109.4: a finite projective resolution of length at most `d` gives the
owner-level projective-dimension bound `HasProjectiveDimensionLE M d`. -/
theorem hasProjectiveDimensionLE_of_hasFiniteProjectiveResolutionLengthLE {d : ℕ}
    (hM : HasFiniteProjectiveResolutionLengthLE M d) :
    HasProjectiveDimensionLE M d := by
  induction d generalizing M with
  | zero =>
      -- The base case is exactly the characterization of projectivity.
      rw [hasFiniteProjectiveResolutionLengthLE_zero_iff] at hM
      exact (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).1 hM
  | succ d ih =>
      rcases exists_projective_presentation_with_finite_kernel_resolution (M := M) hM with
        ⟨P₀, π, hP₀, hπ, hker⟩
      have hker_pd :
          HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π.hom)) d :=
        ih (M := ModuleCat.of R (LinearMap.ker π.hom)) hker
      let S : ShortComplex (ModuleCat.{v} R) := LinearMap.shortComplexKer π.hom
      have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hπ
      -- The short exact sequence `0 → ker π → P₀ → M → 0` raises the bound by one.
      simpa [S, HasProjectiveDimensionLE] using
        (hS.hasProjectiveDimensionLT_X₃_iff d hP₀).mpr (by
          simpa [HasProjectiveDimensionLE] using hker_pd)

/-- Helper for Lemma 10.109.4: an exact pair of linear maps factors through the kernel of the
second map. -/
theorem linearMap_mem_ker_of_exact {A B C : Type v}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (hExact : Function.Exact f g) :
    ∀ x, f x ∈ LinearMap.ker g := by
  -- Exactness says `g ∘ f = 0`, so every value of `f` lands in `ker g`.
  intro x
  simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
    LinearMap.congr_fun hExact.linearMap_comp_eq_zero x

/-- Helper for Lemma 10.109.4: the first differential of a projective resolution is exact against
the augmentation map as a pair of linear maps. -/
theorem projectiveResolution_exact_zero_linearMap
    {M : ModuleCat.{v} R} (P : CategoryTheory.ProjectiveResolution M) :
    Function.Exact (P.complex.d 1 0).hom (P.π.f 0).hom := by
  -- We translate the categorical exactness statement into the linear-map exactness used below.
  simpa using (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀

/-- Helper for Lemma 10.109.4: consecutive differentials in a projective resolution are exact as
linear maps. -/
theorem projectiveResolution_exact_succ_linearMap
    {M : ModuleCat.{v} R} (P : CategoryTheory.ProjectiveResolution M) (n : ℕ) :
    Function.Exact (P.complex.d (n + 2) (n + 1)).hom (P.complex.d (n + 1) n).hom := by
  -- Again we pass from the categorical exactness owner theorem to the linear-map formulation.
  simpa using (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (P.exact_succ n)

/-- Helper for Lemma 10.109.4: if a projective presentation has kernel with a finite projective
resolution of length at most `n`, then the target has one of length at most `n + 1`. -/
theorem hasFiniteProjectiveResolutionLengthLE_succ_of_projective_presentation
    {P₀ : ModuleCat.{v} R} (π : P₀ ⟶ M) (hP₀ : Projective P₀)
    (hπ : Function.Surjective π.hom) {n : ℕ}
    (hker : HasFiniteProjectiveResolutionLengthLE (ModuleCat.of R (LinearMap.ker π.hom)) n) :
    HasFiniteProjectiveResolutionLengthLE M (n + 1) := by
  cases n with
  | zero =>
      rw [hasFiniteProjectiveResolutionLengthLE_zero_iff] at hker
      let κ : ModuleCat.of R (LinearMap.ker π.hom) ⟶ P₀ :=
        ModuleCat.ofHom (LinearMap.ker π.hom).subtype
      -- The length-one case is the defining short exact sequence `0 → ker π → P₀ → M → 0`.
      refine ⟨Fin.cons P₀ (fun _ : Fin 1 ↦ ModuleCat.of R (LinearMap.ker π.hom)), ?_,
        Fin.cases κ (fun i : Fin 0 ↦ Fin.elim0 i), π,
        hπ, ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · simpa using hP₀
        · simpa using hker
      · simpa [κ] using LinearMap.exact_subtype_ker_map π.hom
      · intro i
        exact Fin.elim0 i
      · exact Submodule.injective_subtype (LinearMap.ker π.hom)
  | succ n =>
      rcases hker with ⟨P, hP, δ, πK, hπK, hExact₀, hExact, hInj⟩
      let κ : P 0 ⟶ P₀ := πK ≫ ModuleCat.ofHom (LinearMap.ker π.hom).subtype
      let P' : Fin (n + 3) → ModuleCat.{v} R := Fin.cons P₀ P
      let δ' : (i : Fin (n + 2)) → P' i.succ ⟶ P' i.castSucc :=
        Fin.cases κ fun i ↦ δ i
      -- We prepend `P₀ ⟶ M` to the finite resolution of `ker π`.
      refine ⟨P', ?_, δ', π, hπ, ?_, ?_, ?_⟩
      · intro i
        cases i using Fin.cases with
        | zero =>
            simpa [P'] using hP₀
        | succ i =>
            simpa [P'] using hP i
      · -- Surjectivity of `πK` identifies the image of `κ` with `ker π`.
        have hκ_exact :
            Function.Exact ((LinearMap.ker π.hom).subtype.comp πK.hom) π.hom :=
          (Function.Surjective.comp_exact_iff_exact
            (f := (LinearMap.ker π.hom).subtype) (g := π.hom) hπK).2
            (LinearMap.exact_subtype_ker_map π.hom)
        simpa [κ] using hκ_exact
      · intro i
        cases i using Fin.cases with
        | zero =>
            -- The next exactness statement is unchanged because the subtype map is injective.
            have hsub_inj : Function.Injective (LinearMap.ker π.hom).subtype :=
              Submodule.injective_subtype (LinearMap.ker π.hom)
            have hExact₀' :
                Function.Exact (δ 0).hom ((LinearMap.ker π.hom).subtype.comp πK.hom) :=
              (Function.Injective.comp_exact_iff_exact
                (f := (δ 0).hom) (g := πK.hom) hsub_inj).2 hExact₀
            simpa [δ', κ] using hExact₀'
        | succ i =>
            -- Farther to the left, the exactness statements are inherited verbatim.
            simpa [δ'] using hExact i
      · -- The top differential is unchanged when we prepend a new degree-zero term.
        simpa [δ'] using hInj

/-- Helper for Lemma 10.109.4: in an exact sequence
`F_{e+1} → ⋯ → F₀ → M → 0` of projective modules, a bound
`HasProjectiveDimensionLE M (e + 2)` forces the kernel of the top differential to be projective. -/
theorem projective_top_kernel_of_shifted_exact_of_hasProjectiveDimensionLE
    {e : ℕ} {M' : ModuleCat.{v} R}
    {F : Fin (e + 2) → ModuleCat.{v} R}
    (hF : ∀ i, Projective (F i))
    (δ : (i : Fin (e + 1)) → F i.succ ⟶ F i.castSucc)
    (π : F 0 ⟶ M')
    (hπ : Function.Surjective π.hom)
    (hExact₀ : Function.Exact (δ 0).hom π.hom)
    (hExact : ∀ i : Fin e, Function.Exact (δ i.succ).hom (δ i.castSucc).hom)
    (hpd : HasProjectiveDimensionLE M' (e + 2)) :
    Projective (ModuleCat.of R (LinearMap.ker (δ (Fin.last e)).hom)) := by
  induction e generalizing M' with
  | zero =>
      let κ : F 1 ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom <|
          LinearMap.codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hκ_surj : Function.Surjective κ.hom := by
        -- Exactness at `F₀` identifies `ker π` with the image of `δ₀`.
        intro x
        rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_ker : LinearMap.ker κ.hom = LinearMap.ker (δ 0).hom := by
        simpa [κ] using
          LinearMap.ker_codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      let _ : Module.Projective R (F 0) :=
        module_projective_of_categorical_projective (R := R) (P := F 0) (hF 0)
      have hpd' : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π.hom)) 1 :=
        hasProjectiveDimensionLE_first_syzygy_of_surjective
          (R := R) (M := M') (π := π.hom) hπ hpd
      let _ : Module.Projective R (F 1) :=
        module_projective_of_categorical_projective (R := R) (P := F 1) (hF 1)
      have hprojκ : Module.Projective R (LinearMap.ker κ.hom) :=
        projective_ker_of_surjective_of_hasProjectiveDimensionLE_one
          (R := R) (M := LinearMap.ker π.hom) κ.hom hκ_surj hpd'
      let _ : Module.Projective R (LinearMap.ker (δ 0).hom) := hκ_ker ▸ hprojκ
      -- The kernel of `κ` is the same top kernel as the original two-step exact sequence.
      simpa using
        (show Projective (ModuleCat.of R (LinearMap.ker (δ 0).hom)) from inferInstance)
  | succ e ih =>
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
        simpa [κ] using
          LinearMap.ker_codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hκ_exact : Function.Exact (δ 1).hom κ.hom := by
        -- Restricting the codomain to `ker π` preserves exactness because the subtype map
        -- is injective.
        have hsub_inj : Function.Injective (LinearMap.ker π.hom).subtype :=
          Submodule.injective_subtype (LinearMap.ker π.hom)
        have hExact₁ :
            Function.Exact (δ 1).hom ((LinearMap.ker π.hom).subtype.comp κ.hom) := by
          simpa [κ] using hExact 0
        exact (Function.Injective.comp_exact_iff_exact
          (f := (δ 1).hom) (g := κ.hom) hsub_inj).1 hExact₁
      let _ : Module.Projective R (F 0) :=
        module_projective_of_categorical_projective (R := R) (P := F 0) (hF 0)
      have hpd' : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π.hom)) (e + 2) :=
        hasProjectiveDimensionLE_first_syzygy_of_surjective
          (R := R) (M := M') (π := π.hom) hπ hpd
      let F' : Fin (e + 2) → ModuleCat.{v} R := fun i ↦ F i.succ
      let δ' : (i : Fin (e + 1)) → F' i.succ ⟶ F' i.castSucc := fun i ↦ δ i.succ
      have hExact' : ∀ i : Fin e, Function.Exact (δ' i.succ).hom (δ' i.castSucc).hom := by
        intro i
        simpa [δ'] using hExact i.succ
      -- Route correction: instead of calling Lemma `10.109.3` at the original indexing, we
      -- shift once to `ker π` and recurse on the truncated exact sequence.
      simpa [δ', Fin.succ_last] using
        ih (M' := ModuleCat.of R (LinearMap.ker π.hom))
          (F := F') (hF := fun i ↦ hF i.succ) (δ := δ') (π := κ)
          hκ_surj hκ_exact hExact' hpd'

/-- Helper for Lemma 10.109.4: if the top kernel in an exact sequence of projectives is
projective, then truncating there gives a finite projective resolution. -/
theorem hasFiniteProjectiveResolutionLengthLE_of_shifted_exact_of_projective_top_kernel
    {e : ℕ} {M' : ModuleCat.{v} R}
    {F : Fin (e + 2) → ModuleCat.{v} R}
    (hF : ∀ i, Projective (F i))
    (δ : (i : Fin (e + 1)) → F i.succ ⟶ F i.castSucc)
    (π : F 0 ⟶ M')
    (hπ : Function.Surjective π.hom)
    (hExact₀ : Function.Exact (δ 0).hom π.hom)
    (hExact : ∀ i : Fin e, Function.Exact (δ i.succ).hom (δ i.castSucc).hom)
    (htop : Projective (ModuleCat.of R (LinearMap.ker (δ (Fin.last e)).hom))) :
    HasFiniteProjectiveResolutionLengthLE M' (e + 2) := by
  induction e generalizing M' with
  | zero =>
      let κ : F 1 ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom <|
          LinearMap.codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hκ_surj : Function.Surjective κ.hom := by
        -- Exactness at `F₀` identifies `ker π` with the image of `δ₀`.
        intro x
        rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_ker : LinearMap.ker κ.hom = LinearMap.ker (δ 0).hom := by
        simpa [κ] using
          LinearMap.ker_codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hker : HasFiniteProjectiveResolutionLengthLE
          (ModuleCat.of R (LinearMap.ker π.hom)) 1 := by
        have htop' : Projective (ModuleCat.of R (LinearMap.ker κ.hom)) := by
          exact hκ_ker.symm ▸ htop
        have hker₀ : HasFiniteProjectiveResolutionLengthLE
            (ModuleCat.of R (LinearMap.ker κ.hom)) 0 := by
          simpa [hasFiniteProjectiveResolutionLengthLE_zero_iff] using htop'
        -- The first syzygy has a projective presentation with projective kernel `ker δ₀`.
        exact hasFiniteProjectiveResolutionLengthLE_succ_of_projective_presentation
          (M := ModuleCat.of R (LinearMap.ker π.hom)) κ (hF 1) hκ_surj hker₀
      -- Prepending `F₀ ⟶ M` gives a finite resolution of `M`.
      exact hasFiniteProjectiveResolutionLengthLE_succ_of_projective_presentation
        (M := M') π (hF 0) hπ hker
  | succ e ih =>
      let κ : F 1 ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom <|
          LinearMap.codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hκ_surj : Function.Surjective κ.hom := by
        -- Exactness at `F₀` again identifies the first syzygy with the image of `δ₀`.
        intro x
        rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_ker : LinearMap.ker κ.hom = LinearMap.ker (δ 0).hom := by
        simpa [κ] using
          LinearMap.ker_codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hκ_exact : Function.Exact (δ 1).hom κ.hom := by
        -- Restricting the codomain to `ker π` preserves exactness because the subtype map
        -- is injective.
        have hsub_inj : Function.Injective (LinearMap.ker π.hom).subtype :=
          Submodule.injective_subtype (LinearMap.ker π.hom)
        have hExact₁ :
            Function.Exact (δ 1).hom ((LinearMap.ker π.hom).subtype.comp κ.hom) := by
          simpa [κ] using hExact 0
        exact (Function.Injective.comp_exact_iff_exact
          (f := (δ 1).hom) (g := κ.hom) hsub_inj).1 hExact₁
      let F' : Fin (e + 2) → ModuleCat.{v} R := fun i ↦ F i.succ
      let δ' : (i : Fin (e + 1)) → F' i.succ ⟶ F' i.castSucc := fun i ↦ δ i.succ
      have hExact' : ∀ i : Fin e, Function.Exact (δ' i.succ).hom (δ' i.castSucc).hom := by
        intro i
        simpa [δ'] using hExact i.succ
      have hker : HasFiniteProjectiveResolutionLengthLE
          (ModuleCat.of R (LinearMap.ker π.hom)) (e + 2) := by
        -- After shifting to the first syzygy, the top kernel is unchanged.
        simpa [δ', Fin.succ_last] using
          ih (M' := ModuleCat.of R (LinearMap.ker π.hom))
            (F := F') (hF := fun i ↦ hF i.succ) (δ := δ') (π := κ)
            hκ_surj hκ_exact hExact' htop
      -- One more projective presentation step recovers a finite resolution of `M`.
      exact hasFiniteProjectiveResolutionLengthLE_succ_of_projective_presentation
        (M := M') π (hF 0) hπ hker

namespace CategoryTheory.ProjectiveResolution

/-- Helper for Lemma 10.109.4: once `M` has projective dimension at most `d`, every projective
resolution of `M` has projective `d`th syzygy. -/
theorem syzygyProjective_of_hasProjectiveDimensionLE (P : ProjectiveResolution M) {d : ℕ}
    (hpd : HasProjectiveDimensionLE M d) :
    P.SyzygyProjective d := by
  cases d with
  | zero =>
      -- In degree `0`, the syzygy condition is exactly projectivity of `M`.
      simpa [SyzygyProjective] using
        (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).2 hpd
  | succ d =>
      cases d with
      | zero =>
          have hπ : Function.Surjective (P.π.f 0).hom :=
            (ModuleCat.epi_iff_surjective _).mp inferInstance
          let _ : Module.Projective R (P.complex.X 0) :=
            module_projective_of_categorical_projective
              (R := R) (P := P.complex.X 0) (P.projective 0)
          -- The degree-one clause is the first-syzygy case of Lemma `10.109.3`.
          let _ : Module.Projective R (LinearMap.ker (P.π.f 0).hom) :=
            projective_ker_of_surjective_of_hasProjectiveDimensionLE_one
              (R := R) (M := M) (P.π.f 0).hom hπ hpd
          simpa [SyzygyProjective] using
            (show Projective (ModuleCat.of R (LinearMap.ker (P.π.f 0).hom)) from inferInstance)
      | succ n =>
          have hπ : Function.Surjective (P.π.f 0).hom :=
            (ModuleCat.epi_iff_surjective _).mp inferInstance
          -- Route correction: the higher-degree clause is proved on the shifted exact prefix,
          -- not by applying Lemma `10.109.3` directly at the original indexing.
          simpa [SyzygyProjective] using
            projective_top_kernel_of_shifted_exact_of_hasProjectiveDimensionLE
              (R := R) (M' := M) (F := fun i ↦ P.complex.X i)
              (hF := fun i ↦ P.projective i)
              (δ := fun i ↦ P.complex.d i.succ i.castSucc)
              (π := P.π.f 0) hπ
              (projectiveResolution_exact_zero_linearMap (R := R) P)
              (fun i ↦ by
                simpa using projectiveResolution_exact_succ_linearMap (R := R) P (i : ℕ))
              hpd

/-- Helper for Lemma 10.109.4: if a projective resolution has projective `d`th syzygy, then its
first `d + 1` terms already form a finite projective resolution of length at most `d`. -/
theorem hasFiniteProjectiveResolutionLengthLE_of_syzygyProjective (P : ProjectiveResolution M)
    {d : ℕ} (hP : P.SyzygyProjective d) :
    HasFiniteProjectiveResolutionLengthLE M d := by
  cases d with
  | zero =>
      -- In degree `0`, both predicates are the same projectivity condition.
      simpa [SyzygyProjective, HasFiniteProjectiveResolutionLengthLE] using hP
  | succ d =>
      cases d with
      | zero =>
          have hπ : Function.Surjective (P.π.f 0).hom :=
            (ModuleCat.epi_iff_surjective _).mp inferInstance
          -- The degree-one clause is the defining short exact sequence `0 → ker π → P₀ → M → 0`.
          exact hasFiniteProjectiveResolutionLengthLE_succ_of_projective_presentation
            (M := M) (P.π.f 0) (P.projective 0) hπ hP
      | succ n =>
          have hπ : Function.Surjective (P.π.f 0).hom :=
            (ModuleCat.epi_iff_surjective _).mp inferInstance
          -- Truncating at the projective top kernel gives the required finite resolution.
          exact hasFiniteProjectiveResolutionLengthLE_of_shifted_exact_of_projective_top_kernel
            (R := R) (M' := M) (F := fun i ↦ P.complex.X i)
            (hF := fun i ↦ P.projective i)
            (δ := fun i ↦ P.complex.d i.succ i.castSucc)
            (π := P.π.f 0) hπ
            (projectiveResolution_exact_zero_linearMap (R := R) P)
            (fun i ↦ by
              simpa using projectiveResolution_exact_succ_linearMap (R := R) P (i : ℕ))
            (by simpa [SyzygyProjective] using hP)

end CategoryTheory.ProjectiveResolution

/-- Lemma 10.109.4: the condition that `M` has projective dimension at most `d` is equivalent to
the existence of a finite projective resolution of length at most `d`, to the existence of some
projective resolution whose `d`th syzygy is projective, and to the assertion that every projective
resolution has projective `d`th syzygy. -/
-- Proof sketch: `(1) ↔ (2)` is the textbook definition of projective dimension. `(2) → (4)` is
-- the syzygy-projectivity criterion of Lemma `10.109.3`, `(4) → (3)` is immediate, and `(3) → (2)`
-- follows by truncating a projective resolution once the `d`th syzygy is projective.
theorem projectiveDimensionLE_tfae_resolution_conditions (d : ℕ) :
    List.TFAE
      [ HasProjectiveDimensionLE M d,
        HasFiniteProjectiveResolutionLengthLE M d,
        ∃ P : ProjectiveResolution M, P.SyzygyProjective d,
        ∀ P : ProjectiveResolution M, P.SyzygyProjective d ] := by
  -- The textbook cycle is `(1) → (4) → (3) → (2) → (1)`.
  tfae_have 1 → 4 := by
    intro hpd
    change ∀ Q : ProjectiveResolution M, Q.SyzygyProjective d
    intro Q
    exact CategoryTheory.ProjectiveResolution.syzygyProjective_of_hasProjectiveDimensionLE
      (R := R) (M := M) (P := Q) hpd
  tfae_have 4 → 3 := by
    intro h
    refine ⟨CategoryTheory.projectiveResolution M, h _⟩
  tfae_have 3 → 2 := by
    rintro ⟨Q, hQ⟩
    exact CategoryTheory.ProjectiveResolution.hasFiniteProjectiveResolutionLengthLE_of_syzygyProjective
      (R := R) (M := M) (P := Q) hQ
  tfae_have 2 → 1 := by
    intro h
    exact hasProjectiveDimensionLE_of_hasFiniteProjectiveResolutionLengthLE (M := M) h
  tfae_finish

end
