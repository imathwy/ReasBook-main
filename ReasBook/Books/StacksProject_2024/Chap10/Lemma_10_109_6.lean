import Mathlib
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

/-- Helper for Lemma 10.109.6: the object property selecting finite projective `R`-modules in
`ModuleCat R`. -/
abbrev finiteProjectiveModuleProperty (R : Type u) [CommRing R] :
    ObjectProperty (ModuleCat R) :=
  fun X ↦ Module.Finite R X ∧ Module.Projective R X

/-- Helper for Lemma 10.109.6: the full subcategory of finite projective `R`-modules. -/
abbrev FiniteProjectiveModuleCat (R : Type u) [CommRing R] :=
  (finiteProjectiveModuleProperty R).FullSubcategory

/-- Helper for Lemma 10.109.6: an object of the finite-projective full subcategory is finite. -/
instance (X : FiniteProjectiveModuleCat R) : Module.Finite R X.obj :=
  X.2.1

/-- Helper for Lemma 10.109.6: an object of the finite-projective full subcategory is projective. -/
instance (X : FiniteProjectiveModuleCat R) : Module.Projective R X.obj :=
  X.2.2

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
/-- Helper for Lemma 10.109.6: a bounded resolution by finite projective objects forgets to a
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

/-- Helper for Lemma 10.109.6: a finite projective `ModuleCat R` object determines an object of
`FiniteProjectiveModuleCat R`. -/
abbrev toFiniteProjective (X : ModuleCat.{u} R)
    [Module.Finite R X] [Module.Projective R X] :
    FiniteProjectiveModuleCat R :=
  ⟨X, ⟨inferInstance, inferInstance⟩⟩

/-- Helper for Lemma 10.109.6: a finite module with categorical projectivity defines an object of
`FiniteProjectiveModuleCat R`. -/
abbrev toFiniteProjectiveOfProjective (X : ModuleCat.{u} R)
    [Module.Finite R X] (hX : Projective X) :
    FiniteProjectiveModuleCat R :=
  let _ : Module.Projective R X := module_projective_of_categorical_projective (R := R) hX
  toFiniteProjective X

end ModuleCat

namespace CategoryTheory.ProjectiveResolution

section

variable {M : ModuleCat.{u} R}

/-- Helper for Lemma 10.109.6: if a projective resolution has finite terms and projective `d`th
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
          let _ : Module.Finite R K := hK_finite
          let _ : Module.Projective R K := hK_projective
          let P' : Fin (e + 3) → FiniteProjectiveModuleCat R :=
            Fin.snoc
              (fun i : Fin (e + 2) ↦
                let _ : Module.Finite R (P.complex.X i) := hfinite i
                ModuleCat.toFiniteProjectiveOfProjective (P.complex.X i) (P.projective i))
              (ModuleCat.toFiniteProjective K)
          have hP_castSucc_succ :
              ∀ i : Fin (e + 1), (P' i.castSucc.succ).obj = P.complex.X i.succ := by
            intro i
            -- The nonterminal source terms of the truncation are the original resolution terms.
            simp only [P', Fin.succ_castSucc, Fin.snoc_castSucc]
          have hP_castSucc_castSucc :
              ∀ i : Fin (e + 1), (P' i.castSucc.castSucc).obj = P.complex.X i.castSucc := by
            intro i
            -- The nonterminal target terms are unchanged as well.
            simp only [P', Fin.snoc_castSucc]
          have hP_last_succ : (P' (Fin.last (e + 1)).succ).obj = K := by
            -- The last source object is the adjoined kernel term.
            simp only [P', Fin.succ_last, Fin.snoc_last]
          have hP_last_castSucc :
              (P' (Fin.last (e + 1)).castSucc).obj = P.complex.X (e + 1) := by
            -- The last target object is the former top term of the resolution.
            simp only [P', Fin.snoc_castSucc, Fin.val_last]
          let κBase : (P' (Fin.last (e + 1)).succ).obj ⟶ (P' (Fin.last (e + 1)).castSucc).obj :=
            eqToHom hP_last_succ ≫
              ModuleCat.ofHom (LinearMap.ker (P.complex.d (e + 1) e).hom).subtype ≫
                eqToHom hP_last_castSucc.symm
          let κ : P' (Fin.last (e + 1)).succ ⟶ P' (Fin.last (e + 1)).castSucc :=
            ObjectProperty.homMk κBase
          let δBase :
              ∀ i : Fin (e + 1), (P' i.castSucc.succ).obj ⟶ (P' i.castSucc.castSucc).obj :=
            fun i ↦
              eqToHom (hP_castSucc_succ i) ≫
                P.complex.d i.succ i.castSucc ≫
                  eqToHom (hP_castSucc_castSucc i).symm
          let δ' : (i : Fin (e + 2)) → P' i.succ ⟶ P' i.castSucc :=
            Fin.lastCases κ
              (fun i : Fin (e + 1) ↦ ObjectProperty.homMk (δBase i))
          -- Route correction: we keep the source truncation by the top syzygy kernel, but first
          -- normalize the `FiniteProjectiveModuleCat` differentials back to the underlying maps.
          -- TODO: prove the two transport lemmas
          -- `eqToHom (hP_castSucc_succ i).symm ≫ (δ' i.castSucc).hom ≫
          --    eqToHom (hP_castSucc_castSucc i) = P.complex.d i.succ i.castSucc`
          -- and
          -- `eqToHom hP_last_succ.symm ≫ (δ' (Fin.last (e + 1))).hom ≫
          --    eqToHom hP_last_castSucc =
          --      ModuleCat.ofHom (LinearMap.ker (P.complex.d (e + 1) e).hom).subtype`,
          -- then transport exactness and injectivity across those `eqToHom` isomorphisms.
          sorry

end

end CategoryTheory.ProjectiveResolution

section

variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: a finite free resolution gives a projective resolution whose terms are finite;
-- Lemma `10.109.4` then makes the `d`th syzygy projective, and the preceding helper truncates
-- the finite free resolution at that projective syzygy.
/-- Helper for Lemma 10.109.6: a projective-dimension bound yields a bounded resolution by finite
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
/-- Lemma 10.109.6: for a finite module `M` over a Noetherian ring `R`, having projective
dimension at most `d` is equivalent to admitting a resolution
`0 ⟶ P_d ⟶ P_{d-1} ⟶ ⋯ ⟶ P₀ ⟶ M ⟶ 0`
in which every `Pᵢ` is a finite projective `R`-module. -/
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
