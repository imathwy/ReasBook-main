import Mathlib
import StacksProject_2024.Chap10.Definition_10_72_1
import StacksProject_2024.Chap10.Definition_10_109_10
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_72_5
import StacksProject_2024.Chap10.Lemma_10_104_9
import StacksProject_2024.Chap10.Lemma_10_106_3
import StacksProject_2024.Chap10.Lemma_10_106_6
import StacksProject_2024.Chap10.Lemma_10_107_14
import StacksProject_2024.Chap10.Lemma_10_109_6
import StacksProject_2024.Chap10.Lemma_10_109_7
import StacksProject_2024.Chap10.Lemma_10_109_12
import StacksProject_2024.Chap10.Proposition_10_110_1.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory ChainComplex
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {M : Type (max u v)} [AddCommGroup M] [Module R M] [Module.Finite R M]

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

omit [IsRegularLocalRing R] [Module.Finite R M] in
/-- Helper for Proposition 10.110.1: a bounded finite free resolution transports across an
`R`-linear equivalence of modules by postcomposing the augmentation with the induced isomorphism of
single-term complexes. -/
lemma hasFiniteFreeResolutionLengthLE_of_linearEquiv
    {N : Type (max u v)} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (e : M ≃ₗ[R] N) {n : ℕ} :
    HasFiniteFreeResolutionLengthLE R M n →
      HasFiniteFreeResolutionLengthLE R N n := by
  intro hres
  rcases hres with ⟨F, π, hπ, hbound⟩
  let eSingle :
      CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M) ≅
        CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R N) :=
    (ChainComplex.single₀ (ModuleCat R)).mapIso e.toModuleIso
  let π' : F ⟶ moduleSingle[R] N := π ≫ eSingle.hom
  have hπ' : ChainComplex.IsFiniteFreeResolution π' := by
    let hfree : ChainComplex.IsFreeResolution π := hπ.toIsFreeResolution
    letI : QuasiIso π := hfree.toQuasiIso
    have hquasi : QuasiIso π' := by
      change QuasiIso (π ≫ eSingle.hom)
      infer_instance
    -- The chain complex is unchanged, so termwise freeness and finiteness are inherited.
    exact
      { toIsFreeResolution :=
          { toQuasiIso := hquasi
            termwise_free := hfree.termwise_free }
        termwise_finite := hπ.termwise_finite }
  exact ⟨F, π', hπ', hbound⟩

/-- Helper for Proposition 10.110.1: any bounded finite free resolution already shows that the
target module is finitely generated, even in mixed universes. -/
lemma module_finite_of_hasFiniteFreeResolutionLengthLE_mixed_universe
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}
    (hres : HasFiniteFreeResolutionLengthLE R M n) :
    Module.Finite R M := by
  rcases hres with ⟨F, π, hπ, _hbound⟩
  have hπ_surj : Function.Surjective (π.f 0).hom := by
    -- The augmentation of a finite free resolution is surjective in degree `0`.
    exact (ModuleCat.epi_iff_surjective _).mp
      (quasiIso_single_epi_zero (R := R) (N := M) (G := F) π)
  let _ : Module.Finite R (F.X 0) := ChainComplex.IsFiniteFreeResolution.finite π 0
  -- Finite generation descends along the degree-`0` surjection.
  exact Module.Finite.of_surjective (π.f 0).hom hπ_surj

/-- Helper for Proposition 10.110.1: a length-zero finite free resolution identifies `M` with the
finite free degree-zero term even when the module universe differs from the ring universe. -/
lemma hasFiniteFreeResolutionLengthLE_zero_iff_mixed_universe
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] :
    HasFiniteFreeResolutionLengthLE R M 0 ↔ Module.Free R M ∧ Module.Finite R M := by
  constructor
  · intro hres
    rcases hres with ⟨F, π, hπ, hF⟩
    have hπ_surj : Function.Surjective (π.f 0).hom := by
      -- The augmentation of a finite free resolution is surjective in degree `0`.
      exact (ModuleCat.epi_iff_surjective _).mp
        (quasiIso_single_epi_zero (R := R) (N := M) (G := F) π)
    have hπ_comm : F.d 1 0 ≫ π.f 0 = 0 := by
      -- The augmented complex relation records `π₀ ∘ d₁₀ = 0`.
      simpa using (π.comm 1 0).symm
    let S₀ : ShortComplex (ModuleCat R) :=
      ShortComplex.mk (F.d 1 0) (π.f 0) hπ_comm
    have hS₀_exact : S₀.Exact := by
      -- Exactness at degree `0` comes from the quasi-isomorphism to `single₀`.
      simpa [S₀] using quasiIso_single_exact_zero (R := R) (N := M) (G := F) π
    have hExact₀ : Function.Exact (F.d 1 0).hom (π.f 0).hom := by
      -- We switch to the linear-map exactness statement to read off the kernel of `π₀`.
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₀).1 hS₀_exact
    have hX₁_zero : Limits.IsZero (F.X 1) := hF 1 (by simpa using Nat.zero_lt_one)
    have hd₁₀_zero : (F.d 1 0).hom = 0 := by
      -- Degree `1` vanishes, so the first differential is the zero map.
      ext x
      have hsub : Subsingleton (F.X 1) :=
        (ModuleCat.isZero_iff_subsingleton (M := F.X 1)).1 hX₁_zero
      have hx : x = 0 := Subsingleton.elim _ _
      simpa [hx]
    have hπ_inj : Function.Injective (π.f 0).hom := by
      -- Exactness identifies `ker π₀` with the image of the zero differential.
      have hker_bot : LinearMap.ker (π.f 0).hom = ⊥ := by
        rw [hExact₀.linearMap_ker_eq, hd₁₀_zero, LinearMap.range_zero]
      exact LinearMap.ker_eq_bot.mp hker_bot
    let e₀ : F.X 0 ≃ₗ[R] M :=
      LinearEquiv.ofBijective (π.f 0).hom ⟨hπ_inj, hπ_surj⟩
    let _ : Module.Free R (F.X 0) := ChainComplex.IsFreeResolution.free (R := R) (M := M) π 0
    let _ : Module.Finite R (F.X 0) := ChainComplex.IsFiniteFreeResolution.finite π 0
    -- Transport finite freeness from the degree-`0` term along the augmentation isomorphism.
    exact ⟨Module.Free.of_equiv e₀, Module.Finite.equiv e₀⟩
  · rintro ⟨hfree, hfinite⟩
    let F : ChainComplex (ModuleCat R) ℕ :=
      CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)
    let π : F ⟶ moduleSingle[R] M := 𝟙 F
    have hfree_terms : ChainComplex.IsTermwiseFree F := by
      intro n
      cases n with
      | zero =>
          -- Degree `0` is exactly `M`.
          simpa [F] using hfree
      | succ n =>
          -- Positive degrees of `single₀` are zero modules, hence free.
          have hzero : Limits.IsZero (F.X (n + 1)) := by
            simpa [F] using
              HomologicalComplex.isZero_single_obj_X
                (V := ModuleCat R) (c := ComplexShape.down ℕ) 0 (ModuleCat.of R M) (n + 1)
                (Nat.succ_ne_zero n)
          have hsub : Subsingleton (F.X (n + 1)) :=
            (ModuleCat.isZero_iff_subsingleton (M := F.X (n + 1))).1 hzero
          let _ : Subsingleton (F.X (n + 1)) := hsub
          exact Module.Free.of_subsingleton R (F.X (n + 1))
    have hfinite_terms : ChainComplex.IsTermwiseFinite F := by
      intro n
      cases n with
      | zero =>
          -- Degree `0` is exactly `M`.
          simpa [F] using hfinite
      | succ n =>
          -- Positive degrees of `single₀` are zero modules, hence finite.
          have hzero : Limits.IsZero (F.X (n + 1)) := by
            simpa [F] using
              HomologicalComplex.isZero_single_obj_X
                (V := ModuleCat R) (c := ComplexShape.down ℕ) 0 (ModuleCat.of R M) (n + 1)
                (Nat.succ_ne_zero n)
          have hsub : Subsingleton (F.X (n + 1)) :=
            (ModuleCat.isZero_iff_subsingleton (M := F.X (n + 1))).1 hzero
          let _ : Subsingleton (F.X (n + 1)) := hsub
          let _ : Module.Free R (F.X (n + 1)) := Module.Free.of_subsingleton R (F.X (n + 1))
          exact Module.Finite.of_basis (Module.Free.chooseBasis R (F.X (n + 1)))
    have hπ : ChainComplex.IsFiniteFreeResolution π := by
      -- The identity augmentation on `single₀ M` is a finite free resolution.
      exact
        { toIsFreeResolution :=
            { toQuasiIso := by infer_instance
              termwise_free := hfree_terms }
          termwise_finite := hfinite_terms }
    refine ⟨F, π, hπ, ?_⟩
    intro n hn
    -- Every positive degree of `single₀ M` vanishes, so the length bound is immediate.
    cases n with
    | zero =>
        exact (Nat.not_lt_zero _ hn).elim
    | succ n =>
        simpa [F] using
          HomologicalComplex.isZero_single_obj_X
            (V := ModuleCat R) (c := ComplexShape.down ℕ) 0 (ModuleCat.of R M) (n + 1)
            (Nat.succ_ne_zero n)

/-- Helper for Proposition 10.110.1: a bounded finite free tail can be extended by one finite free
presentation step even when the presentation term and target module live in different universes. -/
lemma hasFiniteFreeResolutionLengthLE_succ_of_finite_free_presentation_mixed_universe
    {R : Type u} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]
    {d : ℕ} {P₀ : ModuleCat.{w} R} (π₀ : P₀ ⟶ ModuleCat.of R M)
    (hπ₀ : Function.Surjective π₀.hom) (hP₀ : Module.Free R P₀) (hP₀finite : Module.Finite R P₀)
    (hK : HasFiniteFreeResolutionLengthLE R (LinearMap.ker π₀.hom) d) :
    HasFiniteFreeResolutionLengthLE R M (d + 1) := by
  rcases hK with ⟨F, π, hπ, hF⟩
  have hπ_surj : Function.Surjective (π.f 0).hom := by
    -- The augmentation of the kernel resolution is surjective in degree `0`.
    exact (ModuleCat.epi_iff_surjective _).mp
      (quasiIso_single_epi_zero (R := R) (N := LinearMap.ker π₀.hom) (G := F) π)
  have hπ_comm : F.d 1 0 ≫ π.f 0 = 0 := by
    -- The kernel resolution is an augmented chain complex.
    simpa using (π.comm 1 0).symm
  let Sπ : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (F.d 1 0) (π.f 0) hπ_comm
  have hSπ_exact : Sπ.Exact := by
    -- Exactness at degree `0` comes from quasi-isomorphism to `single₀`.
    simpa [Sπ] using
      quasiIso_single_exact_zero (R := R) (N := LinearMap.ker π₀.hom) (G := F) π
  have hExact₀ : Function.Exact (F.d 1 0).hom (π.f 0).hom := by
    -- We convert the categorical exactness statement to the linear-map API used below.
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Sπ).1 hSπ_exact
  let X : ℕ → ModuleCat R
    | 0 => P₀
    | n + 1 => F.X n
  let δ : ∀ n : ℕ, X (n + 1) ⟶ X n
    | 0 => π.f 0 ≫ ModuleCat.ofHom (LinearMap.ker π₀.hom).subtype
    | n + 1 => F.d (n + 1) n
  have hδ_sq : ∀ n : ℕ, δ (n + 1) ≫ δ n = 0 := by
    intro n
    cases n with
    | zero =>
        -- The first shifted differential lands in `ker π₀`, so the new `1 → 0` window is a
        -- chain-complex relation.
        apply ModuleCat.hom_ext
        ext x
        exact congrArg Subtype.val <|
          LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hπ_comm) x
    | succ n =>
        -- Farther left, the differentials are inherited verbatim from `F`.
        simpa [δ] using F.d_comp_d (n + 2) (n + 1) n
  let G : ChainComplex (ModuleCat R) ℕ := ChainComplex.of X δ hδ_sq
  have hδ₀_aug : δ 0 ≫ π₀ = 0 := by
    -- The augmentation factors through the kernel subtype by construction.
    apply ModuleCat.hom_ext
    ext x
    simp [δ]
  let ν :
      G ⟶ CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M) :=
    (ChainComplex.toSingle₀Equiv G (ModuleCat.of R M)).symm ⟨π₀, hδ₀_aug⟩
  have hGfree : ChainComplex.IsTermwiseFree G := by
    intro n
    cases n with
    | zero =>
        -- Degree `0` is the chosen finite free presentation term.
        simpa [G, X] using hP₀
    | succ n =>
        -- Every positive degree is inherited from the kernel's finite free resolution.
        simpa [G, X] using
          (ChainComplex.IsFreeResolution.free (R := R) (M := LinearMap.ker π₀.hom) π n)
  have hGfinite : ChainComplex.IsTermwiseFinite G := by
    intro n
    cases n with
    | zero =>
        -- Degree `0` is finite by hypothesis on the chosen presentation.
        simpa [G, X] using hP₀finite
    | succ n =>
        -- Every positive degree is inherited from the kernel's finite free resolution.
        simpa [G, X] using (ChainComplex.IsFiniteFreeResolution.finite π n)
  have hν_quasi : QuasiIso ν := by
    refine ⟨fun n ↦ ?_⟩
    cases n with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
        · -- Degree `0` is exactly `F₀ → ker π₀ → P₀ → M`.
          refine ⟨?_, ?_⟩
          · have hExact_presentation :
                Function.Exact
                  ((LinearMap.ker π₀.hom).subtype.comp (π.f 0).hom) π₀.hom := by
                exact (Function.Surjective.comp_exact_iff_exact
                  (f := (LinearMap.ker π₀.hom).subtype) (g := π₀.hom) hπ_surj).2
                  (LinearMap.exact_subtype_ker_map π₀.hom)
            exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
              hExact_presentation
          · exact (ModuleCat.epi_iff_surjective _).2 hπ₀
        · rfl
        · rfl
        · rfl
    | succ n =>
        rw [quasiIsoAt_iff_exactAt']
        · cases n with
          | zero =>
              have hδ₁_exact :
                  Function.Exact (δ 1).hom (δ 0).hom := by
                -- Postcomposing with the kernel subtype preserves degree-`1` exactness.
                have hsub_inj : Function.Injective (LinearMap.ker π₀.hom).subtype :=
                  Submodule.injective_subtype (LinearMap.ker π₀.hom)
                exact (Function.Injective.comp_exact_iff_exact
                  (f := (F.d 1 0).hom) (g := (π.f 0).hom) hsub_inj).2 hExact₀
              rw [HomologicalComplex.exactAt_iff' G 2 1 0 (by simp) (by simp)]
              exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hδ₁_exact
          | succ n =>
              -- Every higher exactness statement is the corresponding exactness of `F`.
              rw [HomologicalComplex.exactAt_iff' G (n + 3) (n + 2) (n + 1)
                (by simp) (by simp)]
              have hF_comm :
                  F.d (n + 2) (n + 1) ≫ F.d (n + 1) n = 0 := by
                simpa [Nat.add_assoc] using F.d_comp_d (n + 2) (n + 1) n
              let SF : ShortComplex (ModuleCat R) :=
                ShortComplex.mk (F.d (n + 2) (n + 1)) (F.d (n + 1) n) hF_comm
              have hSF_exact : SF.Exact := by
                simpa [SF, Nat.add_assoc] using
                  quasiIso_single_exact_succ (R := R) (N := LinearMap.ker π₀.hom) (G := F) π n
              have hF_exact :
                  Function.Exact (F.d (n + 2) (n + 1)).hom (F.d (n + 1) n).hom := by
                exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact SF).1 hSF_exact
              have hG_exact :
                  Function.Exact (G.d (n + 3) (n + 2)).hom (G.d (n + 2) (n + 1)).hom := by
                have hGd_left : G.d (n + 3) (n + 2) = F.d (n + 2) (n + 1) := by
                  simp [G, ChainComplex.of, δ, Nat.add_assoc]
                have hGd_right : G.d (n + 2) (n + 1) = F.d (n + 1) n := by
                  simp [G, ChainComplex.of, δ, Nat.add_assoc]
                rw [hGd_left, hGd_right]
                exact hF_exact
              exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hG_exact
        · apply ChainComplex.exactAt_succ_single_obj
  refine ⟨G, ν, ?_, ?_⟩
  · -- The prepended complex is finite free because it is quasi-isomorphic to `single₀ M`,
    -- termwise free, and termwise finite.
    exact
      { toIsFreeResolution := { toQuasiIso := hν_quasi, termwise_free := hGfree }
        termwise_finite := hGfinite }
  · intro n hn
    cases n with
    | zero =>
        exact (Nat.not_lt_zero _ hn).elim
    | succ n =>
        -- Vanishing above degree `d + 1` is inherited from the kernel resolution after shifting.
        simpa [G, X] using hF n (Nat.lt_of_succ_lt_succ hn)

/-- Helper for Proposition 10.110.1: the tail of a bounded finite free resolution is a bounded
finite free resolution of the first syzygy even when the module universe differs from the ring
universe. -/
lemma hasFiniteFreeResolutionLengthLE_kernel_of_witness_succ_mixed_universe
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {d : ℕ} {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ moduleSingle[R]M) (hπ : ChainComplex.IsFiniteFreeResolution π)
    (hF : ∀ n : ℕ, d + 1 < n → Limits.IsZero (F.X n)) :
    HasFiniteFreeResolutionLengthLE R (LinearMap.ker (π.f 0).hom) d := by
  have hπ_comm : F.d 1 0 ≫ π.f 0 = 0 := by
    -- The original augmentation kills the first differential.
    simpa using (π.comm 1 0).symm
  let S₀ : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (F.d 1 0) (π.f 0) hπ_comm
  have hS₀_exact : S₀.Exact := by
    -- Degree `0` exactness of the original finite free resolution.
    simpa [S₀] using quasiIso_single_exact_zero (R := R) (N := M) (G := F) π
  have hExact₀ : Function.Exact (F.d 1 0).hom (π.f 0).hom := by
    -- Translate the categorical short-complex exactness into the linear-map statement.
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₀).1 hS₀_exact
  have hF_comm₁ : F.d 2 1 ≫ F.d 1 0 = 0 := by
    -- The next differential also composes to zero.
    simpa using F.d_comp_d 2 1 0
  let S₁ : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (F.d 2 1) (F.d 1 0) hF_comm₁
  have hS₁_exact : S₁.Exact := by
    -- Degree `1` exactness of the original finite free resolution.
    simpa [S₁] using quasiIso_single_exact_succ (R := R) (N := M) (G := F) π 0
  have hExact₁ : Function.Exact (F.d 2 1).hom (F.d 1 0).hom := by
    -- Again we move to the linear-map API used for `codRestrict`.
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₁).1 hS₁_exact
  have hκ_mem : ∀ x, (F.d 1 0).hom x ∈ LinearMap.ker (π.f 0).hom := by
    intro x
    -- Exactness means `π₀ ∘ d₁₀ = 0`, so every image point lies in the kernel.
    simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
      LinearMap.congr_fun hExact₀.linearMap_comp_eq_zero x
  let X : ℕ → ModuleCat R := fun n ↦ F.X (n + 1)
  let δ : ∀ n : ℕ, X (n + 1) ⟶ X n := fun n ↦ F.d (n + 2) (n + 1)
  have hδ_sq : ∀ n : ℕ, δ (n + 1) ≫ δ n = 0 := by
    intro n
    -- The shifted tail is still a chain complex because `F` already is one.
    simpa [δ, Nat.add_assoc] using F.d_comp_d (n + 3) (n + 2) (n + 1)
  let G : ChainComplex (ModuleCat R) ℕ := ChainComplex.of X δ hδ_sq
  let κ : G.X 0 ⟶ ModuleCat.of R (LinearMap.ker (π.f 0).hom) :=
    ModuleCat.ofHom (LinearMap.codRestrict (LinearMap.ker (π.f 0).hom) (F.d 1 0).hom hκ_mem)
  have hκ_zero : δ 0 ≫ κ = 0 := by
    -- Restricting the codomain does not change the underlying composition `d₂₁ ≫ d₁₀ = 0`.
    apply ModuleCat.hom_ext
    ext x
    change (F.d 1 0).hom ((F.d 2 1).hom x) = 0
    exact LinearMap.congr_fun hExact₁.linearMap_comp_eq_zero x
  let κAug : G ⟶ moduleSingle[R] (LinearMap.ker (π.f 0).hom) :=
    (ChainComplex.toSingle₀Equiv G (ModuleCat.of R (LinearMap.ker (π.f 0).hom))).symm
      ⟨κ, hκ_zero⟩
  have hGfree : ChainComplex.IsTermwiseFree G := by
    intro n
    -- Every shifted term is a positive-degree term of the original finite free resolution.
    simpa [G, X] using (ChainComplex.IsFreeResolution.free (R := R) (M := M) π (n + 1))
  have hGfinite : ChainComplex.IsTermwiseFinite G := by
    intro n
    -- Every shifted term is a positive-degree finite term of the original finite free resolution.
    simpa [G, X] using (ChainComplex.IsFiniteFreeResolution.finite π (n + 1))
  have hκ_surj : Function.Surjective κ.hom := by
    -- Exactness at `F₀` identifies the first syzygy with the image of `d₁₀`.
    intro x
    rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
    refine ⟨y, Subtype.ext ?_⟩
    exact hy
  have hκ_exact : Function.Exact (δ 0).hom κ.hom := by
    -- Exactness at `F₁` survives after restricting the codomain of `d₁₀`.
    let κlin : F.X 1 →ₗ[R] LinearMap.ker (π.f 0).hom :=
      LinearMap.codRestrict (LinearMap.ker (π.f 0).hom) (F.d 1 0).hom hκ_mem
    have hsub_inj : Function.Injective (LinearMap.ker (π.f 0).hom).subtype :=
      Submodule.injective_subtype (LinearMap.ker (π.f 0).hom)
    have hcomp :
        Function.Exact (F.d 2 1).hom ((LinearMap.ker (π.f 0).hom).subtype.comp κlin) := by
      simpa [κlin] using hExact₁
    exact (Function.Injective.comp_exact_iff_exact
      (f := (F.d 2 1).hom) (g := κlin) hsub_inj).1 <| by
        simpa [δ, κ, κlin] using hcomp
  have hκAug_quasi : QuasiIso κAug := by
    refine ⟨fun n ↦ ?_⟩
    cases n with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
        · -- Degree `0` is exactly `F₂ → F₁ → ker(π₀)`.
          refine ⟨?_, ?_⟩
          · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hκ_exact
          · exact (ModuleCat.epi_iff_surjective _).2 hκ_surj
        · rfl
        · rfl
        · rfl
    | succ n =>
        rw [quasiIsoAt_iff_exactAt']
        · rw [HomologicalComplex.exactAt_iff' G (n + 2) (n + 1) n (by simp) (by simp)]
          -- Every positive-degree exactness statement is inherited from the original resolution.
          have hF_comm :
              F.d (n + 3) (n + 2) ≫ F.d (n + 2) (n + 1) = 0 := by
            simpa [Nat.add_assoc] using F.d_comp_d (n + 3) (n + 2) (n + 1)
          let SF : ShortComplex (ModuleCat R) :=
            ShortComplex.mk (F.d (n + 3) (n + 2)) (F.d (n + 2) (n + 1)) hF_comm
          have hSF_exact : SF.Exact := by
            simpa [SF, Nat.add_assoc] using
              quasiIso_single_exact_succ (R := R) (N := M) (G := F) π (n + 1)
          have hF_exact :
              Function.Exact (F.d (n + 3) (n + 2)).hom (F.d (n + 2) (n + 1)).hom := by
            exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact SF).1 hSF_exact
          have hG_exact :
              Function.Exact (G.d (n + 2) (n + 1)).hom (G.d (n + 1) n).hom := by
            have hGd_left : G.d (n + 2) (n + 1) = F.d (n + 3) (n + 2) := by
              simp [G, ChainComplex.of, δ]
            have hGd_right : G.d (n + 1) n = F.d (n + 2) (n + 1) := by
              simp [G, ChainComplex.of, δ]
            rw [hGd_left, hGd_right]
            exact hF_exact
          exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hG_exact
        · apply ChainComplex.exactAt_succ_single_obj
  refine ⟨G, κAug, ?_, ?_⟩
  · -- The shifted tail remains a finite free resolution of the first syzygy.
    exact
      { toIsFreeResolution := { toQuasiIso := hκAug_quasi, termwise_free := hGfree }
        termwise_finite := hGfinite }
  · intro n hn
    -- Vanishing one degree higher in `F` becomes the desired bound after shifting.
    simpa [G, X] using hF (n + 1) (Nat.succ_lt_succ hn)

section MixedUniverseBridge

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

omit [IsLocalRing R] in
/-- Helper for Proposition 10.110.1: forgetting termwise finiteness from a bounded finite free
resolution leaves a bounded free resolution in the original module universe. -/
lemma hasFreeResolutionLengthLE_of_hasFiniteFreeResolutionLengthLE_mixed_universe
    {n : ℕ} (hres : HasFiniteFreeResolutionLengthLE R M n) :
    HasFreeResolutionLengthLE R M n := by
  rcases hres with ⟨F, π, hπ, hbound⟩
  -- The source-facing owner already contains the same bounded complex with finiteness forgotten.
  exact ⟨F, π, hπ.toIsFreeResolution, hbound⟩

omit [IsLocalRing R] in
/-- Helper for Proposition 10.110.1: the tail of a bounded free resolution is a bounded free
resolution of the first syzygy, with no same-universe restriction on `M`. -/
lemma hasFreeResolutionLengthLE_kernel_of_witness_succ_mixed_universe
    {d : ℕ} {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ moduleSingle[R]M) (hπ : ChainComplex.IsFreeResolution π)
    (hF : ∀ n : ℕ, d + 1 < n → Limits.IsZero (F.X n)) :
    HasFreeResolutionLengthLE R (LinearMap.ker (π.f 0).hom) d := by
  have hπ_comm : F.d 1 0 ≫ π.f 0 = 0 := by
    -- The original augmentation kills the first differential.
    simpa using (π.comm 1 0).symm
  let S₀ : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (F.d 1 0) (π.f 0) hπ_comm
  have hS₀_exact : S₀.Exact := by
    -- Exactness at degree `0` comes from the quasi-isomorphism to `single₀`.
    simpa [S₀] using quasiIso_single_exact_zero (R := R) (N := M) (G := F) π
  have hExact₀ : Function.Exact (F.d 1 0).hom (π.f 0).hom := by
    -- We switch to the linear-map API needed for the codomain restriction.
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₀).1 hS₀_exact
  have hF_comm₁ : F.d 2 1 ≫ F.d 1 0 = 0 := by
    -- The next differential also composes to zero.
    simpa using F.d_comp_d 2 1 0
  let S₁ : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (F.d 2 1) (F.d 1 0) hF_comm₁
  have hS₁_exact : S₁.Exact := by
    -- Degree `1` exactness is inherited from the same quasi-isomorphism.
    simpa [S₁] using quasiIso_single_exact_succ (R := R) (N := M) (G := F) π 0
  have hExact₁ : Function.Exact (F.d 2 1).hom (F.d 1 0).hom := by
    -- Again we move to linear maps before restricting codomains.
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₁).1 hS₁_exact
  have hκ_mem : ∀ x, (F.d 1 0).hom x ∈ LinearMap.ker (π.f 0).hom := by
    intro x
    -- Exactness means `π₀ ∘ d₁₀ = 0`, so every image point lies in the kernel.
    simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
      LinearMap.congr_fun hExact₀.linearMap_comp_eq_zero x
  let X : ℕ → ModuleCat R := fun n ↦ F.X (n + 1)
  let δ : ∀ n : ℕ, X (n + 1) ⟶ X n := fun n ↦ F.d (n + 2) (n + 1)
  have hδ_sq : ∀ n : ℕ, δ (n + 1) ≫ δ n = 0 := by
    intro n
    -- The shifted tail is still a chain complex because `F` already is one.
    simpa [δ, Nat.add_assoc] using F.d_comp_d (n + 3) (n + 2) (n + 1)
  let G : ChainComplex (ModuleCat R) ℕ := ChainComplex.of X δ hδ_sq
  let κ : G.X 0 ⟶ ModuleCat.of R (LinearMap.ker (π.f 0).hom) :=
    ModuleCat.ofHom (LinearMap.codRestrict (LinearMap.ker (π.f 0).hom) (F.d 1 0).hom hκ_mem)
  have hκ_zero : δ 0 ≫ κ = 0 := by
    -- Restricting the codomain does not change the underlying composition `d₂₁ ≫ d₁₀ = 0`.
    apply ModuleCat.hom_ext
    ext x
    change (F.d 1 0).hom ((F.d 2 1).hom x) = 0
    exact LinearMap.congr_fun hExact₁.linearMap_comp_eq_zero x
  let κAug : G ⟶ moduleSingle[R] (LinearMap.ker (π.f 0).hom) :=
    (ChainComplex.toSingle₀Equiv G (ModuleCat.of R (LinearMap.ker (π.f 0).hom))).symm
      ⟨κ, hκ_zero⟩
  have hGfree : ChainComplex.IsTermwiseFree G := by
    intro n
    -- Every shifted term is a positive-degree term of the original free resolution.
    simpa [G, X] using (ChainComplex.IsFreeResolution.free (R := R) (M := M) π (n + 1))
  have hκ_surj : Function.Surjective κ.hom := by
    -- Exactness at `F₀` identifies the first syzygy with the image of `d₁₀`.
    intro x
    rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
    refine ⟨y, Subtype.ext ?_⟩
    exact hy
  have hκ_exact : Function.Exact (δ 0).hom κ.hom := by
    -- Exactness at `F₁` survives after restricting the codomain of `d₁₀`.
    let κlin : F.X 1 →ₗ[R] LinearMap.ker (π.f 0).hom :=
      LinearMap.codRestrict (LinearMap.ker (π.f 0).hom) (F.d 1 0).hom hκ_mem
    have hsub_inj : Function.Injective (LinearMap.ker (π.f 0).hom).subtype :=
      Submodule.injective_subtype (LinearMap.ker (π.f 0).hom)
    have hcomp :
        Function.Exact (F.d 2 1).hom ((LinearMap.ker (π.f 0).hom).subtype.comp κlin) := by
      simpa [κlin] using hExact₁
    exact (Function.Injective.comp_exact_iff_exact
      (f := (F.d 2 1).hom) (g := κlin) hsub_inj).1 <| by
        simpa [δ, κ, κlin] using hcomp
  have hκAug_quasi : QuasiIso κAug := by
    refine ⟨fun n ↦ ?_⟩
    cases n with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
        · -- The degree-`0` short complex is exactly `F₂ → F₁ → ker(π₀)`.
          refine ⟨?_, ?_⟩
          · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hκ_exact
          · exact (ModuleCat.epi_iff_surjective _).2 hκ_surj
        · rfl
        · rfl
        · rfl
    | succ n =>
        rw [quasiIsoAt_iff_exactAt']
        · rw [HomologicalComplex.exactAt_iff' G (n + 2) (n + 1) n (by simp) (by simp)]
          -- Every positive-degree exactness statement is inherited from the original resolution.
          have hF_comm :
              F.d (n + 3) (n + 2) ≫ F.d (n + 2) (n + 1) = 0 := by
            simpa [Nat.add_assoc] using F.d_comp_d (n + 3) (n + 2) (n + 1)
          let SF : ShortComplex (ModuleCat R) :=
            ShortComplex.mk (F.d (n + 3) (n + 2)) (F.d (n + 2) (n + 1)) hF_comm
          have hSF_exact : SF.Exact := by
            simpa [SF, Nat.add_assoc] using
              quasiIso_single_exact_succ (R := R) (N := M) (G := F) π (n + 1)
          have hF_exact :
              Function.Exact (F.d (n + 3) (n + 2)).hom (F.d (n + 2) (n + 1)).hom := by
            exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact SF).1 hSF_exact
          have hG_exact :
              Function.Exact (G.d (n + 2) (n + 1)).hom (G.d (n + 1) n).hom := by
            have hGd_left : G.d (n + 2) (n + 1) = F.d (n + 3) (n + 2) := by
              simp [G, ChainComplex.of, δ]
            have hGd_right : G.d (n + 1) n = F.d (n + 2) (n + 1) := by
              simp [G, ChainComplex.of, δ]
            rw [hGd_left, hGd_right]
            exact hF_exact
          exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hG_exact
        · apply ChainComplex.exactAt_succ_single_obj
  refine ⟨G, κAug, ?_⟩
  refine ⟨?_, ?_⟩
  · -- The shifted tail remains a free resolution of the first syzygy.
    exact { toQuasiIso := hκAug_quasi, termwise_free := hGfree }
  · intro n hn
    -- Vanishing one degree higher in `F` becomes the desired bound after shifting.
    simpa [G, X] using hF (n + 1) (Nat.succ_lt_succ hn)

omit [IsLocalRing R] in
/-- Helper for Proposition 10.110.1: a length-zero free resolution identifies `M` with the free
degree-zero term, so `M` already has projective dimension `0`. -/
lemma hasProjectiveDimensionLE_zero_of_hasFreeResolutionLengthLE_zero_mixed_universe
    (hres : HasFreeResolutionLengthLE R M 0) :
    HasProjectiveDimensionLE (ModuleCat.of R M) 0 := by
  rcases hres with ⟨F, π, hπ, hF⟩
  have hπ_surj : Function.Surjective (π.f 0).hom := by
    -- The augmentation of a free resolution is surjective in degree `0`.
    exact (ModuleCat.epi_iff_surjective _).mp
      (quasiIso_single_epi_zero (R := R) (N := M) (G := F) π)
  have hπ_comm : F.d 1 0 ≫ π.f 0 = 0 := by
    -- The augmented complex relation records `π₀ ∘ d₁₀ = 0`.
    simpa using (π.comm 1 0).symm
  let S₀ : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (F.d 1 0) (π.f 0) hπ_comm
  have hS₀_exact : S₀.Exact := by
    -- Exactness at degree `0` comes from the quasi-isomorphism to `single₀`.
    simpa [S₀] using quasiIso_single_exact_zero (R := R) (N := M) (G := F) π
  have hExact₀ : Function.Exact (F.d 1 0).hom (π.f 0).hom := by
    -- We again switch to the linear-map exactness API.
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₀).1 hS₀_exact
  have hX₁_zero : Limits.IsZero (F.X 1) := hF 1 (by simpa using Nat.zero_lt_one)
  have hd₁₀_zero : (F.d 1 0).hom = 0 := by
    -- Since degree `1` vanishes, the first differential is the zero map.
    ext x
    have hsub :
        Subsingleton (F.X 1) :=
      (ModuleCat.isZero_iff_subsingleton (M := F.X 1)).1 hX₁_zero
    have hx : x = 0 := Subsingleton.elim _ _
    simpa [hx]
  have hπ_inj : Function.Injective (π.f 0).hom := by
    -- Exactness identifies `ker π₀` with the image of the zero differential.
    have hker_bot : LinearMap.ker (π.f 0).hom = ⊥ := by
      rw [hExact₀.linearMap_ker_eq, hd₁₀_zero, LinearMap.range_zero]
    exact LinearMap.ker_eq_bot.mp hker_bot
  let e : ModuleCat.of R (F.X 0) ≅ ModuleCat.of R M :=
    (LinearEquiv.ofBijective (π.f 0).hom ⟨hπ_inj, hπ_surj⟩).toModuleIso
  have hproj₀ : Projective (F.X 0) := by
    -- Degree `0` of a free resolution is free, hence projective.
    let _ : Module.Free R (F.X 0) := ChainComplex.IsFreeResolution.free (R := R) (M := M) π 0
    infer_instance
  have hprojM : Projective (ModuleCat.of R M) := Projective.of_iso e hproj₀
  -- The projective object obtained from the degree-`0` term gives projective dimension `0`.
  exact (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero (ModuleCat.of R M)).1 hprojM

omit [IsLocalRing R] in
/-- Helper for Proposition 10.110.1: a bounded free resolution in the original module universe
still gives the canonical owner bound on projective dimension. -/
lemma hasProjectiveDimensionLE_of_hasFreeResolutionLengthLE_mixed_universe
    {n : ℕ} (hres : HasFreeResolutionLengthLE R M n) :
    HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  induction n generalizing M with
  | zero =>
      -- The base case is exactly the length-zero argument above.
      exact hasProjectiveDimensionLE_zero_of_hasFreeResolutionLengthLE_zero_mixed_universe
        (R := R) (M := M) hres
  | succ n ih =>
      rcases hres with ⟨F, π, hπ, hF⟩
      have hπ_surj : Function.Surjective (π.f 0).hom := by
        -- The augmentation of a free resolution is surjective in degree `0`.
        exact (ModuleCat.epi_iff_surjective _).mp
          (quasiIso_single_epi_zero (R := R) (N := M) (G := F) π)
      have hP₀proj : Projective (F.X 0) := by
        -- The first term of the free resolution is free, hence projective.
        let _ : Module.Free R (F.X 0) :=
          ChainComplex.IsFreeResolution.free (R := R) (M := M) π 0
        infer_instance
      have hker :
          HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker (π.f 0).hom)) n := by
        -- The shifted tail is a shorter free resolution of the first syzygy.
        exact ih <|
          hasFreeResolutionLengthLE_kernel_of_witness_succ_mixed_universe
            (R := R) (M := M) π hπ hF
      let S : ShortComplex (ModuleCat R) := LinearMap.shortComplexKer (π.f 0).hom
      have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hπ_surj
      -- The short exact sequence `0 → ker π₀ → F₀ → M → 0` raises the bound by one.
      simpa [S, HasProjectiveDimensionLE] using
        (hS.hasProjectiveDimensionLT_X₃_iff n hP₀proj).mpr (by
          simpa [HasProjectiveDimensionLE] using hker)

/-- Helper for Chap10 Proposition 10 110 1: a finite module admits a finite free presentation
whose source lives in the same `ModuleCat` universe, provided the ring is small in that universe. -/
lemma existsFiniteFreePresentation_of_small
    {R : Type u} [CommRing R] [Small.{v} R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (P₀ : ModuleCat.{v} R) (π₀ : P₀ ⟶ ModuleCat.of R M),
      Module.Free R P₀ ∧ Module.Finite R P₀ ∧ Function.Surjective π₀.hom := by
  obtain ⟨m, σ, hσ⟩ := exists_finite_free_cover (R := R) (N := M)
  letI : Small.{v} (Fin m → R) := inferInstance
  let e : Shrink.{v} (Fin m → R) ≃ₗ[R] (Fin m → R) :=
    Shrink.linearEquiv R (Fin m → R)
  let P₀ : ModuleCat.{v} R := ModuleCat.of R (Shrink.{v} (Fin m → R))
  let π₀ : P₀ ⟶ ModuleCat.of R M := ModuleCat.ofHom (σ.comp e.toLinearMap)
  refine ⟨P₀, π₀, ?_, ?_, ?_⟩
  · -- Shrinking the standard finite free cover keeps freeness in the target universe.
    let _ : Module.Free R (Fin m → R) := inferInstance
    exact Module.Free.of_equiv e.symm
  · -- The same linear equivalence transports finite generation of the cover source.
    let _ : Module.Finite R (Fin m → R) := inferInstance
    exact Module.Finite.equiv e.symm
  · -- Surjectivity is unchanged after precomposing with the shrink equivalence.
    intro x
    rcases hσ x with ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    calc
      π₀.hom (e.symm y) = σ y := by
        simpa [π₀] using congrArg σ (e.apply_symm_apply y)
      _ = x := hy

/-- Helper for Proposition 10.110.1: over a local Noetherian ring, a projective-dimension bound
can be turned back into a bounded finite free resolution even when the module universe differs
from the ring universe. -/
lemma hasFiniteFreeResolutionLengthLE_of_hasProjectiveDimensionLE_mixed_universe
    [Small.{v} R] [IsNoetherianRing R] [Module.Finite R M] {n : ℕ}
    (hpd : HasProjectiveDimensionLE (ModuleCat.of R M) n) :
    HasFiniteFreeResolutionLengthLE R M n := by
  induction n generalizing M with
  | zero =>
      have hprojCat : Projective (ModuleCat.of R M) :=
        (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero (ModuleCat.of R M)).2 hpd
      have hproj : Module.Projective R M := by
        letI : Projective (ModuleCat.of R M) := hprojCat
        exact ModuleCat.projective_of_module_projective (ModuleCat.of R M)
      let _ : Module.Projective R M := hproj
      -- Over a local ring, finite projective modules are free, giving the length-zero witness.
      exact (hasFiniteFreeResolutionLengthLE_zero_iff_mixed_universe (R := R) (M := M)).2
        ⟨projective_module_free_of_isLocalRing (R := R) (P := M), inferInstance⟩
  | succ n ih =>
      obtain ⟨P₀, π₀, hP₀free, hP₀finite, hπ₀⟩ :=
        existsFiniteFreePresentation_of_small (R := R) (M := M)
      have hP₀proj : Projective P₀ := by
        let _ : Module.Free R P₀ := hP₀free
        infer_instance
      let S : ShortComplex (ModuleCat R) := LinearMap.shortComplexKer π₀.hom
      have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hπ₀
      have hker_pd : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π₀.hom)) n := by
        have hM_lt : HasProjectiveDimensionLT (ModuleCat.of R M) (n + 2) := by
          simpa [HasProjectiveDimensionLE] using hpd
        have hker_lt :
            HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker π₀.hom)) (n + 1) := by
          -- The short exact syzygy criterion lowers the projective-dimension bound to the kernel.
          simpa [S] using (hS.hasProjectiveDimensionLT_X₃_iff n hP₀proj).mp hM_lt
        simpa [HasProjectiveDimensionLE] using hker_lt
      have hker_finite : Module.Finite R (LinearMap.ker π₀.hom) := by
        let _ : Module.Finite R P₀ := hP₀finite
        letI : IsNoetherian R P₀ := inferInstance
        letI : IsNoetherian R (LinearMap.ker π₀.hom) := inferInstance
        exact Module.IsNoetherian.finite R (LinearMap.ker π₀.hom)
      let _ : Module.Finite R (LinearMap.ker π₀.hom) := hker_finite
      have hK : HasFiniteFreeResolutionLengthLE R (LinearMap.ker π₀.hom) n :=
        ih hker_pd
      -- Prepending the finite free presentation raises the kernel resolution by one step.
      exact hasFiniteFreeResolutionLengthLE_succ_of_finite_free_presentation_mixed_universe
        (R := R) (M := M) π₀ hπ₀ hP₀free hP₀finite hK

end MixedUniverseBridge

/-- Helper for Proposition 10.110.1: after descending the ring, the remaining `ULift` on the
module can be removed by passing through the canonical owner statement on projective dimension and
transporting that owner across the linear equivalence. -/
lemma hasFiniteFreeResolutionLengthLE_of_linearEquiv_mixed_universe
    [Small.{v} R] [Small.{w} R]
    {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
    {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
    (e : M₁ ≃ₗ[R] M₂) {n : ℕ} :
    HasFiniteFreeResolutionLengthLE R M₁ n →
      HasFiniteFreeResolutionLengthLE R M₂ n := by
  intro hres
  have hfinite₁ : Module.Finite R M₁ :=
    module_finite_of_hasFiniteFreeResolutionLengthLE_mixed_universe (R := R) (M := M₁) hres
  let _ : Module.Finite R M₁ := hfinite₁
  have hfinite₂ : Module.Finite R M₂ := Module.Finite.equiv e
  let _ : Module.Finite R M₂ := hfinite₂
  have hfree₁ : HasFreeResolutionLengthLE R M₁ n :=
    hasFreeResolutionLengthLE_of_hasFiniteFreeResolutionLengthLE_mixed_universe
      (R := R) (M := M₁) hres
  have hpd₁ : HasProjectiveDimensionLE (ModuleCat.of R M₁) n :=
    hasProjectiveDimensionLE_of_hasFreeResolutionLengthLE_mixed_universe
      (R := R) (M := M₁) hfree₁
  have hpd₂ : HasProjectiveDimensionLE (ModuleCat.of R M₂) n := by
    let _ : HasProjectiveDimensionLE (ModuleCat.of R M₁) n := hpd₁
    -- Projective dimension is the universe-stable invariant transported by the linear equivalence.
    exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
      (M := ModuleCat.of R M₁) (N := ModuleCat.of R M₂) e n
  -- Convert the transported owner bound back to a finite free resolution over the target module.
  exact hasFiniteFreeResolutionLengthLE_of_hasProjectiveDimensionLE_mixed_universe
    (R := R) (M := M₂) hpd₂

/-- Helper for Proposition 10.110.1: the two scalar actions on a compatible restricted-scalar
module agree after rewriting the algebra map as the chosen ring equivalence. -/
lemma ringEquiv_compHom_smul_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (e : A ≃+* B)
    [Algebra A B] (halg : algebraMap A B = e.toRingHom)
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (a : A) (x : N) :
    a • x = e a • x := by
  have ha : algebraMap A B a = e a := by
    simpa using DFunLike.congr_fun halg a
  calc
    a • x = a • ((1 : B) • x) := by simp
    _ = ((algebraMap A B a) * 1 : B) • x := by
      simpa using (IsScalarTower.smul_assoc a (1 : B) x)
    _ = e a • x := by simp [ha]

/-- Helper for Proposition 10.110.1: after applying the inverse ring equivalence, the compatible
restricted-scalar action again agrees with the ambient scalar action. -/
lemma ringEquiv_compHom_symm_smul_eq
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (e : A ≃+* B)
    [Algebra A B] (halg : algebraMap A B = e.toRingHom)
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (b : B) (x : N) :
    b • x = e.symm b • x := by
  simpa using (ringEquiv_compHom_smul_eq
    (e := e) (halg := halg) (N := N) (a := e.symm b) (x := x)).symm

/-- Helper for Proposition 10.110.1: the identity map is semilinear when the `A`-action on a
`B`-module is obtained from a ring equivalence `A ≃+* B`. -/
noncomputable def ringEquiv_compHom_semilinearEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (e : A ≃+* B)
    [Algebra A B] (halg : algebraMap A B = e.toRingHom)
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [RingHomInvPair e.toRingHom e.symm.toRingHom]
    [RingHomInvPair e.symm.toRingHom e.toRingHom] :
    N ≃ₛₗ[e.toRingHom] N :=
  { toFun := id
    invFun := id
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := ringEquiv_compHom_smul_eq (e := e) (halg := halg) (N := N) }

/-- Helper for Proposition 10.110.1: the restricted-scalars object on a `B`-module with a
compatible `A`-module structure is canonically the same underlying `A`-module, with no
same-universe restriction on the three types. -/
lemma restrictScalars_objIso_identity_linear_mixed_universe
    {A : Type u} {B : Type v} {M : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (a : A) (x : (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M)) :
    (AddEquiv.refl M).toFun (a • x) = a • (AddEquiv.refl M).toFun x := by
  -- Rewrite the restricted action through `A → B` and then use the scalar-tower compatibility.
  rw [ModuleCat.restrictScalars.smul_def]
  simpa [one_smul, mul_one] using (IsScalarTower.smul_assoc a (1 : B) (x : M)).symm

/-- Helper for Proposition 10.110.1: the restricted-scalars object on a `B`-module with a
compatible `A`-module structure is canonically the same underlying `A`-module even in mixed
universes. -/
noncomputable def restrictScalars_objIso_mixed_universe
    {A : Type u} {B : Type v} {M : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] :
    (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M) ≅ ModuleCat.of A M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M)) ≃ₗ[A] M from
    { __ := AddEquiv.refl M
      map_smul' := restrictScalars_objIso_identity_linear_mixed_universe
        (A := A) (B := B) (M := M) }).toModuleIso

/-- Helper for Proposition 10.110.1: the mixed-universe restricted-scalars object-identity bridge
acts by the identity on elements. -/
@[simp] lemma restrictScalars_objIso_mixed_universe_hom_apply
    {A : Type u} {B : Type v} {M : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (x : (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B M)) :
    (restrictScalars_objIso_mixed_universe (A := A) (B := B) (M := M)).hom x = x :=
  rfl

/-- Helper for Proposition 10.110.1: the inverse mixed-universe restricted-scalars bridge also
acts by the identity on elements. -/
@[simp] lemma restrictScalars_objIso_mixed_universe_inv_apply
    {A : Type u} {B : Type v} {M : Type w} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (x : M) :
    (restrictScalars_objIso_mixed_universe (A := A) (B := B) (M := M)).inv x = x :=
  rfl

/-- Helper for Proposition 10.110.1: across a ring equivalence, the owner statement
`HasProjectiveDimensionLE` descends along the compatible restriction-of-scalars action. -/
lemma hasProjectiveDimensionLE_of_ringEquiv_compHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (e : A ≃+* B)
    [Algebra A B] (halg : algebraMap A B = e.toRingHom)
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Small.{w} A] [Small.{w} B]
    {n : ℕ} :
    HasProjectiveDimensionLE (ModuleCat.of B N) n →
      HasProjectiveDimensionLE (ModuleCat.of A N) n := by
  intro hpd
  letI : HasProjectiveDimensionLE (ModuleCat.of B N) n := hpd
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.symm e.toRingHom e.symm.toRingHom
  -- Apply the owner-level transport theorem to the identity semilinear equivalence on `N`.
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv
    (e := e.symm) (M := ModuleCat.of B N) (N := ModuleCat.of A N)
    (e' := (ringEquiv_compHom_semilinearEquiv
      (e := e) (halg := halg) (N := N)).symm)
    n

/-- Helper for Proposition 10.110.1: restricting scalars along a ring equivalence preserves the
existence of a bounded finite free resolution by transporting projective dimension first. -/
lemma hasFiniteFreeResolutionLengthLE_of_ringEquiv_compHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (e : A ≃+* B)
    [Algebra A B] (halg : algebraMap A B = e.toRingHom)
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A]
    [Small.{w} A] [Small.{w} B]
    (htower : IsScalarTower A B N)
    {n : ℕ} :
    HasFiniteFreeResolutionLengthLE B N n →
      HasFiniteFreeResolutionLengthLE A N n := by
  intro hres
  letI : IsScalarTower A B N := htower
  have hfiniteB : Module.Finite B N :=
    module_finite_of_hasFiniteFreeResolutionLengthLE_mixed_universe (R := B) (M := N) hres
  let _ : Module.Finite B N := hfiniteB
  have hfreeB : HasFreeResolutionLengthLE B N n :=
    hasFreeResolutionLengthLE_of_hasFiniteFreeResolutionLengthLE_mixed_universe
      (R := B) (M := N) hres
  have hpdB : HasProjectiveDimensionLE (ModuleCat.of B N) n :=
    hasProjectiveDimensionLE_of_hasFreeResolutionLengthLE_mixed_universe
      (R := B) (M := N) hfreeB
  have hpdA : HasProjectiveDimensionLE (ModuleCat.of A N) n :=
    hasProjectiveDimensionLE_of_ringEquiv_compHom
      (A := A) (B := B) (e := e) (halg := halg) (N := N) hpdB
  have hfiniteA : Module.Finite A N := by
    have hAB : Module.Finite A B := by
      have hsurj : Function.Surjective (Algebra.linearMap A B) := by
        -- The chosen ring equivalence makes the algebra map onto `B`.
        intro b
        refine ⟨e.symm b, ?_⟩
        change algebraMap A B (e.symm b) = b
        rw [halg]
        exact e.apply_symm_apply b
      exact Module.Finite.of_surjective (Algebra.linearMap A B) hsurj
    let _ : Module.Finite A B := hAB
    exact Module.Finite.trans B N
  let _ : Module.Finite A N := hfiniteA
  -- The descended owner bound is converted back to a finite free resolution over `A`.
  exact hasFiniteFreeResolutionLengthLE_of_hasProjectiveDimensionLE_mixed_universe
    (R := A) (M := N) hpdA

/-- Chap10 Proposition 10 110 1: if `R` is a regular local ring of dimension `d` and `M` is a
finite `R`-module of depth `e`, then `M` admits a finite free resolution of length at most
`d - e`. -/
@[stacks 00O7]
theorem hasFiniteFreeResolutionLengthLE_of_moduleDepth_of_isRegularLocalRing
    {d e : ℕ} (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M = e) :
    HasFiniteFreeResolutionLengthLE R M (d - e) := by
  -- Route correction: the owner-level descent to projective dimension downstairs is available,
  -- but the source-facing finite free resolution now factors through one witness-level descent
  -- lemma and one mixed-universe linear equivalence.
  let Rw : Type (max u v) := ULift.{max u v} R
  let Mw : Type (max u v) := ULift.{u} M
  have hupstairs :
      HasFiniteFreeResolutionLengthLE Rw Mw (d - e) :=
    hasFiniteFreeResolutionLengthLE_of_ulift_ring_model
      (R := R) (M := M) hdim hdepth
  letI : IsRegularLocalRing Rw := isRegularLocalRing_of_ulift_ring_model (R := R)
  letI : Algebra R (ULift.{max u v} R) :=
    ((ULift.ringEquiv : ULift.{max u v} R ≃+* R).symm).toRingHom.toAlgebra
  let htower : IsScalarTower R (ULift.{max u v} R) (ULift.{u} M) :=
    { smul_assoc := fun r a m ↦ by
        -- Both lifted scalar actions are defined coordinatewise on `ULift`.
        cases a
        cases m
        simp }
  let _ : Small.{max u v} R :=
    small_of_injective (f := (ULift.up : R → ULift.{max u v} R)) ULift.up_injective
  let _ : Small.{max u v} (ULift.{max u v} R) := inferInstance
  have hdownstairs_ulift :
      HasFiniteFreeResolutionLengthLE R (ULift.{u} M) (d - e) :=
    hasFiniteFreeResolutionLengthLE_of_ringEquiv_compHom
      (A := R) (B := ULift.{max u v} R)
      (e := (ULift.ringEquiv : ULift.{max u v} R ≃+* R).symm)
      (halg := rfl) (htower := htower) (N := ULift.{u} M) hupstairs
  -- After descending the ring, only the module lift remains, and the canonical linear
  -- equivalence `ULift.moduleEquiv` removes it without changing the length bound.
  exact
    hasFiniteFreeResolutionLengthLE_of_linearEquiv_mixed_universe
      (R := R) (M₁ := Mw) (M₂ := M) (ULift.moduleEquiv (R := R) (M := M))
      hdownstairs_ulift

-- Proof sketch: first prove the source-facing finite free resolution statement above, then forget
-- finiteness and apply the mixed-universe free-resolution-to-projective-dimension bridge.
/-- Core/canonical form of Proposition 10.110.1 (1): if `R` is a regular local ring of dimension
`d` and `M` is a finite `R`-module of depth `e`, then `M` has projective dimension at most
`d - e`. -/
theorem hasProjectiveDimensionLE_of_moduleDepth_of_isRegularLocalRing
    {d e : ℕ} (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M = e) :
    HasProjectiveDimensionLE (ModuleCat.of R M) (d - e) := by
  have hres :
      HasFiniteFreeResolutionLengthLE R M (d - e) :=
    hasFiniteFreeResolutionLengthLE_of_moduleDepth_of_isRegularLocalRing
      (R := R) (M := M) hdim hdepth
  have hfree :
      HasFreeResolutionLengthLE R M (d - e) :=
    hasFreeResolutionLengthLE_of_hasFiniteFreeResolutionLengthLE_mixed_universe
      (R := R) (M := M) hres
  -- The remaining step is the mixed-universe projective-dimension bridge proved above.
  exact hasProjectiveDimensionLE_of_hasFreeResolutionLengthLE_mixed_universe
    (R := R) (M := M) hfree

/-- Helper for Proposition 10.110.1: every cyclic quotient `R ⧸ I` over a regular local ring of
dimension `d` has projective dimension at most `d`. -/
lemma cyclic_quotient_hasProjectiveDimensionLE_of_isRegularLocalRing
    {d : ℕ} (hdim : ringKrullDim R = d) (I : Ideal R) :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) d := by
  by_cases hI : I = ⊤
  · subst hI
    have hzero :
        Limits.IsZero (ModuleCat.of R (R ⧸ (⊤ : Ideal R))) := by
      exact
        (ModuleCat.isZero_iff_subsingleton (M := ModuleCat.of R (R ⧸ (⊤ : Ideal R)))).2
          inferInstance
    have hpd0 :
        HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ (⊤ : Ideal R))) 0 :=
      (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero
        (ModuleCat.of R (R ⧸ (⊤ : Ideal R)))).1 hzero.projective
    letI : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ (⊤ : Ideal R))) 0 := hpd0
    -- The zero cyclic quotient has projective dimension `0`, hence also `≤ d`.
    exact
      CategoryTheory.hasProjectiveDimensionLT_of_ge
        (X := ModuleCat.of R (R ⧸ (⊤ : Ideal R))) 1 (d + 1) (by omega)
  · obtain ⟨e, hdepth⟩ := exists_nat_moduleDepth_of_proper_quotient (R := R) hI
    have hpd :
        HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) (d - e) :=
      hasProjectiveDimensionLE_of_moduleDepth_of_isRegularLocalRing
        (R := R) (M := R ⧸ I) hdim hdepth
    letI : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) (d - e) := hpd
    -- The owner bound is monotone in the integer parameter, so `d - e ≤ d` upgrades the result.
    exact
      CategoryTheory.hasProjectiveDimensionLT_of_ge
        (X := ModuleCat.of R (R ⧸ I)) (d - e + 1) (d + 1) (by omega)

-- Proof sketch: apply the canonical module-wise bound above to finite modules and then use the
-- finite/cyclic criterion for the owner `HasGlobalDimensionLE R d`.
/-- Consequence of Chap10 Proposition 10 110 1: a regular local ring of dimension `d` has global
dimension at most `d` (Proposition 10.110.1 (2)). -/
@[stacks 00O7]
theorem hasGlobalDimensionLE_of_isRegularLocalRing
    {d : ℕ} (hdim : ringKrullDim R = d) :
    HasGlobalDimensionLE R d := by
  -- The source-faithful closing step is exactly the cyclic-module clause of Lemma `10.109.12`.
  exact ((globalDimensionLE_tfae_finite_and_cyclic_modules (R := R) d).out 2 0).mp
    (fun I ↦ cyclic_quotient_hasProjectiveDimensionLE_of_isRegularLocalRing
      (R := R) hdim I)

end
