import stacks_proof.stacks_project.Chap10.Lemma_10_109_5
import stacks_proof.stacks_project.Chap10.Lemma_10_109_6
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory ChainComplex Limits

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/- Domain-style sampling:
* primary domain: bounded finite free resolutions of finite modules over local Noetherian rings;
* sampled declarations:
  `ChainComplex.IsFiniteFreeResolution`,
  `HasFiniteFreeResolutionLengthLE`,
  `ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms`,
  `ChainComplex.IsFiniteFreeResolution`,
  `projective_module_free_of_isLocalRing`;
* best owner abstraction: `HasFiniteFreeResolutionLengthLE R M d`, built from
  `ChainComplex.IsFiniteFreeResolution`;
* layer triage: `HasFiniteFreeResolutionLengthLE` is `source-facing`, while this item is the
  `bridge/view` from projective dimension to that owner;
* primitive data: a bounded augmented chain complex with `IsFiniteFreeResolution`;
* derived API: the coordinate-level finite-projective exact sequence of Lemma `10.109.6` is only a
  bridge into this owner abstraction.
-/

-- Proof sketch: Lemma `10.109.6` provides a bounded finite-projective resolution with finite
-- terms. Over a local ring, Theorem `10.85.4` upgrades each projective term to a free term, so
-- the same bounded resolution yields a bounded finite free resolution. Conversely, a bounded
-- finite free resolution is in particular a bounded free resolution, hence gives projective
-- dimension at most `d`.
/-- Helper for Lemma 10.109.7: a bounded finite-projective resolution with finite terms starts
with a finite projective presentation whose kernel still has a bounded finite-projective
resolution with finite terms. -/
theorem exists_finite_projective_presentation_with_finite_kernel_resolution {n : ℕ}
    (hM :
      ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms
        (ModuleCat.of R M) (n + 1)) :
    ∃ (P₀ : ModuleCat R) (π : P₀ ⟶ ModuleCat.of R M),
      Module.Projective R P₀ ∧
        Module.Finite R P₀ ∧
          Function.Surjective π.hom ∧
            ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms
              (ModuleCat.of R (LinearMap.ker π.hom)) n := by
  cases n with
  | zero =>
      rcases hM with ⟨P, δ, π, hπ, hExact, _, hInj⟩
      have hδ_mem :
          ∀ x, ((δ 0).hom).hom x ∈ LinearMap.ker π.hom :=
        linearMap_mem_ker_of_exact (R := R)
          (show Function.Exact ((δ 0).hom).hom π.hom from hExact)
      let κ : (P 1).obj ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom
          (LinearMap.codRestrict (LinearMap.ker π.hom) ((δ 0).hom).hom hδ_mem)
      have hκ_surj : Function.Surjective κ.hom := by
        -- Exactness at `P₀` identifies `ker π` with the image of `δ₀`.
        intro x
        rcases (hExact x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_inj : Function.Injective κ.hom := by
        -- Injectivity of `δ₀` passes to the codomain restriction `κ`.
        intro x y hxy
        have hxy_val : ((δ 0).hom).hom x = ((δ 0).hom).hom y := by
          simpa [κ] using congrArg Subtype.val hxy
        exact hInj hxy_val
      let e : (P 1).obj ≅ ModuleCat.of R (LinearMap.ker π.hom) :=
        (LinearEquiv.ofBijective κ.hom ⟨hκ_inj, hκ_surj⟩).toModuleIso
      have hker_projective_cat :
          Projective (ModuleCat.of R (LinearMap.ker π.hom)) := by
        -- The left term is isomorphic to the first kernel, so the kernel is projective.
        have hP₁_projective : Projective ((P 1).obj) := by
          infer_instance
        exact Projective.of_iso e hP₁_projective
      have hker_projective :
          Module.Projective R (ModuleCat.of R (LinearMap.ker π.hom)) :=
        module_projective_of_categorical_projective (R := R) hker_projective_cat
      have hP₀_projective : Module.Projective R (P 0).obj := inferInstance
      have hP₀_finite : Module.Finite R (P 0).obj := inferInstance
      let _ : Module.Finite R (P 0).obj := hP₀_finite
      have hker_finite :
          Module.Finite R (ModuleCat.of R (LinearMap.ker π.hom)) := by
        -- The kernel is finite because it sits inside the finite domain `(P 0).obj`.
        simpa using kernel_finite_of_domain_finite (R := R) π
      refine ⟨(P 0).obj, π, hP₀_projective, hP₀_finite, hπ, ?_⟩
      -- In length `0`, the kernel data is exactly finite projectivity.
      exact ⟨hker_projective, hker_finite⟩
  | succ n =>
      rcases hM with ⟨P, δ, π, hπ, hExact₀, hExact, hInj⟩
      have hδ_mem :
          ∀ x, ((δ 0).hom).hom x ∈ LinearMap.ker π.hom :=
        linearMap_mem_ker_of_exact (R := R)
          (show Function.Exact ((δ 0).hom).hom π.hom from hExact₀)
      let κ : (P 1).obj ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom
          (LinearMap.codRestrict (LinearMap.ker π.hom) ((δ 0).hom).hom hδ_mem)
      have hκ_surj : Function.Surjective κ.hom := by
        -- Exactness at `P₀` identifies `ker π` with the image of `δ₀`.
        intro x
        rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_ker : LinearMap.ker κ.hom = LinearMap.ker ((δ 0).hom).hom := by
        -- Restricting the codomain to `ker π` does not change the kernel of `δ₀`.
        simpa [κ] using
          LinearMap.ker_codRestrict (LinearMap.ker π.hom) ((δ 0).hom).hom hδ_mem
      let P' : Fin (n + 2) → FiniteProjectiveModuleCat R := fun i ↦ P i.succ
      let δ' : (i : Fin (n + 1)) → P' i.succ ⟶ P' i.castSucc := fun i ↦ δ i.succ
      have hκ_exact : Function.Exact (δ' 0).hom κ.hom := by
        -- Exactness of `δ₁` against `δ₀` becomes exactness against the restricted kernel map.
        exact LinearMap.exact_iff.mpr <| hκ_ker.trans (hExact 0).linearMap_ker_eq
      have hδ'_exact :
          ∀ i : Fin n, Function.Exact (δ' i.succ).hom (δ' i.castSucc).hom := by
        intro i
        -- Every later exactness statement is inherited verbatim from the original sequence.
        simpa [δ', Fin.castSucc_succ] using hExact i.succ
      have hδ'_inj : Function.Injective (δ' (Fin.last n)).hom := by
        -- The top differential of the truncated finite resolution is the original top differential.
        simpa [δ'] using hInj
      have hP₀_projective : Module.Projective R (P 0).obj := inferInstance
      have hP₀_finite : Module.Finite R (P 0).obj := inferInstance
      refine ⟨(P 0).obj, π, hP₀_projective, hP₀_finite, hπ, ?_⟩
      -- The tail of the finite-projective sequence resolves the first syzygy.
      exact ⟨P', δ', κ, hκ_surj, hκ_exact, hδ'_exact, hδ'_inj⟩

/-- Helper for Lemma 10.109.7: forgetting the finiteness decoration of a finite free resolution
produces an ordinary free resolution of the same length. -/
theorem hasFreeResolutionLengthLE_of_hasFiniteFreeResolutionLengthLE {d : ℕ}
    (hM : HasFiniteFreeResolutionLengthLE R M d) :
    HasFreeResolutionLengthLE R M d := by
  rcases hM with ⟨F, π, hπ, hF⟩
  refine ⟨F, π, hπ.toIsFreeResolution, hF⟩

/-- Helper for Lemma 10.109.7: a surjective map from a finite free module onto `M` extends a
bounded finite free resolution of its kernel by one step to a bounded finite free resolution of
`M`. -/
theorem hasFiniteFreeResolutionLengthLE_succ_of_finite_free_presentation
    {d : ℕ} {P₀ : ModuleCat R} (π₀ : P₀ ⟶ ModuleCat.of R M)
    (hπ₀ : Function.Surjective π₀.hom) (hP₀ : Module.Free R P₀)
    (hP₀finite : Module.Finite R P₀)
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
  let ν : G ⟶ moduleSingle[R] M :=
    (ChainComplex.toSingle₀Equiv G (ModuleCat.of R M)).symm ⟨π₀, hδ₀_aug⟩
  have hGfree : ChainComplex.IsTermwiseFree G := by
    intro n
    cases n with
    | zero =>
        -- Degree `0` is the chosen finite free presentation term.
        simpa [G, X] using hP₀
    | succ n =>
        -- Every positive degree is inherited from the given finite free resolution of `ker π₀`.
        simpa [G, X] using
          (IsFreeResolution.free (R := R) (M := LinearMap.ker π₀.hom) π n)
  have hGfinite : ChainComplex.IsTermwiseFinite G := by
    intro n
    cases n with
    | zero =>
        -- Degree `0` is finite by hypothesis on the chosen presentation.
        simpa [G, X] using hP₀finite
    | succ n =>
        -- Every positive degree is inherited from the kernel's finite free resolution.
        simpa [G, X] using
          (ChainComplex.IsFiniteFreeResolution.finite π n)
  have hν_quasi : QuasiIso ν := by
    refine ⟨fun n ↦ ?_⟩
    cases n with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
        · -- Degree `0` is exactly `F₀ → ker π₀ → P₀ → M`, so exactness and surjectivity come
          -- from the kernel resolution and the free presentation.
          refine ⟨?_, ?_⟩
          · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 <|
              exact_subtype_comp_of_surjective
                (R := R) (g := π₀.hom) (k := (π.f 0).hom) hπ_surj
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
                -- Postcomposing with the kernel subtype preserves the degree-`1` exactness.
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
  refine ⟨G, ν, ?_⟩
  refine ⟨?_, ?_⟩
  · -- The prepended complex is finite free because it is quasi-isomorphic to `single₀ M`,
    -- termwise free, and termwise finite.
    let hνfree : IsFreeResolution ν := { toQuasiIso := hν_quasi, termwise_free := hGfree }
    letI : IsFreeResolution ν := hνfree
    exact ⟨hGfinite⟩
  · intro n hn
    cases n with
    | zero =>
        exact (Nat.not_lt_zero _ hn).elim
    | succ n =>
        -- Vanishing above degree `d + 1` is inherited from the kernel resolution after shifting.
        simpa [G, X] using hF n (Nat.lt_of_succ_lt_succ hn)

/-- Helper for Lemma 10.109.7: over a local Noetherian ring, a bounded finite projective
resolution with finite terms can be refined termwise to a bounded finite free resolution. -/
theorem hasFiniteFreeResolutionLengthLE_of_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
    {d : ℕ}
    (hM :
      ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms
        (ModuleCat.of R M) d) :
    HasFiniteFreeResolutionLengthLE R M d := by
  induction d generalizing M with
  | zero =>
      rw [ModuleCat.hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff] at hM
      have hproj : Module.Projective R M := by
        simpa using hM.1
      let _ : Module.Projective R M := hproj
      -- In degree `0`, finite projective equals finite free over the local ring.
      exact (hasFiniteFreeResolutionLengthLE_zero_iff (R := R) (M := M)).2
        ⟨projective_module_free_of_isLocalRing (R := R) (P := M), inferInstance⟩
  | succ d ih =>
      rcases exists_finite_projective_presentation_with_finite_kernel_resolution
        (R := R) (M := M) hM with
        ⟨P₀, π₀, hP₀proj, hP₀finite, hπ₀, hker⟩
      let _ : Module.Projective R P₀ := hP₀proj
      let _ : Module.Finite R P₀ := hP₀finite
      have hP₀free : Module.Free R P₀ :=
        projective_module_free_of_isLocalRing (R := R) (P := P₀)
      have hker_finite : Module.Finite R (LinearMap.ker π₀.hom) := by
        -- The first syzygy is finite because it is a kernel inside the finite module `P₀`.
        simpa using kernel_finite_of_domain_finite (R := R) π₀
      let _ : Module.Finite R (LinearMap.ker π₀.hom) := hker_finite
      have hfree_ker :
          HasFiniteFreeResolutionLengthLE R (LinearMap.ker π₀.hom) d :=
        ih hker
      -- One more finite free presentation step recovers the desired bounded finite free
      -- resolution of `M`.
      exact hasFiniteFreeResolutionLengthLE_succ_of_finite_free_presentation
        (R := R) (M := M) π₀ hπ₀ hP₀free hP₀finite hfree_ker

/-- Lemma 10.109.7: for a finite module over a local Noetherian ring, having projective dimension
at most `d` is equivalent to admitting a finite free resolution of length at most `d`. -/
@[stacks 0CXF]
theorem hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE
    (d : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R M) d ↔
      HasFiniteFreeResolutionLengthLE R M d := by
  constructor
  · intro hpd
    have hfinite_projective :
        ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms
          (ModuleCat.of R M) d :=
      (hasProjectiveDimensionLE_iff_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
        (R := R) (M := M) d).mp hpd
    -- The source proof first upgrades the bounded finite-projective resolution to a bounded
    -- finite free resolution over the local ring.
    exact hasFiniteFreeResolutionLengthLE_of_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
      (R := R) (M := M) hfinite_projective
  · intro hfinite_free
    have hfree : HasFreeResolutionLengthLE R M d :=
      hasFreeResolutionLengthLE_of_hasFiniteFreeResolutionLengthLE
        (R := R) (M := M) hfinite_free
    -- Forgetting termwise finiteness reduces the reverse implication to Lemma `10.109.5`.
    exact (hasProjectiveDimensionLE_iff_hasFreeResolutionLengthLE
      (R := R) (M := M) d).mpr hfree

end
