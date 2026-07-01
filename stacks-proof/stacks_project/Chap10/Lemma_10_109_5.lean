import Mathlib
import stacks_project.Chap10.Definition_10_71_2
import stacks_project.Chap10.Lemma_10_71_4
import stacks_project.Chap10.Lemma_10_109_4
import stacks_project.Chap10.Theorem_10_85_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory ChainComplex Limits

section

variable {R : Type u} [Ring R]
variable {M : Type u} [AddCommGroup M] [Module R M]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/-
Domain-style sampling:
* primary domain: free resolutions of modules and their boundedness properties;
* sampled owner declarations:
  `ChainComplex.IsFreeResolution`,
  `ChainComplex.IsFiniteFreeResolution`,
  `ChainComplex.IsTermwiseFree`,
  `CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)`;
* best owner abstraction: `ChainComplex.IsFreeResolution π` for an augmentation
  `π : F ⟶ moduleSingle[R] M`;
* layer triage:
  `ChainComplex.IsFreeResolution` is `core/canonical`,
  `HasFreeResolutionLengthLE` and `HasFiniteFreeResolutionLengthLE` below are `source-facing`,
  the final equivalence with `HasProjectiveDimensionLE (ModuleCat.of R M) d` is a `bridge/view`;
* primitive data: a free resolution `π : F ⟶ moduleSingle[R] M`;
* derived API: the length bound, expressed by vanishing of the complex above degree `d`, and the
  extra termwise-finite hypothesis when the source calls the resolution finite free.
-/

/-- `M` admits a free resolution of length at most `d`. For `d = 0` this means that `M`
itself is free; for `d = n + 1` it is an exact sequence
`0 ⟶ P_{n+1} ⟶ P_n ⟶ ⋯ ⟶ P₀ ⟶ M ⟶ 0`
with every `Pᵢ` free. -/
def HasFreeResolutionLengthLE
    (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] (d : ℕ) : Prop :=
  ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R] M),
    IsFreeResolution π ∧
      ∀ n : ℕ, d < n → IsZero (F.X n)

-- Proof sketch: if the resolution is supported in degree `0`, then its augmentation identifies
-- `M` with the degree-`0` term of a free resolution, so `M` is free; conversely, a free module is
-- resolved by the degree-`0` chain complex `single₀`.
/-- A free resolution of length at most `0` is exactly freeness of `M`. -/
theorem hasFreeResolutionLengthLE_zero_iff :
    HasFreeResolutionLengthLE R M 0 ↔ Module.Free R M :=
  sorry

/-- `M` admits a finite free resolution of length at most `d`. For `d = 0` this means that `M`
itself is finite free; for `d = n + 1` it is an exact sequence
`0 ⟶ P_{n+1} ⟶ P_n ⟶ ⋯ ⟶ P₀ ⟶ M ⟶ 0`
with every `Pᵢ` finite free. -/
def HasFiniteFreeResolutionLengthLE
    (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] (d : ℕ) : Prop :=
  ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R] M),
    IsFiniteFreeResolution π ∧
      ∀ n : ℕ, d < n → IsZero (F.X n)

/-- A finite free resolution of length at most `0` is exactly finite freeness of `M`. -/
theorem hasFiniteFreeResolutionLengthLE_zero_iff :
    HasFiniteFreeResolutionLengthLE R M 0 ↔ Module.Free R M ∧ Module.Finite R M :=
  sorry

end

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/-- Helper for Lemma 10.109.5: surjectivity onto the kernel lets exactness pass through the kernel
subtype map. -/
theorem exact_subtype_comp_of_surjective
    {A B C : Type u}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {g : B →ₗ[R] C} {k : A →ₗ[R] LinearMap.ker g}
    (hk : Function.Surjective k) :
    Function.Exact ((LinearMap.ker g).subtype.comp k) g := by
  -- Surjectivity of `k` reduces exactness to the canonical kernel-subtype sequence.
  exact (Function.Surjective.comp_exact_iff_exact
    (f := (LinearMap.ker g).subtype) (g := g) hk).2
    (LinearMap.exact_subtype_ker_map g)

/-- Helper for Lemma 10.109.5: an exact pair `f, g` makes the codomain restriction of `f` to
`ker g` surjective. -/
theorem surjective_codRestrict_ker_of_exact
    {A B C : Type u}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (hExact : Function.Exact f g) :
    Function.Surjective
      (LinearMap.codRestrict (LinearMap.ker g) f
        (linearMap_mem_ker_of_exact (R := R) hExact)) := by
  -- Exactness identifies `ker g` with the image of `f`, so every cycle has a preimage.
  intro x
  rcases (hExact x.1).mp x.2 with ⟨y, hy⟩
  refine ⟨y, Subtype.ext ?_⟩
  simpa using hy

/-- Helper for Lemma 10.109.5: if `f` is exact against `g`, then it is also exact against the
codomain restriction of `g` to the kernel of the next map. -/
theorem exact_codRestrict_ker_of_exact
    {A B C D : Type u}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    [AddCommGroup D] [Module R D]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} {h : C →ₗ[R] D}
    (hfg : Function.Exact f g) (hgh : Function.Exact g h) :
    Function.Exact f
      (LinearMap.codRestrict (LinearMap.ker h) g
        (linearMap_mem_ker_of_exact (R := R) hgh)) := by
  let κ : B →ₗ[R] LinearMap.ker h :=
    LinearMap.codRestrict (LinearMap.ker h) g
      (linearMap_mem_ker_of_exact (R := R) hgh)
  have hsub_inj : Function.Injective (LinearMap.ker h).subtype :=
    Submodule.injective_subtype (LinearMap.ker h)
  have hcomp : Function.Exact f ((LinearMap.ker h).subtype.comp κ) := by
    -- Forgetting the codomain restriction recovers the original exact pair.
    simpa [κ] using hfg
  exact (Function.Injective.comp_exact_iff_exact
    (f := f) (g := κ) hsub_inj).1 hcomp

/-- Helper for Lemma 10.109.5: a surjective map from a free module onto `M` extends a bounded
free resolution of its kernel by one step to a bounded free resolution of `M`. -/
theorem hasFreeResolutionLengthLE_succ_of_free_presentation
    {d : ℕ} {P₀ : ModuleCat R} (π₀ : P₀ ⟶ ModuleCat.of R M)
    (hπ₀ : Function.Surjective π₀.hom) (hP₀ : Module.Free R P₀)
    (hK : HasFreeResolutionLengthLE R (LinearMap.ker π₀.hom) d) :
    HasFreeResolutionLengthLE R M (d + 1) := by
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
        -- complex.
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
        -- Degree `0` is the chosen free presentation term.
        simpa [G, X] using hP₀
    | succ n =>
        -- Every positive degree is inherited from the given free resolution of `ker π₀`.
        simpa [G, X] using
          (IsFreeResolution.free (R := R) (M := LinearMap.ker π₀.hom) π n)
  have hν_quasi : QuasiIso ν := by
    refine ⟨fun n ↦ ?_⟩
    cases n with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
        · -- Degree `0` is exactly `F₀ → ker π₀ → P₀ → M`, so exactness and surjectivity come
          -- from the kernel resolution and the free presentation.
          refine ⟨?_, ?_⟩
          · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 <|
              exact_subtype_comp_of_surjective (R := R) (g := π₀.hom) (k := (π.f 0).hom) hπ_surj
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
  · -- The prepended complex is a free resolution because it is termwise free and quasi-isomorphic
    -- to `single₀ M`.
    exact { toQuasiIso := hν_quasi, termwise_free := hGfree }
  · intro n hn
    cases n with
    | zero =>
        exact (Nat.not_lt_zero _ hn).elim
    | succ n =>
        -- Vanishing above degree `d + 1` is inherited from the kernel resolution after shifting.
        simpa [G, X] using hF n (Nat.lt_of_succ_lt_succ hn)

/-- Helper for Lemma 10.109.5: a bounded finite projective resolution over a local ring can be
refined to a bounded free resolution by replacing each projective presentation term with a free
one. -/
theorem hasFreeResolutionLengthLE_of_hasFiniteProjectiveResolutionLengthLE {d : ℕ}
    (hM : HasFiniteProjectiveResolutionLengthLE (M := ModuleCat.of R M) d) :
    HasFreeResolutionLengthLE R M d := by
  induction d generalizing M with
  | zero =>
      -- In degree `0`, local projective modules are free.
      rw [hasFiniteProjectiveResolutionLengthLE_zero_iff] at hM
      have hproj : Module.Projective R (ModuleCat.of R M) :=
        module_projective_of_categorical_projective (R := R) hM
      let _ : Module.Projective R M := hproj
      exact (hasFreeResolutionLengthLE_zero_iff (R := R) (M := M)).2
        (projective_module_free_of_isLocalRing (R := R) (P := M))
  | succ d ih =>
      rcases exists_projective_presentation_with_finite_kernel_resolution
        (M := ModuleCat.of R M) hM with
        ⟨P₀, π₀, hP₀, hπ₀, hker⟩
      have hP₀proj : Module.Projective R P₀ :=
        module_projective_of_categorical_projective (R := R) hP₀
      let _ : Module.Projective R P₀ := hP₀proj
      have hP₀free : Module.Free R P₀ :=
        projective_module_free_of_isLocalRing (R := R) (P := P₀)
      have hfreeKer :
          HasFreeResolutionLengthLE R (LinearMap.ker π₀.hom) d :=
        ih hker
      -- One more free presentation step recovers the desired bounded free resolution of `M`.
      exact hasFreeResolutionLengthLE_succ_of_free_presentation
        (R := R) (M := M) π₀ hπ₀ hP₀free hfreeKer

/-- Helper for Lemma 10.109.5: the tail of a bounded free resolution is a bounded free resolution
of the first syzygy. -/
theorem hasFreeResolutionLengthLE_kernel_of_witness_succ
    {d : ℕ} {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ moduleSingle[R] M) (hπ : IsFreeResolution π)
    (hF : ∀ n : ℕ, d + 1 < n → IsZero (F.X n)) :
    HasFreeResolutionLengthLE R (LinearMap.ker (π.f 0).hom) d := by
  have hπ_comm : F.d 1 0 ≫ π.f 0 = 0 := by
    -- The original augmentation kills the first differential.
    simpa using (π.comm 1 0).symm
  let S₀ : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (F.d 1 0) (π.f 0) hπ_comm
  have hS₀_exact : S₀.Exact := by
    -- Degree `0` exactness of the original free resolution.
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
    -- Degree `1` exactness of the original free resolution.
    simpa [S₁] using quasiIso_single_exact_succ (R := R) (N := M) (G := F) π 0
  have hExact₁ : Function.Exact (F.d 2 1).hom (F.d 1 0).hom := by
    -- Again we move to the linear-map API used for `codRestrict`.
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₁).1 hS₁_exact
  have hκ_mem : ∀ x, (F.d 1 0).hom x ∈ LinearMap.ker (π.f 0).hom :=
    linearMap_mem_ker_of_exact (R := R) hExact₀
  let X : ℕ → ModuleCat R := fun n ↦ F.X (n + 1)
  let δ : ∀ n : ℕ, X (n + 1) ⟶ X n := fun n ↦ F.d (n + 2) (n + 1)
  have hδ_sq : ∀ n : ℕ, δ (n + 1) ≫ δ n = 0 := by
    intro n
    -- The shifted tail is still a chain complex because `F` is one.
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
    -- Every degree of the shifted tail is one degree of the original free resolution.
    simpa [G, X] using (IsFreeResolution.free (R := R) (M := M) π (n + 1))
  have hκ_surj : Function.Surjective κ.hom := by
    -- Exactness at `F₀` identifies the first syzygy with the image of `d₁₀`.
    simpa [κ] using surjective_codRestrict_ker_of_exact (R := R) hExact₀
  have hκ_exact : Function.Exact (δ 0).hom κ.hom := by
    -- Exactness at `F₁` survives after restricting the codomain of `d₁₀` to `ker π₀`.
    simpa [δ, κ] using exact_codRestrict_ker_of_exact (R := R) hExact₁ hExact₀
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
        · rw [HomologicalComplex.exactAt_iff' G (n + 2) (n + 1) n
            (by simp) (by simp)]
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
              simp [G, ChainComplex.of, δ, Nat.add_assoc]
            have hGd_right : G.d (n + 1) n = F.d (n + 2) (n + 1) := by
              simp [G, ChainComplex.of, δ, Nat.add_assoc]
            rw [hGd_left, hGd_right]
            exact hF_exact
          exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hG_exact
        · apply ChainComplex.exactAt_succ_single_obj
  refine ⟨G, κAug, ?_⟩
  refine ⟨?_, ?_⟩
  · -- The shifted tail remains a free resolution of the first syzygy.
    exact { toQuasiIso := hκAug_quasi, termwise_free := hGfree }
  · intro n hn
    -- Vanishing one degree higher in `F` becomes the required bound after shifting.
    simpa [G, X] using hF (n + 1) (Nat.succ_lt_succ hn)

/-- Helper for Lemma 10.109.5: a bounded free resolution can be truncated recursively to a bounded
finite projective resolution. -/
theorem hasFiniteProjectiveResolutionLengthLE_of_hasFreeResolutionLengthLE {d : ℕ}
    (hM : HasFreeResolutionLengthLE R M d) :
    HasFiniteProjectiveResolutionLengthLE (M := ModuleCat.of R M) d := by
  induction d generalizing M with
  | zero =>
      have hfree : Module.Free R M :=
        (hasFreeResolutionLengthLE_zero_iff (R := R) (M := M)).1 hM
      let _ : Module.Free R M := hfree
      simpa [HasFiniteProjectiveResolutionLengthLE] using
        (show Projective (ModuleCat.of R M) from inferInstance)
  | succ d ih =>
      rcases hM with ⟨F, π, hπ, hF⟩
      have hπ_surj : Function.Surjective (π.f 0).hom :=
        (ModuleCat.epi_iff_surjective _).mp
          (quasiIso_single_epi_zero (R := R) (N := M) (G := F) π)
      have hP₀proj : Projective (F.X 0) := by
        let _ : Module.Free R (F.X 0) := IsFreeResolution.free (R := R) (M := M) π 0
        infer_instance
      have hker :
          HasFiniteProjectiveResolutionLengthLE
            (M := ModuleCat.of R (LinearMap.ker (π.f 0).hom)) d := by
        have htail :
            HasFreeResolutionLengthLE R (LinearMap.ker (π.f 0).hom) d :=
          hasFreeResolutionLengthLE_kernel_of_witness_succ
            (R := R) (M := M) π hπ hF
        exact ih htail
      -- The initial free term is projective, and the kernel tail has the shorter bound.
      exact hasFiniteProjectiveResolutionLengthLE_succ_of_projective_presentation
        (M := ModuleCat.of R M) (π.f 0) hP₀proj hπ_surj hker

-- Proof sketch: combine Lemma `10.109.4`, which identifies `HasProjectiveDimensionLE` with the
-- existence of a finite projective resolution of length at most `d`, with Theorem `10.85.4`,
-- which says that projective modules over a local ring are free.
/-- Lemma 10.109.5: for a module over a local ring, having projective dimension at most `d` is
equivalent to admitting a free resolution of length at most `d`. Combined with Lemma `10.109.4`,
this says that the four equivalent conditions there are also equivalent to the existence of such a
free resolution. -/
theorem hasProjectiveDimensionLE_iff_hasFreeResolutionLengthLE (d : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R M) d ↔
      HasFreeResolutionLengthLE R M d := by
  constructor
  · intro hpd
    let P : ProjectiveResolution (ModuleCat.of R M) :=
      CategoryTheory.ProjectiveResolution.of (ModuleCat.of R M)
    have hsyz : P.SyzygyProjective d :=
      CategoryTheory.ProjectiveResolution.syzygyProjective_of_hasProjectiveDimensionLE
        (M := ModuleCat.of R M) (P := P) hpd
    have hfin :
        HasFiniteProjectiveResolutionLengthLE (M := ModuleCat.of R M) d :=
      CategoryTheory.ProjectiveResolution.hasFiniteProjectiveResolutionLengthLE_of_syzygyProjective
        (M := ModuleCat.of R M) (P := P) hsyz
    -- The forward direction is the source-faithful conversion of projective terms to free ones.
    exact hasFreeResolutionLengthLE_of_hasFiniteProjectiveResolutionLengthLE
      (R := R) (M := M) hfin
  · intro hfree
    have hfin :
        HasFiniteProjectiveResolutionLengthLE (M := ModuleCat.of R M) d :=
      hasFiniteProjectiveResolutionLengthLE_of_hasFreeResolutionLengthLE
        (R := R) (M := M) hfree
    -- Route correction: instead of reconstructing syzygies directly, truncate the bounded free
    -- resolution to a bounded projective one and invoke Lemma `10.109.4`.
    exact hasProjectiveDimensionLE_of_hasFiniteProjectiveResolutionLengthLE
      (M := ModuleCat.of R M) hfin

end
