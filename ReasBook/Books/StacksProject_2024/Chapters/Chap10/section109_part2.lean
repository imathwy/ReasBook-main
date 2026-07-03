import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_109_5 (from Chap10) -/
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

/-! ### Lemma_10_109_6 (from Chap10) -/
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

/-! ### Lemma_10_109_7 (from Chap10) -/
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

/-! ### Lemma_10_109_8 (from Chap10) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Abelian

universe u v

section

variable {R : Type u} [Ring R]

/-- Having projective dimension at most `n` is equivalent to vanishing of all higher `Ext`
groups above degree `n`. -/
-- Proof sketch: unfold `HasProjectiveDimensionLE M n` as
-- `HasProjectiveDimensionLT M (n + 1)` and rewrite with
-- `hasProjectiveDimensionLT_iff`.
theorem hasProjectiveDimensionLE_iff_ext_eq_zero_of_ge
    (M : ModuleCat.{max u v} R) (n : ℕ) :
    HasProjectiveDimensionLE M n ↔
      ∀ (N : ModuleCat.{max u v} R) (i : ℕ), n + 1 ≤ i → ∀ e : Ext M N i, e = 0 := by
  constructor
  · intro hM N i hi e
    letI : HasProjectiveDimensionLT M (n + 1) := hM
    exact Ext.eq_zero_of_hasProjectiveDimensionLT e (n + 1) hi
  · intro h
    rw [HasProjectiveDimensionLE, hasProjectiveDimensionLT_iff]
    intro i hi N e
    exact h N i hi e

/-- Having projective dimension at most `n` is equivalent to vanishing of `Ext^{n+1}(M, N)` for
every `R`-module `N`. -/
-- Proof sketch: one direction is the degree `n + 1` case of higher Ext-vanishing. For the
-- converse, use `hasProjectiveDimensionLT_of_enoughInjectives` in `ModuleCat R`, observing that
-- vanishing of all classes in degree `n + 1` makes each `Ext^{n+1}(M, N)` a subsingleton.
theorem hasProjectiveDimensionLE_iff_ext_eq_zero_at_succ
    (M : ModuleCat.{max u v} R) (n : ℕ) :
    HasProjectiveDimensionLE M n ↔
      ∀ N : ModuleCat.{max u v} R, ∀ e : Ext M N (n + 1), e = 0 := by
  constructor
  · intro hM N e
    letI : HasProjectiveDimensionLT M (n + 1) := hM
    exact Ext.eq_zero_of_hasProjectiveDimensionLT e (n + 1) (by rfl)
  · intro h
    exact hasProjectiveDimensionLT_of_enoughInjectives M (n + 1) fun N ↦
      ⟨fun e₁ e₂ ↦ by rw [h N e₁, h N e₂]⟩

/-- Lemma 10.109.8: for an `R`-module `M` and `n ≥ 0`, the following are equivalent:
`M` has projective dimension at most `n`, `Ext^i_R(M, N) = 0` for every `R`-module `N` and
every `i ≥ n + 1`, and `Ext^{n + 1}_R(M, N) = 0` for every `R`-module `N`. -/
-- Proof sketch: combine `hasProjectiveDimensionLE_iff_ext_eq_zero_of_ge` and
-- `hasProjectiveDimensionLE_iff_ext_eq_zero_at_succ`, then package the three pairwise
-- equivalent clauses as a `List.TFAE`.
theorem moduleCat_projectiveDimensionLE_ext_vanishing_tfae
    (M : ModuleCat.{max u v} R) (n : ℕ) :
    List.TFAE [
      HasProjectiveDimensionLE M n,
      ∀ (N : ModuleCat.{max u v} R) (i : ℕ), n + 1 ≤ i → ∀ e : Ext M N i, e = 0,
      ∀ N : ModuleCat.{max u v} R, ∀ e : Ext M N (n + 1), e = 0
    ] := by
  tfae_have 1 ↔ 2 := hasProjectiveDimensionLE_iff_ext_eq_zero_of_ge M n
  tfae_have 1 ↔ 3 := hasProjectiveDimensionLE_iff_ext_eq_zero_at_succ M n
  tfae_finish

end

/-! ### Lemma_10_109_9 (from Chap10) -/
universe u v

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

variable {R : Type u} [Ring R] {S : ShortComplex (ModuleCat.{v} R)}

/- Domain-style sampling:
* primary domain: projective dimension in the abelian category `ModuleCat R`, specialized to short
  exact sequences;
* sampled owner declarations:
  `HasProjectiveDimensionLE`,
  `HasProjectiveDimensionLT`,
  `ShortExact.hasProjectiveDimensionLT_X₁`,
  `ShortExact.hasProjectiveDimensionLT_X₂`,
  `ShortExact.hasProjectiveDimensionLT_X₃`;
* best owner abstraction: the canonical owner data is `hS : S.ShortExact`, and the `LT` lemmas are
  the core/canonical API;
* layer triage:
  the three `hasProjectiveDimensionLE_Xᵢ` theorems below are `bridge/view` declarations translating
  the source-facing `≤ n` formulation into the canonical `LT` owner lemmas;
* primitive data: `hS : S.ShortExact`;
* derived API: the `LE` bounds, obtained from the owner lemmas via
  `HasProjectiveDimensionLE X n = HasProjectiveDimensionLT X (n + 1)`.
-/

-- Proof sketch: rewrite the hypotheses and conclusion from `HasProjectiveDimensionLE` to
-- `HasProjectiveDimensionLT` using the successor shift, then apply the canonical short-exact
-- lemma `hS.hasProjectiveDimensionLT_X₁`.
/-- Lemma 10.109.9 (1): in a short exact sequence `0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` of `R`-modules, if the
middle term has projective dimension at most `n` and the cokernel has projective dimension at most
`n + 1`, then the kernel has projective dimension at most `n`. -/
theorem hasProjectiveDimensionLE_X₁ (hS : S.ShortExact) (n : ℕ)
    (h₂ : HasProjectiveDimensionLE S.X₂ n)
    (h₃ : HasProjectiveDimensionLE S.X₃ (n + 1)) :
    HasProjectiveDimensionLE S.X₁ n := by
  simpa [HasProjectiveDimensionLE] using hS.hasProjectiveDimensionLT_X₁ (n + 1) h₂ h₃

-- Proof sketch: convert both hypotheses and the conclusion to the corresponding
-- `HasProjectiveDimensionLT` bounds and apply the canonical short-exact lemma
-- `hS.hasProjectiveDimensionLT_X₂`.
/-- Lemma 10.109.9 (2): in a short exact sequence `0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` of `R`-modules, if the
kernel and cokernel both have projective dimension at most `n`, then the middle term has
projective dimension at most `n`. -/
theorem hasProjectiveDimensionLE_X₂ (hS : S.ShortExact) (n : ℕ)
    (h₁ : HasProjectiveDimensionLE S.X₁ n)
    (h₃ : HasProjectiveDimensionLE S.X₃ n) :
    HasProjectiveDimensionLE S.X₂ n := by
  simpa [HasProjectiveDimensionLE] using hS.hasProjectiveDimensionLT_X₂ (n + 1) h₁ h₃

-- Proof sketch: view `HasProjectiveDimensionLE S.X₁ n` as
-- `HasProjectiveDimensionLT S.X₁ (n + 1)` and `HasProjectiveDimensionLE S.X₂ (n + 1)` as
-- `HasProjectiveDimensionLT S.X₂ (n + 2)`, then apply `hS.hasProjectiveDimensionLT_X₃ (n + 1)`.
/-- Lemma 10.109.9 (3): in a short exact sequence `0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` of `R`-modules, if the
kernel has projective dimension at most `n` and the middle term has projective dimension at most
`n + 1`, then the cokernel has projective dimension at most `n + 1`. -/
theorem hasProjectiveDimensionLE_X₃ (hS : S.ShortExact) (n : ℕ)
    (h₁ : HasProjectiveDimensionLE S.X₁ n)
    (h₂ : HasProjectiveDimensionLE S.X₂ (n + 1)) :
    HasProjectiveDimensionLE S.X₃ (n + 1) := by
  simpa [HasProjectiveDimensionLE] using hS.hasProjectiveDimensionLT_X₃ (n + 1) h₁ h₂

end ShortExact
end ShortComplex
end CategoryTheory

/-! ### Definition_10_109_10 (from Chap10) -/
open CategoryTheory

universe u

section

variable (R : Type u) [Ring R]

/-- A ring has global dimension at most `n` if every `R`-module has projective dimension at
most `n`. -/
class HasGlobalDimensionLE (n : ℕ) : Prop where
  hasProjectiveDimensionLE (M : ModuleCat.{u} R) : HasProjectiveDimensionLE M n

/-- Definition 10.109.10: a ring has finite global dimension if there is an integer `n` such that
every `R`-module has projective dimension at most `n`, equivalently admits a projective
resolution of length at most `n`. -/
class IsFiniteGlobalDimensionRing : Prop where
  exists_bound : ∃ n : ℕ, HasGlobalDimensionLE R n

/-- A global-dimension bound on `R` induces the corresponding projective-dimension bound on every
`R`-module. -/
instance (n : ℕ) [HasGlobalDimensionLE R n] (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLE M n :=
  HasGlobalDimensionLE.hasProjectiveDimensionLE M

/-- The global dimension of a ring with finite global dimension is the least uniform bound on the
projective dimensions of its modules. -/
noncomputable def globalDimension [IsFiniteGlobalDimensionRing R] : ℕ :=
  sInf { n : ℕ | HasGlobalDimensionLE R n }

/-- The global dimension itself is a valid uniform bound on projective dimensions. -/
-- Proof sketch: the defining set of `globalDimension R` is the set of all admissible bounds;
-- finite global dimension gives nonemptiness, and `sInf` belongs to that set in `ℕ`.
theorem hasGlobalDimensionLE_globalDimension [IsFiniteGlobalDimensionRing R] :
    HasGlobalDimensionLE R (globalDimension R) := by
  refine Nat.sInf_mem ?_
  simpa [Set.nonempty_def] using
    (IsFiniteGlobalDimensionRing.exists_bound : ∃ n : ℕ, HasGlobalDimensionLE R n)

/-- A ring of finite global dimension has the canonical bound given by its global dimension. -/
noncomputable instance [IsFiniteGlobalDimensionRing R] :
    HasGlobalDimensionLE R (globalDimension R) :=
  hasGlobalDimensionLE_globalDimension R

/-- Any admissible bound on the projective dimensions of `R`-modules dominates the global
dimension. -/
-- Proof sketch: `globalDimension R` is the infimum of the set of all integers `n` such that
-- `HasGlobalDimensionLE R n`, so every member of that set is at least `globalDimension R`.
theorem globalDimension_le {n : ℕ} [IsFiniteGlobalDimensionRing R] [HasGlobalDimensionLE R n] :
    globalDimension R ≤ n := by
  exact Nat.sInf_le (show n ∈ {m : ℕ | HasGlobalDimensionLE R m} from ‹HasGlobalDimensionLE R n›)

end
