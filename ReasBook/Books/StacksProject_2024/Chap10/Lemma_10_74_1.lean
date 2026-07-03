import Mathlib
import StacksProject_2024.Chap10.Lemma_10_82_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open LinearMap
open scoped Pointwise

variable {R : Type u} [CommRing R]
variable {N : Type v} [AddCommGroup N] [Module R N]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R N] [Module.Finite R M]

-- Proof sketch: a splitting modulo `I ^ n` forces `ker f ⊆ I ^ n N`; since this happens for
-- arbitrarily large `n`, Lemma `10.51.5` gives `ker f = 0`, so `f` is injective. Passing to the
-- quotient `Q = M / f(N)`, the extension class of `0 → N → M → Q → 0` lies in `Ext¹_R(Q, N)`.
-- The split reductions modulo arbitrarily large powers force its image in every large
-- `Ext¹_R(Q / I ^ n Q, N / I ^ n N)` to vanish, and Lemma `10.51.5` again shows the original
-- class is zero. Therefore the short exact sequence splits, giving a retraction of `f`.
/-- Helper for Lemma 10.74.1: a retraction of the reduction of `f` modulo `I ^ n` forces every
kernel element of `f` to vanish modulo `I ^ n`. -/
lemma ker_le_pow_smul_of_split_quotient_retraction
    (I : Ideal R) (f : N →ₗ[R] M) (n : ℕ)
    (s : M ⧸ (I ^ n • (⊤ : Submodule R M)) →ₗ[R]
      N ⧸ (I ^ n • (⊤ : Submodule R N)))
    (hs : s.comp (f.quotientMapByIdeal (I ^ n)) = LinearMap.id) :
    LinearMap.ker f ≤ I ^ n • (⊤ : Submodule R N) := by
  intro x hx
  have hx0 : f x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  -- Apply the section identity to the class of `x` modulo `I ^ n`.
  have hquot : (I ^ n • (⊤ : Submodule R N)).mkQ x = 0 := by
    have hsec := LinearMap.congr_fun hs ((I ^ n • (⊤ : Submodule R N)).mkQ x)
    have hmap :
        (f.quotientMapByIdeal (I ^ n)) ((I ^ n • (⊤ : Submodule R N)).mkQ x) = 0 := by
      simp [LinearMap.quotientMapByIdeal, hx0]
    rw [LinearMap.comp_apply, LinearMap.id_apply, hmap] at hsec
    simpa using hsec.symm
  -- Triviality of the quotient class is exactly membership in `I ^ n N`.
  exact (Submodule.Quotient.mk_eq_zero _).mp hquot

/-- Helper for Lemma 10.74.1: if the reductions of `f` modulo arbitrarily large powers of `I`
split injectively, then `f` itself is injective by the `I`-adic Krull intersection theorem. -/
lemma injective_of_split_injective_mod_ideal_pow_frequently
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (f : N →ₗ[R] M)
    (hsplit :
      ∀ n₀ : ℕ, ∃ n ≥ n₀, ∃ s : M ⧸ (I ^ n • (⊤ : Submodule R M)) →ₗ[R]
          N ⧸ (I ^ n • (⊤ : Submodule R N)),
        s.comp (f.quotientMapByIdeal (I ^ n)) = LinearMap.id) :
    Function.Injective f := by
  -- Every kernel element lands in every `I ^ n N` because the split reductions occur cofinally.
  have hker_iInf : LinearMap.ker f ≤ ⨅ n : ℕ, I ^ n • (⊤ : Submodule R N) := by
    intro x hx
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨m, hmn, s, hs⟩ := hsplit n
    have hxmem : x ∈ I ^ m • (⊤ : Submodule R N) :=
      ker_le_pow_smul_of_split_quotient_retraction (I := I) (f := f) m s hs hx
    exact
      (Submodule.smul_mono (Ideal.pow_le_pow_right hmn)
        (show (⊤ : Submodule R N) ≤ ⊤ by rfl)) hxmem
  -- Lemma `10.51.5` identifies the `I`-adic intersection with zero for finite modules.
  have hIbot : I ≤ (⊥ : Ideal R).jacobson := by
    simpa [Ideal.jacobson_bot] using hI
  have hintersection :
      (⨅ n : ℕ, I ^ n • (⊤ : Submodule R N)) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I hIbot
  have hker_eq_bot : LinearMap.ker f = ⊥ := by
    refine le_antisymm ?_ bot_le
    simpa [hintersection] using hker_iInf
  exact LinearMap.ker_eq_bot.mp hker_eq_bot

/-- Helper for Lemma 10.74.1: coordinatewise `I ^ k`-divisibility on a finite product implies
the whole function is `I ^ k`-divisible. -/
lemma function_mem_pow_smul_top_of_coordinates
    (I : Ideal R) {k m : ℕ} (v : Fin m → N)
    (hv : ∀ i : Fin m, v i ∈ I ^ k • (⊤ : Submodule R N)) :
    v ∈ I ^ k • (⊤ : Submodule R (Fin m → N)) := by
  -- Bundle the coordinatewise hypothesis as membership in the product submodule.
  have hpi : v ∈ Submodule.pi Set.univ (fun _ : Fin m ↦ I ^ k • (⊤ : Submodule R N)) := by
    rw [Submodule.mem_pi]
    intro i hi
    exact hv i
  -- Rewrite the product submodule as the sum of the coordinate inclusions.
  rw [← Submodule.iSup_map_single
      (R := R) (ι := Fin m) (φ := fun _ : Fin m ↦ N)
      (p := fun _ : Fin m ↦ I ^ k • (⊤ : Submodule R N))] at hpi
  refine (show
      (⨆ i : Fin m,
        Submodule.map (LinearMap.single R (fun _ : Fin m ↦ N) i)
          (I ^ k • (⊤ : Submodule R N)))
        ≤ I ^ k • (⊤ : Submodule R (Fin m → N)) from ?_) hpi
  refine iSup_le fun i ↦ ?_
  -- Each coordinate inclusion preserves `I ^ k`-divisibility.
  rw [Submodule.map_smul'', Submodule.map_top]
  exact Submodule.smul_mono (show I ^ k ≤ I ^ k by rfl)
    (show LinearMap.range (LinearMap.single R (fun _ : Fin m ↦ N) i) ≤
        (⊤ : Submodule R (Fin m → N)) by simp)

/-- Helper for Lemma 10.74.1: a map out of the finite free module `R^m` lands in
`I ^ k Hom_R(R^m, N)` exactly when its values on the standard basis vectors land in `I ^ k N`. -/
lemma linearMap_mem_pow_smul_top_iff_on_pi_basis
    (I : Ideal R) {k m : ℕ} (u : (Fin m → R) →ₗ[R] N) :
    u ∈ I ^ k • (⊤ : Submodule R ((Fin m → R) →ₗ[R] N)) ↔
      ∀ i : Fin m, u (Pi.single i 1) ∈ I ^ k • (⊤ : Submodule R N) := by
  let e : ((Fin m → R) →ₗ[R] N) ≃ₗ[R] Fin m → N := LinearEquiv.piRing R N (Fin m) R
  constructor
  · intro hu i
    -- Transport the divisibility statement to the function model `Fin m → N`.
    have hu_fun : e u ∈ I ^ k • (⊤ : Submodule R (Fin m → N)) := by
      have hmap :
          e u ∈ Submodule.map e.toLinearMap
            (I ^ k • (⊤ : Submodule R ((Fin m → R) →ₗ[R] N))) :=
        Submodule.mem_map_of_mem hu
      simpa [e, Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using hmap
    -- Read off the `i`-th coordinate by induction on the `I ^ k`-multiple expression.
    have hcoord : e u i ∈ I ^ k • (⊤ : Submodule R N) := by
      refine Submodule.smul_induction_on hu_fun ?_ ?_
      · intro r hr x hx
        exact Submodule.smul_mem_smul hr (show x i ∈ (⊤ : Submodule R N) by simp)
      · intro x y hx hy
        exact Submodule.add_mem (I ^ k • (⊤ : Submodule R N)) hx hy
    simpa [e] using hcoord
  · intro hu
    -- Reassemble the coordinatewise divisibility statement in the function model.
    have hu_fun : e u ∈ I ^ k • (⊤ : Submodule R (Fin m → N)) := by
      refine function_mem_pow_smul_top_of_coordinates (I := I) (k := k) (v := e u) ?_
      intro i
      simpa [e] using hu i
    -- Transport the function-level divisibility statement back to the linear-map model.
    have hmap :
        e.symm (e u) ∈ Submodule.map e.symm.toLinearMap
          (I ^ k • (⊤ : Submodule R (Fin m → N))) :=
      Submodule.mem_map_of_mem hu_fun
    simpa [e, Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using hmap

/-- Helper for Lemma 10.74.1: quotienting the relation `f ∘ β = α ∘ d₁` and applying a chosen
section modulo `I ^ k` identifies the reduced obstruction map with the reduced correction map. -/
lemma reduced_obstruction_identity_of_split_mod
    (I : Ideal R) {m n k : ℕ}
    (f : N →ₗ[R] M)
    (d₁ : (Fin m → R) →ₗ[R] (Fin n → R))
    (α : (Fin n → R) →ₗ[R] M)
    (β : (Fin m → R) →ₗ[R] N)
    (hβ : f.comp β = α.comp d₁)
    (s : M ⧸ (I ^ k • (⊤ : Submodule R M)) →ₗ[R]
      N ⧸ (I ^ k • (⊤ : Submodule R N)))
    (hs : s.comp (f.quotientMapByIdeal (I ^ k)) = LinearMap.id) :
    β.quotientMapByIdeal (I ^ k) =
      (s.comp (α.quotientMapByIdeal (I ^ k))).comp (d₁.quotientMapByIdeal (I ^ k)) := by
  refine DFunLike.ext _ _ fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I ^ k • (⊤ : Submodule R (Fin m → R))) x
  -- Route correction: compare both reduced maps on representatives, then use the section
  -- identity on the class of `β y`.
  have hβy : f (β y) = α (d₁ y) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hβ y
  have hsec := LinearMap.congr_fun hs ((I ^ k • (⊤ : Submodule R N)).mkQ (β y))
  calc
    β.quotientMapByIdeal (I ^ k) ((I ^ k • (⊤ : Submodule R (Fin m → R))).mkQ y)
        = (I ^ k • (⊤ : Submodule R N)).mkQ (β y) := by
            rfl
    _ = s ((f.quotientMapByIdeal (I ^ k)) ((I ^ k • (⊤ : Submodule R N)).mkQ (β y))) := by
          simpa [LinearMap.comp_apply] using hsec.symm
    _ = s ((I ^ k • (⊤ : Submodule R M)).mkQ (f (β y))) := by
          rfl
    _ = s ((I ^ k • (⊤ : Submodule R M)).mkQ (α (d₁ y))) := by
          rw [hβy]
    _ =
        ((s.comp (α.quotientMapByIdeal (I ^ k))).comp
          (d₁.quotientMapByIdeal (I ^ k)))
            ((I ^ k • (⊤ : Submodule R (Fin m → R))).mkQ y) := by
              rfl

/-- Helper for Lemma 10.74.1: the reduced correction map from the quotient of a finite free
module lifts through the quotient map `N → N / I ^ k N`. -/
lemma free_lift_of_reduced_correction_through_mkQ
    (I : Ideal R) {n k : ℕ}
    (γbar : ((Fin n → R) ⧸ (I ^ k • (⊤ : Submodule R (Fin n → R)))) →ₗ[R]
      N ⧸ (I ^ k • (⊤ : Submodule R N))) :
    ∃ γ : (Fin n → R) →ₗ[R] N,
      ((I ^ k • (⊤ : Submodule R N)).mkQ).comp γ =
        γbar.comp ((I ^ k • (⊤ : Submodule R (Fin n → R))).mkQ) := by
  let τ : (Fin n → R) →ₗ[R] N ⧸ (I ^ k • (⊤ : Submodule R N)) :=
    γbar.comp ((I ^ k • (⊤ : Submodule R (Fin n → R))).mkQ)
  -- Lift the quotient-valued correction from the free module before quotienting the domain.
  obtain ⟨γ, hγ⟩ :=
    Module.projective_lifting_property ((I ^ k • (⊤ : Submodule R N)).mkQ) τ
      (Submodule.mkQ_surjective _)
  exact ⟨γ, hγ⟩

/-- Helper for Lemma 10.74.1: if the reduction of `f` modulo `I ^ k` has a left inverse, then
any relation `f ∘ β = α ∘ d₁` can be corrected by a map `γ` so that the remaining defect lands in
`I ^ k Hom_R(R^m, N)`. -/
lemma obstruction_map_mem_range_add_pow_smul_of_split_mod
    (I : Ideal R) {m n k : ℕ}
    (f : N →ₗ[R] M)
    (d₁ : (Fin m → R) →ₗ[R] (Fin n → R))
    (α : (Fin n → R) →ₗ[R] M)
    (β : (Fin m → R) →ₗ[R] N)
    (hβ : f.comp β = α.comp d₁)
    (s : M ⧸ (I ^ k • (⊤ : Submodule R M)) →ₗ[R]
      N ⧸ (I ^ k • (⊤ : Submodule R N)))
    (hs : s.comp (f.quotientMapByIdeal (I ^ k)) = LinearMap.id) :
    ∃ γ : (Fin n → R) →ₗ[R] N,
      β - γ.comp d₁ ∈ I ^ k • (⊤ : Submodule R ((Fin m → R) →ₗ[R] N)) := by
  -- Route correction: the quotient identity and free lifting step are now isolated in
  -- `reduced_obstruction_identity_of_split_mod` and
  -- `free_lift_of_reduced_correction_through_mkQ`.
  let γbar :
      ((Fin n → R) ⧸ (I ^ k • (⊤ : Submodule R (Fin n → R)))) →ₗ[R]
        N ⧸ (I ^ k • (⊤ : Submodule R N)) :=
    s.comp (α.quotientMapByIdeal (I ^ k))
  obtain ⟨γ, hγ⟩ :=
    free_lift_of_reduced_correction_through_mkQ (I := I) (k := k) (γbar := γbar)
  refine ⟨γ, (linearMap_mem_pow_smul_top_iff_on_pi_basis (I := I) (k := k)
    (u := β - γ.comp d₁)).2 ?_⟩
  intro i
  -- Compare the two reduced corrections on the `i`-th basis vector of `R^m`.
  have hβred :
      (I ^ k • (⊤ : Submodule R N)).mkQ (β (Pi.single i 1)) =
        γbar ((I ^ k • (⊤ : Submodule R (Fin n → R))).mkQ (d₁ (Pi.single i 1))) := by
    simpa [γbar, LinearMap.quotientMapByIdeal, LinearMap.comp_apply] using
      LinearMap.congr_fun
        (reduced_obstruction_identity_of_split_mod (I := I) (f := f) (d₁ := d₁)
          (α := α) (β := β) hβ s hs)
        ((I ^ k • (⊤ : Submodule R (Fin m → R))).mkQ (Pi.single i 1))
  have hγred :
      (I ^ k • (⊤ : Submodule R N)).mkQ (γ (d₁ (Pi.single i 1))) =
        γbar ((I ^ k • (⊤ : Submodule R (Fin n → R))).mkQ (d₁ (Pi.single i 1))) := by
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun hγ (d₁ (Pi.single i 1))
  -- Zero quotient class is equivalent to membership in `I ^ k N`.
  have hdefect_zero :
      (I ^ k • (⊤ : Submodule R N)).mkQ ((β - γ.comp d₁) (Pi.single i 1)) = 0 := by
    calc
      (I ^ k • (⊤ : Submodule R N)).mkQ ((β - γ.comp d₁) (Pi.single i 1))
          = (I ^ k • (⊤ : Submodule R N)).mkQ (β (Pi.single i 1)) -
              (I ^ k • (⊤ : Submodule R N)).mkQ (γ (d₁ (Pi.single i 1))) := by
                simp [LinearMap.comp_apply, map_sub]
      _ = 0 := by rw [hβred, hγred, sub_self]
  exact (Submodule.Quotient.mk_eq_zero _).mp hdefect_zero

/-- Helper for Lemma 10.74.1: an element of a finite module that lies in arbitrarily high
`I`-powers must vanish when `I` lies in the Jacobson radical. -/
lemma eventually_mem_pow_smul_top_eq_zero
    {C : Type*} [AddCommGroup C] [Module R C] [Module.Finite R C]
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (c : C)
    (hc : ∀ n₀ : ℕ, ∃ n ≥ n₀, c ∈ I ^ n • (⊤ : Submodule R C)) :
    c = 0 := by
  -- Membership in every sufficiently large `I ^ n C` upgrades to membership in the full `I`-adic
  -- intersection, which is zero by Lemma `10.51.5`.
  have hmem : c ∈ ⨅ n : ℕ, I ^ n • (⊤ : Submodule R C) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨m, hmn, hcm⟩ := hc n
    exact
      (Submodule.smul_mono (Ideal.pow_le_pow_right hmn)
        (show (⊤ : Submodule R C) ≤ ⊤ by rfl)) hcm
  have hIbot : I ≤ (⊥ : Ideal R).jacobson := by
    simpa [Ideal.jacobson_bot] using hI
  have hintersection :
      (⨅ n : ℕ, I ^ n • (⊤ : Submodule R C)) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I hIbot
  have hzero : c ∈ (⊥ : Submodule R C) := by
    simpa [hintersection] using hmem
  simpa using hzero

/-- Helper for Lemma 10.74.1: if the obstruction representative `β` can be corrected modulo
arbitrarily large powers of `I`, then its class in the cokernel of precomposition by `d₁`
vanishes, so `β` already lies in the range of precomposition. -/
lemma obstruction_class_zero_of_frequently_pow_divisible
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) {m n : ℕ}
    (d₁ : (Fin m → R) →ₗ[R] (Fin n → R))
    (β : (Fin m → R) →ₗ[R] N)
    (hβpow :
      ∀ n₀ : ℕ, ∃ k ≥ n₀, ∃ γ : (Fin n → R) →ₗ[R] N,
        β - γ.comp d₁ ∈ I ^ k • (⊤ : Submodule R ((Fin m → R) →ₗ[R] N))) :
    ∃ γ : (Fin n → R) →ₗ[R] N, β = γ.comp d₁ := by
  let precomp_d₁ : ((Fin n → R) →ₗ[R] N) →ₗ[R] ((Fin m → R) →ₗ[R] N) :=
    { toFun := fun γ ↦ γ.comp d₁
      map_add' := by
        intro γ₁ γ₂
        rfl
      map_smul' := by
        intro r γ
        rfl }
  let q : ((Fin m → R) →ₗ[R] N) →ₗ[R]
      (((Fin m → R) →ₗ[R] N) ⧸ LinearMap.range precomp_d₁) :=
    (LinearMap.range precomp_d₁).mkQ
  letI : Module.Finite R (((Fin m → R) →ₗ[R] N) ⧸ LinearMap.range precomp_d₁) :=
    Module.Finite.of_surjective q (Submodule.mkQ_surjective _)
  have hc :
      ∀ n₀ : ℕ, ∃ k ≥ n₀, q β ∈
        I ^ k • (⊤ : Submodule R (((Fin m → R) →ₗ[R] N) ⧸ LinearMap.range precomp_d₁)) := by
    intro n₀
    obtain ⟨k, hk, γ, hγ⟩ := hβpow n₀
    refine ⟨k, hk, ?_⟩
    have hq_mem_range :
        q (γ.comp d₁) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨γ, rfl⟩
    have hq_defect :
        q (β - γ.comp d₁) ∈
          I ^ k • (⊤ : Submodule R (((Fin m → R) →ₗ[R] N) ⧸ LinearMap.range precomp_d₁)) := by
      have hmap :
          q (β - γ.comp d₁) ∈
            Submodule.map q (I ^ k • (⊤ : Submodule R ((Fin m → R) →ₗ[R] N))) :=
        Submodule.mem_map_of_mem hγ
      rw [Submodule.map_smul'', Submodule.map_top] at hmap
      exact
        (Submodule.smul_mono (show I ^ k ≤ I ^ k by rfl)
          (show LinearMap.range q ≤
              (⊤ : Submodule R (((Fin m → R) →ₗ[R] N) ⧸ LinearMap.range precomp_d₁)) by
            simp)) hmap
    rw [show q β = q (β - γ.comp d₁) by
      rw [map_sub, hq_mem_range, sub_zero]]
    exact hq_defect
  have hzero : q β = 0 :=
    eventually_mem_pow_smul_top_eq_zero (I := I) hI (c := q β) hc
  rcases (Submodule.Quotient.mk_eq_zero _).mp hzero with ⟨γ, hγ⟩
  exact ⟨γ, by simpa [precomp_d₁] using hγ.symm⟩

/-- Helper for Lemma 10.74.1: the cokernel `M / range(f)` admits a canonical finite free
presentation because it is a finite module over a Noetherian ring. -/
lemma finite_cokernel_presentation
    (f : N →ₗ[R] M) :
    ∃ m n : ℕ, ∃ K : Submodule R (Fin n → R),
      ∃ e : (M ⧸ LinearMap.range f) ≃ₗ[R] ((Fin n → R) ⧸ K),
        ∃ d₁ : (Fin m → R) →ₗ[R] (Fin n → R), LinearMap.range d₁ = K := by
  let q : M →ₗ[R] (M ⧸ LinearMap.range f) := (LinearMap.range f).mkQ
  letI : Module.Finite R (M ⧸ LinearMap.range f) :=
    Module.Finite.of_surjective q (Submodule.mkQ_surjective _)
  letI : Module.FinitePresentation R (M ⧸ LinearMap.range f) :=
    Module.finitePresentation_of_finite R (M ⧸ LinearMap.range f)
  -- First realize the cokernel as a quotient of a finite free module.
  obtain ⟨n, K, e, hKfg⟩ := Module.FinitePresentation.exists_fin R (M ⧸ LinearMap.range f)
  -- Then realize the presented submodule `K` as the range of a finite free map.
  obtain ⟨m, d₁, hd₁⟩ :=
    (Submodule.fg_iff_exists_fin_linearMap R (Fin n → R)).mp hKfg
  exact ⟨m, n, K, e, d₁, hd₁⟩

/-- Helper for Lemma 10.74.1: the presentation map `F₀ → M / range(f)` lifts to a map
`F₀ → M` because the finite free module `F₀` is projective. -/
lemma lift_cokernel_presentation_map
    {n : ℕ} (f : N →ₗ[R] M)
    (K : Submodule R (Fin n → R))
    (e : (M ⧸ LinearMap.range f) ≃ₗ[R] ((Fin n → R) ⧸ K)) :
    ∃ α : (Fin n → R) →ₗ[R] M,
      (LinearMap.range f).mkQ.comp α =
        e.symm.toLinearMap.comp (Submodule.mkQ K) := by
  let π : (Fin n → R) →ₗ[R] M ⧸ LinearMap.range f :=
    e.symm.toLinearMap.comp (Submodule.mkQ K)
  -- Lift the quotient presentation map through the cokernel quotient.
  obtain ⟨α, hα⟩ :=
    Module.projective_lifting_property ((LinearMap.range f).mkQ) π
      (Submodule.mkQ_surjective _)
  exact ⟨α, hα⟩

/-- Helper for Lemma 10.74.1: if `ψ ∘ d₁ = 0`, then `ψ` factors through the quotient by the
presented submodule `K`. -/
lemma presentation_descend_of_comp_eq_zero
    {m n : ℕ} (K : Submodule R (Fin n → R))
    (d₁ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hd₁ : LinearMap.range d₁ = K)
    (ψ : (Fin n → R) →ₗ[R] M)
    (hψ : ψ.comp d₁ = 0) :
    ∃ ψK : ((Fin n → R) ⧸ K) →ₗ[R] M,
      ψK.comp (Submodule.mkQ K) = ψ := by
  -- Route correction: descend through `range d₁` first, and only then transport across `hd₁`.
  have hrange_le_ker : LinearMap.range d₁ ≤ LinearMap.ker ψ := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hψ y
  let ψrange : ((Fin n → R) ⧸ LinearMap.range d₁) →ₗ[R] M :=
    (LinearMap.range d₁).liftQ ψ hrange_le_ker
  let e : ((Fin n → R) ⧸ K) →ₗ[R] ((Fin n → R) ⧸ LinearMap.range d₁) :=
    (Submodule.quotEquivOfEq K (LinearMap.range d₁) hd₁.symm).toLinearMap
  refine ⟨ψrange.comp e, ?_⟩
  -- The descended map agrees with `ψ` on representatives by the defining quotient formulas.
  ext x
  simp [ψrange, e, LinearMap.comp_apply]

/-- Helper for Lemma 10.74.1: if a map into `M` becomes zero in `M / range(f)`, then it factors
through `f` once `f` is known to be injective. -/
lemma lift_relation_through_range_of_cokernel
    {m : ℕ} (f : N →ₗ[R] M) (hf : Function.Injective f)
    (ψ : (Fin m → R) →ₗ[R] M)
    (hzero : (LinearMap.range f).mkQ.comp ψ = 0) :
    ∃ β : (Fin m → R) →ₗ[R] N, f.comp β = ψ := by
  have hmem : ∀ x, ψ x ∈ LinearMap.range f := by
    intro x
    have hx_zero : (LinearMap.range f).mkQ (ψ x) = 0 := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hzero x
    exact (Submodule.Quotient.mk_eq_zero _).mp hx_zero
  let ψR : (Fin m → R) →ₗ[R] LinearMap.range f :=
    ψ.codRestrict (LinearMap.range f) hmem
  let eRange : N ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hf
  refine ⟨eRange.symm.toLinearMap.comp ψR, ?_⟩
  -- Pull the range-valued factorization back along the equivalence `N ≃ range(f)`.
  ext x
  simpa [ψR, eRange, LinearMap.comp_apply] using
    congrArg Subtype.val (eRange.apply_symm_apply (ψR x))

/-- Helper for Lemma 10.74.1: once the obstruction representative is actually a boundary, the
presented quotient descends to a section of the cokernel map `M → M / range(f)`. -/
lemma exists_cokernel_section_of_obstruction_zero
    {m n : ℕ}
    (f : N →ₗ[R] M)
    (K : Submodule R (Fin n → R))
    (e : (M ⧸ LinearMap.range f) ≃ₗ[R] ((Fin n → R) ⧸ K))
    (d₁ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hd₁ : LinearMap.range d₁ = K)
    (α : (Fin n → R) →ₗ[R] M)
    (β : (Fin m → R) →ₗ[R] N)
    (hα :
      (LinearMap.range f).mkQ.comp α =
        e.symm.toLinearMap.comp (Submodule.mkQ K))
    (hβ : f.comp β = α.comp d₁)
    (hγ : ∃ γ : (Fin n → R) →ₗ[R] N, β = γ.comp d₁) :
    ∃ δ : M ⧸ LinearMap.range f →ₗ[R] M,
      (LinearMap.range f).mkQ.comp δ = LinearMap.id := by
  let q : M →ₗ[R] M ⧸ LinearMap.range f := (LinearMap.range f).mkQ
  obtain ⟨γ, hγ⟩ := hγ
  -- The corrected lift `α - f ∘ γ` vanishes on the relations `d₁`.
  have hcomp_zero : (α - f.comp γ).comp d₁ = 0 := by
    refine DFunLike.ext _ _ fun x ↦ ?_
    have hβx : f (β x) = α (d₁ x) := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hβ x
    have hγx : β x = γ (d₁ x) := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hγ x
    calc
      ((α - f.comp γ).comp d₁) x = α (d₁ x) - f (γ (d₁ x)) := by
        simp [LinearMap.comp_apply]
      _ = f (β x) - f (β x) := by rw [← hβx, hγx]
      _ = 0 := sub_self _
  obtain ⟨ψK, hψK⟩ :=
    presentation_descend_of_comp_eq_zero (K := K) (d₁ := d₁) hd₁ (α - f.comp γ) hcomp_zero
  -- The `f ∘ γ` part dies in the cokernel, so the descended map becomes a section.
  have hqfγ : q.comp (f.comp γ) = 0 := by
    refine DFunLike.ext _ _ fun x ↦ ?_
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨γ x, by simp [LinearMap.comp_apply]⟩
  have hqψK : q.comp ψK = e.symm.toLinearMap := by
    refine DFunLike.ext _ _ fun x ↦ ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective K x
    have hψKy : ψK ((Submodule.mkQ K) y) = (α - f.comp γ) y := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hψK y
    calc
      (q.comp ψK) ((Submodule.mkQ K) y)
          = q ((α - f.comp γ) y) := by
              simpa [LinearMap.comp_apply] using congrArg q hψKy
      _ = q (α y) - q ((f.comp γ) y) := by
            simp [q, LinearMap.comp_apply, map_sub]
      _ = q (α y) := by
            have hqfγy : q ((f.comp γ) y) = 0 := by
              simpa [LinearMap.comp_apply] using LinearMap.congr_fun hqfγ y
            rw [hqfγy, sub_zero]
      _ = e.symm ((Submodule.mkQ K) y) := by
            simpa [q, LinearMap.comp_apply] using LinearMap.congr_fun hα y
      _ = e.symm.toLinearMap ((Submodule.mkQ K) y) := rfl
  let δ : M ⧸ LinearMap.range f →ₗ[R] M := ψK.comp e.toLinearMap
  refine ⟨δ, ?_⟩
  -- Compose the descended map with the quotient equivalence to get the desired section.
  refine DFunLike.ext _ _ fun x ↦ ?_
  calc
    ((LinearMap.range f).mkQ.comp δ) x = q (ψK (e x)) := rfl
    _ = e.symm.toLinearMap (e x) := by
          simpa [δ, q, LinearMap.comp_apply] using LinearMap.congr_fun hqψK (e x)
    _ = x := by simp

/-- Helper for Lemma 10.74.1: each split reduction modulo `I ^ k` produces a correction of the
obstruction representative modulo `I ^ k`. -/
lemma frequent_pow_corrections_from_split_sections
    (I : Ideal R) {m n : ℕ}
    (f : N →ₗ[R] M)
    (d₁ : (Fin m → R) →ₗ[R] (Fin n → R))
    (α : (Fin n → R) →ₗ[R] M)
    (β : (Fin m → R) →ₗ[R] N)
    (hβ : f.comp β = α.comp d₁)
    (hsplit :
      ∀ n₀ : ℕ, ∃ k ≥ n₀, ∃ s : M ⧸ (I ^ k • (⊤ : Submodule R M)) →ₗ[R]
          N ⧸ (I ^ k • (⊤ : Submodule R N)),
        s.comp (f.quotientMapByIdeal (I ^ k)) = LinearMap.id) :
    ∀ n₀ : ℕ, ∃ k ≥ n₀, ∃ γ : (Fin n → R) →ₗ[R] N,
      β - γ.comp d₁ ∈ I ^ k • (⊤ : Submodule R ((Fin m → R) →ₗ[R] N)) := by
  intro n₀
  obtain ⟨k, hk, s, hs⟩ := hsplit n₀
  -- Apply the modulo-`I ^ k` splitting to kill the obstruction representative at level `k`.
  obtain ⟨γ, hγ⟩ :=
    obstruction_map_mem_range_add_pow_smul_of_split_mod (I := I) (f := f) (d₁ := d₁)
      (α := α) (β := β) hβ s hs
  exact ⟨k, hk, γ, hγ⟩

/-- Helper for Lemma 10.74.1: a section of the cokernel quotient of an injective map yields a
linear retraction of the original map. -/
lemma retraction_of_cokernel_section
    (f : N →ₗ[R] M) (hf : Function.Injective f)
    (δ : M ⧸ LinearMap.range f →ₗ[R] M)
    (hδ : (LinearMap.range f).mkQ.comp δ = LinearMap.id) :
    ∃ s : M →ₗ[R] N, s.comp f = LinearMap.id := by
  let q : M →ₗ[R] M ⧸ LinearMap.range f := (LinearMap.range f).mkQ
  let g : M →ₗ[R] M := LinearMap.id - δ.comp q
  -- The difference `id_M - δ ∘ q` lands in `range f` because its cokernel class vanishes.
  have hg_zero : q.comp g = 0 := by
    ext x
    have hδx : q (δ (q x)) = q x := by
      simpa [q, LinearMap.comp_apply] using LinearMap.congr_fun hδ (q x)
    simp only [q, g, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.zero_apply]
    rw [map_sub, hδx, sub_self]
  have hg_mem : ∀ x, g x ∈ LinearMap.range f := by
    intro x
    have hx_zero : q (g x) = 0 := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hg_zero x
    exact (Submodule.Quotient.mk_eq_zero _).mp hx_zero
  let p : M →ₗ[R] LinearMap.range f := g.codRestrict (LinearMap.range f) hg_mem
  let e : N ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hf
  refine ⟨e.symm.toLinearMap.comp p, ?_⟩
  -- On `range f`, the projection is the identity, so pulling back gives the desired retraction.
  ext x
  change e.symm (p (f x)) = x
  have hqfx : q (f x) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩
  have hp_val : ((p (f x) : LinearMap.range f) : M) = f x := by
    simp [p, g, q, LinearMap.comp_apply, hqfx]
  have hp_apply : p (f x) = e x := by
    apply Subtype.ext
    calc
      ((p (f x) : LinearMap.range f) : M) = f x := hp_val
      _ = ((e x : LinearMap.range f) : M) := rfl
  rw [hp_apply]
  exact e.symm_apply_apply x

/-- Lemma 10.74.1: if a linear map of finite modules over a Noetherian ring becomes split
injective modulo `I ^ n` for arbitrarily large `n`, where `I` lies in the Jacobson radical, then
the original map has a linear retraction and is therefore split injective. -/
theorem exists_retraction_of_split_injective_mod_ideal_pow_frequently
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (f : N →ₗ[R] M)
    (hsplit :
      ∀ n₀ : ℕ, ∃ n ≥ n₀, ∃ s : M ⧸ (I ^ n • (⊤ : Submodule R M)) →ₗ[R]
          N ⧸ (I ^ n • (⊤ : Submodule R N)),
        s.comp (f.quotientMapByIdeal (I ^ n)) = LinearMap.id) :
    ∃ s : M →ₗ[R] N, s.comp f = LinearMap.id := by
  -- First recover the injectivity asserted in the source proof from the repeated split reductions.
  have hf : Function.Injective f :=
    injective_of_split_injective_mod_ideal_pow_frequently (I := I) hI f hsplit
  obtain ⟨m, n, K, e, d₁, hd₁⟩ := finite_cokernel_presentation (R := R) (N := N) (M := M) f
  let π : (Fin n → R) →ₗ[R] M ⧸ LinearMap.range f :=
    e.symm.toLinearMap.comp (Submodule.mkQ K)
  have hmkQ_d₁ : (Submodule.mkQ K).comp d₁ = 0 := by
    -- The presentation relations lie in `K = range d₁`, so the quotient map kills them.
    refine DFunLike.ext _ _ fun x ↦ ?_
    exact (Submodule.Quotient.mk_eq_zero K).mpr <| by
      rw [← hd₁]
      exact ⟨x, rfl⟩
  have hπ : π.comp d₁ = 0 := by
    -- Transport the vanishing of `mkQ K ∘ d₁` across the quotient equivalence.
    refine DFunLike.ext _ _ fun x ↦ ?_
    have hx : (Submodule.mkQ K) (d₁ x) = 0 := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun hmkQ_d₁ x
    calc
      (π.comp d₁) x = e.symm ((Submodule.mkQ K) (d₁ x)) := rfl
      _ = e.symm 0 := by rw [hx]
      _ = 0 := by simp
  obtain ⟨α, hα⟩ := lift_cokernel_presentation_map (f := f) (K := K) (e := e)
  have hqd₁ : (LinearMap.range f).mkQ.comp (α.comp d₁) = 0 := by
    -- The lifted presentation map still kills the relations after composing with the cokernel.
    refine DFunLike.ext _ _ fun x ↦ ?_
    calc
      ((LinearMap.range f).mkQ.comp (α.comp d₁)) x = ((LinearMap.range f).mkQ.comp α) (d₁ x) := rfl
      _ = π (d₁ x) := by
            simpa [LinearMap.comp_apply] using LinearMap.congr_fun hα (d₁ x)
      _ = 0 := by
            simpa [LinearMap.comp_apply] using LinearMap.congr_fun hπ x
  obtain ⟨β, hβ⟩ :=
    lift_relation_through_range_of_cokernel (f := f) hf (ψ := α.comp d₁) hqd₁
  have hβpow :
      ∀ n₀ : ℕ, ∃ k ≥ n₀, ∃ γ : (Fin n → R) →ₗ[R] N,
        β - γ.comp d₁ ∈ I ^ k • (⊤ : Submodule R ((Fin m → R) →ₗ[R] N)) :=
    frequent_pow_corrections_from_split_sections (I := I) (f := f) (d₁ := d₁)
      (α := α) (β := β) hβ hsplit
  obtain ⟨γ, hγ⟩ :=
    obstruction_class_zero_of_frequently_pow_divisible (I := I) hI d₁ β hβpow
  obtain ⟨δ, hδ⟩ :=
    exists_cokernel_section_of_obstruction_zero (f := f) (K := K) (e := e) (d₁ := d₁)
      hd₁ α β hα hβ ⟨γ, hγ⟩
  exact retraction_of_cokernel_section (f := f) hf δ hδ

end
