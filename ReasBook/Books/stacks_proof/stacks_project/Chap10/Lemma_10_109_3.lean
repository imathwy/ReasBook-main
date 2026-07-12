import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v

open CategoryTheory

/-
Domain-style sampling:
* primary domain: projective dimension in `ModuleCat`, short exact complexes, and projective
  syzygies.
* inspected owner declarations:
  `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`,
  `CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero`,
  `LinearMap.shortComplexKer`, and `LinearMap.shortExact_shortComplexKer`.
* best owner abstraction: a short exact complex `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with projective middle
  term; a kernel `LinearMap.ker π` is a bridge/view via `LinearMap.shortComplexKer π`.
* layer triage:
  the short-exact corollary below is `core/canonical`,
  `projective_ker_of_surjective_of_hasProjectiveDimensionLE_one` is `bridge/view`,
  and the finite exact-sequence statement remains `source-facing`.
* primitive data: the short exact owner object and the projective-dimension bound on its cokernel.
* derived API: projectivity of the kernel / top syzygy.
-/

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

section

variable {R : Type v} [Ring R]
variable {S : ShortComplex (ModuleCat.{v} R)}

/-- In a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `R`-modules with `X₂` projective, if
`X₃` has projective dimension at most `1`, then `X₁` is projective. This is the `n = 0`
specialization of the canonical owner theorem
`ShortExact.hasProjectiveDimensionLT_X₃_iff`. -/
theorem projective_X₁_of_projective_X₂_of_hasProjectiveDimensionLE_one
    (hS : S.ShortExact) [Projective S.X₂] (hpd : HasProjectiveDimensionLE S.X₃ 1) :
    Projective S.X₁ := by
  -- We rewrite projectivity of `X₁` as projective dimension `≤ 0`.
  rw [projective_iff_hasProjectiveDimensionLE_zero]
  -- The short-exact owner theorem shifts the projective-dimension bound from `X₃` to `X₁`.
  simpa [HasProjectiveDimensionLE] using
    (hS.hasProjectiveDimensionLT_X₃_iff 0 inferInstance).mp (by
      simpa [HasProjectiveDimensionLE] using hpd)

end

end ShortExact
end ShortComplex
end CategoryTheory

section

variable {R : Type v} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.109.3: categorical projectivity of `ModuleCat.of R P` gives the usual
module-theoretic projectivity of `P`. -/
lemma module_projective_of_categorical_projective
    {P : Type v} [AddCommGroup P] [Module R P]
    (hP : Projective (ModuleCat.of R P)) :
    Module.Projective R P := by
  -- We convert categorical factorisations through epis into lifts through surjective linear maps.
  let _ : Small.{v} R := small_self R
  refine Module.Projective.of_lifting_property ?_
  intro A B _ _ _ _ f g hf
  let _ : Projective (ModuleCat.of R P) := hP
  have hf' : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  refine ⟨(Projective.factorThru (ModuleCat.ofHom g) (ModuleCat.ofHom f)).hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom
    (Projective.factorThru_comp (ModuleCat.ofHom g) (ModuleCat.ofHom f))

/-- Helper for Lemma 10.109.3: the first syzygy of a surjection from a projective module lowers
the projective-dimension bound by one. -/
lemma hasProjectiveDimensionLE_first_syzygy_of_surjective
    {F₀ : Type v} [AddCommGroup F₀] [Module R F₀]
    (π : F₀ →ₗ[R] M) (hπ : Function.Surjective π)
    [Module.Projective R F₀] {n : ℕ}
    (hpd : HasProjectiveDimensionLE (ModuleCat.of R M) (n + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) n := by
  let S : ShortComplex (ModuleCat.{v} R) := LinearMap.shortComplexKer π
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hπ
  -- The owner theorem equates the shifted bounds on the cokernel and the kernel.
  simpa [S, HasProjectiveDimensionLE] using
    (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp (by
      simpa [HasProjectiveDimensionLE] using hpd)

/-- Lemma 10.109.3 (1): if `F₀ ⟶ M ⟶ 0` is exact with `F₀` projective and `M` has projective
dimension at most `1`, then `ker(F₀ ⟶ M)` is projective. This is the `e = 0` case of the
textbook lemma, phrased in terms of the equivalent upper-bound condition on projective
dimension. The raw-kernel formulation is the bridge obtained from the owner theorem
`CategoryTheory.ShortComplex.ShortExact.projective_X₁_of_projective_X₂_of_hasProjectiveDimensionLE_one`
by applying it to `LinearMap.shortComplexKer π`. -/
-- Proof sketch: package `π` as the short exact complex
-- `0 ⟶ ker π ⟶ F₀ ⟶ M ⟶ 0`, apply the owner theorem in
-- `CategoryTheory.ShortComplex.ShortExact`, and then identify the left term with the module
-- `LinearMap.ker π`.
@[stacks 00O5]
theorem projective_ker_of_surjective_of_hasProjectiveDimensionLE_one
    {F₀ : Type v}
    [AddCommGroup F₀] [Module R F₀]
    (π : F₀ →ₗ[R] M) (hπ : Function.Surjective π)
    [Module.Projective R F₀]
    (hpd : HasProjectiveDimensionLE (ModuleCat.of R M) 1) :
    Module.Projective R (LinearMap.ker π) := by
  have hproj_cat : Projective (ModuleCat.of R (LinearMap.ker π)) := by
    -- We package `π` into the canonical short exact sequence
    -- `0 ⟶ ker π ⟶ F₀ ⟶ M ⟶ 0`.
    simpa [LinearMap.shortComplexKer] using
      CategoryTheory.ShortComplex.ShortExact.projective_X₁_of_projective_X₂_of_hasProjectiveDimensionLE_one
        (R := R) (S := LinearMap.shortComplexKer π)
        (LinearMap.shortExact_shortComplexKer hπ) hpd
  -- Finally we translate categorical projectivity back to the module-theoretic statement.
  exact module_projective_of_categorical_projective (R := R) hproj_cat

/-- Lemma 10.109.3 (2): if
`F_{e+1} ⟶ F_e ⟶ ⋯ ⟶ F₀ ⟶ M ⟶ 0`
is exact, every `Fᵢ` is projective, and `M` has projective dimension at most `e + 1`, then the
kernel of the top differential `F_{e+1} ⟶ F_e` is projective. This is the canonical upper-bound
reformulation of the textbook hypothesis `e ≥ d - 1` when `M` has projective dimension `d`. -/
-- Proof sketch: prove the statement by induction on `e`. The case `e = 0` is part (1). For the
-- inductive step, replace `M` by the first syzygy `ker(F₀ ⟶ M)`, use the canonical short-exact
-- projective-dimension shift to see that this syzygy has projective dimension at most `e`, and
-- then apply the induction hypothesis to the truncated exact projective sequence.
@[stacks 00O5]
theorem projective_top_kernel_of_exact_of_hasProjectiveDimensionLE
    {e : ℕ} {M : Type v} [AddCommGroup M] [Module R M]
    {F : Fin (e + 2) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, Module.Projective R (F i)]
    (d : (i : Fin (e + 1)) → F i.succ →ₗ[R] F i.castSucc)
    (π : F 0 →ₗ[R] M)
    (hπ : Function.Surjective π)
    (h_exact₀ : Function.Exact (d 0) π)
    (h_exact : ∀ i : Fin e, Function.Exact (d i.succ) (d i.castSucc))
    (hpd : HasProjectiveDimensionLE (ModuleCat.of R M) (e + 1)) :
    Module.Projective R (LinearMap.ker (d (Fin.last e))) := by
  induction e generalizing M with
  | zero =>
      have hκ_mem : ∀ x, d 0 x ∈ LinearMap.ker π := by
        intro x
        -- Exactness at `F₀` gives `π ∘ d₀ = 0`, so `d₀` lands in `ker π`.
        simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
          LinearMap.congr_fun h_exact₀.linearMap_comp_eq_zero x
      let κ : F 1 →ₗ[R] LinearMap.ker π :=
        LinearMap.codRestrict (LinearMap.ker π) (d 0) hκ_mem
      have hκ_ker : LinearMap.ker κ = LinearMap.ker (d 0) := by
        simpa [κ] using LinearMap.ker_codRestrict (LinearMap.ker π) (d 0) hκ_mem
      have hκ_surj : Function.Surjective κ := by
        intro x
        -- Exactness identifies `ker π` with the image of `d₀`.
        rcases (h_exact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hkerπ_proj : Module.Projective R (LinearMap.ker π) :=
        projective_ker_of_surjective_of_hasProjectiveDimensionLE_one
          (R := R) (M := M) π hπ hpd
      have hpd_kerπ : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) 0 := by
        let _ : Module.Projective R (LinearMap.ker π) := hkerπ_proj
        -- A projective first syzygy has projective dimension `≤ 0`.
        rw [← CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero]
        infer_instance
      let _ : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) 0 := hpd_kerπ
      -- We apply the `e = 0` kernel criterion once more to the surjection onto `ker π`.
      have hprojκ : Module.Projective R (LinearMap.ker κ) :=
        projective_ker_of_surjective_of_hasProjectiveDimensionLE_one
          (R := R) (M := LinearMap.ker π) κ hκ_surj
          (inferInstance : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) 1)
      exact hκ_ker ▸ hprojκ
  | succ e ih =>
      have hκ_mem : ∀ x, d 0 x ∈ LinearMap.ker π := by
        intro x
        -- Exactness at `F₀` again produces the codomain restriction to the first syzygy.
        simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
          LinearMap.congr_fun h_exact₀.linearMap_comp_eq_zero x
      let κ : F 1 →ₗ[R] LinearMap.ker π :=
        LinearMap.codRestrict (LinearMap.ker π) (d 0) hκ_mem
      have hκ_ker : LinearMap.ker κ = LinearMap.ker (d 0) := by
        simpa [κ] using LinearMap.ker_codRestrict (LinearMap.ker π) (d 0) hκ_mem
      have hκ_surj : Function.Surjective κ := by
        intro x
        -- The first syzygy is the image of `d₀`.
        rcases (h_exact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_exact : Function.Exact (d 1) κ := by
        -- The codomain restriction preserves the kernel, so the exactness equality is unchanged.
        exact LinearMap.exact_iff.mpr <| hκ_ker.trans (h_exact 0).linearMap_ker_eq
      have hpd' : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) (e + 1) :=
        hasProjectiveDimensionLE_first_syzygy_of_surjective
          (R := R) (M := M) (π := π) hπ hpd
      let F' : Fin (e + 2) → Type v := fun i => F i.succ
      let d' : (i : Fin (e + 1)) → F' i.succ →ₗ[R] F' i.castSucc := fun i => d i.succ
      have h_exact' : ∀ i : Fin e, Function.Exact (d' i.succ) (d' i.castSucc) := by
        intro i
        -- The truncated complex inherits exactness from the original sequence.
        simpa [d'] using h_exact i.succ
      -- Induction on the truncated exact projective resolution finishes the higher-syzygy case.
      simpa [F', d'] using
        ih (M := LinearMap.ker π) (F := F') (d := d') (π := κ) hκ_surj hκ_exact h_exact' hpd'

end
