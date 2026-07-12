import Mathlib
import StacksProject_2024.Chap10.Lemma_10_51_3
import StacksProject_2024.Chap15.Lemma_15_66_6

noncomputable section

open CategoryTheory
open DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-
Domain-style sampling for Lemma 15.66.7:
- primary domain: pseudo-coherent objects in the derived category of `A`-modules, together with
  the degree-`i` homology comparison induced by a map into a single-degree object and the
  commutative-algebra control of finite quotient modules by powers of an ideal;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.homologyToSingle`,
  `Ideal.exists_artin_rees_constant_of_exact`,
  `Submodule.annihilator_quotient`;
- best owner abstraction: the source-facing content is still the existence theorem below; the
  canonical owners are `K.IsPseudoCoherent`, the bridge morphism `DerivedCategory.homologyToSingle`
  from `15.66.6`, and the standard quotient/annihilator API used to produce an `I`-power-torsion
  finite module;
- primitive vs. derived:
  primitive data are the object `K`, the degree `i`, the ideal `I`, and the hypothesis that
  `H^i(K) / I H^i(K)` is nontrivial;
  derived API is the chosen finite `A`-module `E`, the annihilator containment `I ^ n ≤
  Module.annihilator A E`, and the morphism `α : K ⟶ E[-i]` with nonzero induced map on
  homology;
- source/core/bridge triage:
  `source-facing`: the existence theorem
    `exists_finite_ideal_pow_torsion_map_of_homology_mod_ideal_nontrivial`;
  `core/canonical`: `K.IsPseudoCoherent`, `homologyFunctor`, `singleFunctor`, and the Chapter 10
    Artin-Rees / quotient-annihilator owner API;
  `bridge/view`: `DerivedCategory.homologyToSingle`.
-/

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single" => DerivedCategory.singleFunctor (ModuleCat A)

/-- Helper for Lemma 15.66.7: postcomposing a map into a single object with a module morphism
postcomposes the induced map on degree-`i` homology by the same morphism. -/
lemma homologyToSingle_comp_single_map
    {K : DMod} {M E : ModuleCat A} (i : ℤ)
    (α : K ⟶ (single i).obj M) (q : M ⟶ E) :
    homologyToSingle i (α ≫ (single i).map q) = homologyToSingle i α ≫ q := by
  -- Expand the definition so the naturality square for the single-object comparison is visible.
  rw [DerivedCategory.homologyToSingle, DerivedCategory.homologyToSingle]
  simp only [Functor.map_comp, Category.assoc]
  -- Naturality identifies the right-hand factor with postcomposition by `q`.
  simpa [Category.assoc] using
    congrArg (fun f ↦ (H i).map α ≫ f)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) i).hom.naturality q)

/-- Helper for Lemma 15.66.7: an injective map into a finite module admits a quotient by a power
of `I` whose kernel on the source is already contained in `I • ⊤`. -/
lemma exists_ideal_power_preimage_in_ideal_of_injective_map
    {X M : ModuleCat A} [Module.Finite A M]
    (φ : X →ₗ[A] M) (hφ_inj : Function.Injective φ) :
    ∃ n : ℕ, ∀ x : X,
      (Submodule.mkQ (I ^ n • (⊤ : Submodule A M))) (φ x) = 0 →
        x ∈ I • (⊤ : Submodule A X) := by
  -- Read the exact sequence `0 → X → M` through the kernel inclusion of `φ`.
  obtain ⟨c, hpreimage, _hbound⟩ :=
    Ideal.exists_artin_rees_constant_of_exact (R := A) (I := I)
      (LinearMap.exact_subtype_ker_map φ)
  refine ⟨c + 1, ?_⟩
  intro x hx
  have hx_mem :
      φ x ∈ I ^ (c + 1) • (⊤ : Submodule A M) := by
    exact (Submodule.Quotient.mk_eq_zero _).1 hx
  have hx_comap : x ∈ Submodule.comap φ (I ^ (c + 1) • (⊤ : Submodule A M)) := by
    exact hx_mem
  have hx_shift :
      x ∈ LinearMap.ker φ ⊔
          I ^ (c + 1 - c) • Submodule.comap φ (I ^ c • (⊤ : Submodule A M)) := by
    rw [← hpreimage (c + 1) (Nat.le_add_right c 1)]
    exact hx_comap
  have hx_mem :
      x ∈ I • Submodule.comap φ (I ^ c • (⊤ : Submodule A M)) := by
    simpa [LinearMap.ker_eq_bot.2 hφ_inj, show c + 1 - c = 1 by omega] using hx_shift
  -- Forgetting the deeper Artin-Rees preimage leaves the desired membership in `I • ⊤`.
  exact
    (smul_mono_right I
      (show Submodule.comap φ (I ^ c • (⊤ : Submodule A M)) ≤
          (⊤ : Submodule A X) from le_top)) hx_mem

/-- Helper for Lemma 15.66.7: if every class vanishing in `M / I^n M` already comes from
`I X`, then the composite `X → M → M / I^n M` is nonzero whenever `X / I X` is nontrivial. -/
lemma quotient_comp_ne_zero_of_nontrivial_mod_ideal
    {X M : ModuleCat A} (φ : X →ₗ[A] M) (n : ℕ)
    (hpre : ∀ x : X,
      (Submodule.mkQ (I ^ n • (⊤ : Submodule A M))) (φ x) = 0 →
        x ∈ I • (⊤ : Submodule A X))
    (hX : Nontrivial (X ⧸ (I • (⊤ : Submodule A X)))) :
    (Submodule.mkQ (I ^ n • (⊤ : Submodule A M))).comp φ ≠ 0 := by
  intro hzero
  have htop_le : (⊤ : Submodule A X) ≤ I • (⊤ : Submodule A X) := by
    intro x hx
    -- If the quotient composite were zero, every element of `X` would already lie in `I X`.
    apply hpre x
    have hx_zero :=
      congrArg (fun f : X →ₗ[A] M ⧸ (I ^ n • (⊤ : Submodule A M)) ↦ f x) hzero
    simpa using hx_zero
  have htop : I • (⊤ : Submodule A X) = ⊤ := top_unique htop_le
  have hsubsingleton : Subsingleton (X ⧸ (I • (⊤ : Submodule A X))) := by
    simpa [htop] using
      (inferInstance : Subsingleton (X ⧸ (⊤ : Submodule A X)))
  exact (not_nontrivial_iff_subsingleton.mpr hsubsingleton) hX

/-- Helper for Lemma 15.66.7: the quotient by `I ^ n M` is annihilated by `I ^ n`. -/
lemma ideal_pow_le_annihilator_quotient_by_pow_smul
    (M : ModuleCat A) (n : ℕ) :
    I ^ n ≤ Module.annihilator A (M ⧸ (I ^ n • (⊤ : Submodule A M))) := by
  intro a ha
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule A M)) x
  -- The scalar `a ∈ I ^ n` sends every lift into the killed submodule.
  change (Submodule.Quotient.mk (a • y) :
      M ⧸ (I ^ n • (⊤ : Submodule A M))) = 0
  exact (Submodule.Quotient.mk_eq_zero _).2 <|
    Submodule.smul_mem_smul ha (by simp)

-- Proof sketch: apply Lemma `15.66.6` to obtain a map from `K` to a finitely presented module in
-- degree `i` whose induced map on `H^i(K)` is injective. Use Artin-Rees for the inclusion
-- `H^i(K) ⊆ M` with respect to `I` to choose `n` with `H^i(K) ∩ I ^ n M ⊆ I H^i(K)`, pass to
-- the quotient `E = M / I ^ n M`, and compose with the quotient map; the induced map on
-- `H^i(K)` remains nonzero because `H^i(K) / I H^i(K)` is nontrivial.
/-- Lemma 15.66.7: let `A` be a Noetherian ring, let `K ∈ D(A)` be pseudo-coherent, and let `I`
be an ideal of `A`. If `H^i(K) / I H^i(K)` is nontrivial, then there exists a finite `A`-module
`E` annihilated by a power of `I` and a map `K ⟶ E[-i]` whose induced map on `H^i(K)`
is nonzero, formalized as `DerivedCategory.homologyToSingle i α ≠ 0`. -/
@[stacks 0A7D]
theorem exists_finite_ideal_pow_torsion_map_of_homology_mod_ideal_nontrivial
    (K : DMod) (hK : K.IsPseudoCoherent) (i : ℤ)
    (hHi : Nontrivial (((H i).obj K) ⧸ (I • (⊤ : Submodule A ((H i).obj K))))) :
    ∃ (E : ModuleCat A) (_ : Module.Finite A E) (n : ℕ)
      (_ : I ^ n ≤ Module.annihilator A E) (α : K ⟶ (single i).obj E),
        homologyToSingle i α ≠ 0 := by
  obtain ⟨M, hMfp, α, hαmono⟩ :=
    exists_finitelyPresented_module_map_inducing_mono_of_isPseudoCoherent
      (R := A) K hK i
  letI : Module.FinitePresentation A M := hMfp
  let φ : (H i).obj K ⟶ M := homologyToSingle i α
  have hφ_inj : Function.Injective φ.hom := by
    exact (ModuleCat.mono_iff_injective _).1 hαmono
  obtain ⟨n, hpre⟩ :=
    exists_ideal_power_preimage_in_ideal_of_injective_map
      (I := I) φ.hom hφ_inj
  let E : ModuleCat A := ModuleCat.of A (M ⧸ (I ^ n • (⊤ : Submodule A M)))
  have hEfinite : Module.Finite A E := inferInstance
  have hEann : I ^ n ≤ Module.annihilator A E :=
    ideal_pow_le_annihilator_quotient_by_pow_smul (I := I) M n
  let q : M ⟶ E := ModuleCat.ofHom (Submodule.mkQ (I ^ n • (⊤ : Submodule A M)))
  let β : K ⟶ (single i).obj E := α ≫ (single i).map q
  have hβ_desc :
      homologyToSingle i β = φ ≫ q := by
    -- The final homology map is the Artin-Rees quotient of the injective comparison from
    -- Lemma `15.66.6`.
    simpa [β, φ] using homologyToSingle_comp_single_map (A := A) (i := i) α q
  have hqφ_ne :
      (Submodule.mkQ (I ^ n • (⊤ : Submodule A M))).comp φ.hom ≠ 0 :=
    quotient_comp_ne_zero_of_nontrivial_mod_ideal
      (I := I) φ.hom n hpre hHi
  refine ⟨E, hEfinite, n, hEann, β, ?_⟩
  intro hzero
  rw [hβ_desc] at hzero
  have hzero_hom : (Submodule.mkQ (I ^ n • (⊤ : Submodule A M))).comp φ.hom = 0 := by
    simpa [q, φ] using congrArg (fun f => f.hom) hzero
  exact hqφ_ne hzero_hom

end

end CategoryTheory
