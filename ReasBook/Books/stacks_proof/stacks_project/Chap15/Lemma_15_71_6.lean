import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_71_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open ModuleCat

universe u

/-
Domain-style sampling:
* primary domain: `I`-projective modules and their behavior in short exact sequences;
* sampled owner declarations:
  `Module.IsIdealProjective`,
  `smul_endomorphism_tfae_factorsThroughProjective_factorsThroughFree_ext`,
  `ShortComplex.ShortExact.extClass`,
  `precomp_extClass_surjective_of_projective_X₂`;
* best owner abstraction: the chapter owner is `Module.IsIdealProjective I M`, whose primitive
  data are projective factorizations of the multiplication maps `m ↦ (a : R) • m`; the canonical bridge
  for this short-exact statement is the `Ext`-annihilation formulation from Lemma `15.71.3`,
  combined with the short-exact `Ext` owner `ShortComplex.ShortExact.extClass` and its
  dimension-shifting API when the middle term is projective;
* primitive data: a short exact complex `S` together with explicit hypotheses
  `Module.IsIdealProjective I S.X₃` and `Projective S.X₂`;
* derived API: the `Ext¹`-annihilation characterization of `Module.IsIdealProjective`, obtained from
  `smul_endomorphism_tfae_factorsThroughProjective_factorsThroughFree_ext`, and the
  short-exact `Ext` comparison maps attached to `hS`;
* layer triage: this file is `source-facing`, reusing the chapter owner and the canonical
  short-exact `Ext` bridge rather than introducing a parallel `ModuleCat` wrapper.
-/

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {S : ShortComplex (ModuleCat.{u} R)}

/-- Helper for Lemma 15.71.6: the scalar endomorphism of `S.X₁` is the `ModuleCat` morphism
attached to `LinearMap.lsmul`. -/
lemma ofHom_lsmul_eq_smul_id (a : I) :
    ModuleCat.ofHom (LinearMap.lsmul R S.X₁ (a : R)) = (a : R) • 𝟙 S.X₁ := by
  -- Compare the two endomorphisms on the underlying module.
  ext x
  rfl

/-- Helper for Lemma 15.71.6: the extension class of `hS` is annihilated by every element of
`I` when `S.X₃` is `I`-projective. -/
lemma extClass_smul_zero_of_isIdealProjective (hS : S.ShortExact)
    (hX₃ : Module.IsIdealProjective I S.X₃) (a : I) :
    (a : R) • hS.extClass = 0 := by
  -- Apply Lemma 15.71.3 with test module `S.X₁`.
  let hAnnAll := (isIdealProjective_iff_ext_annihilator I S.X₃).mp hX₃
  let hAnnLe := hAnnAll S.X₁
  have hAnn :
      (a : R) ∈ Module.annihilator R (Ext S.X₃ S.X₁ 1) :=
    hAnnLe a.2
  exact Module.mem_annihilator.mp hAnn hS.extClass

/-- Helper for Lemma 15.71.6: the annihilation of the extension class rewrites as the degree-zero
exactness hypothesis for the scalar endomorphism of `S.X₁`. -/
lemma smul_extClass_eq_comp_lsmul_mk0 (hS : S.ShortExact)
    (hX₃ : Module.IsIdealProjective I S.X₃) (a : I) :
    hS.extClass.comp (mk₀ (ModuleCat.ofHom (LinearMap.lsmul R S.X₁ (a : R)))) (add_zero 1) = 0 := by
  -- Rewrite scalar multiplication on `Ext` as postcomposition by the scalar endomorphism.
  calc
    hS.extClass.comp (mk₀ (ModuleCat.ofHom (LinearMap.lsmul R S.X₁ (a : R)))) (add_zero 1)
        = hS.extClass.comp (mk₀ ((a : R) • 𝟙 S.X₁)) (add_zero 1) := by
            rw [ofHom_lsmul_eq_smul_id (S := S) (R := R) a]
    _ = (a : R) • hS.extClass := by
      simpa using (smul_eq_comp_mk₀ hS.extClass (a : R)).symm
    _ = 0 := extClass_smul_zero_of_isIdealProjective (S := S) hS hX₃ a

/-- Helper for Lemma 15.71.6: if the Yoneda product of the extension class with a degree-zero
class vanishes, then the corresponding endomorphism of `S.X₁` factors through the middle term
`S.X₂`. -/
lemma linearMap_factorsThroughProjective_of_extClass_comp_zero (hS : S.ShortExact)
    (hX₂ : Projective S.X₂) (φ : S.X₁ →ₗ[R] S.X₁)
    (hφ : hS.extClass.comp (mk₀ (ModuleCat.ofHom φ)) (add_zero 1) = 0) :
    φ.FactorsThroughProjective := by
  have hdeg : 1 + 0 = 1 := by
    simp
  -- Exactness lifts the degree-zero class `mk₀ φ` to a morphism out of the middle term.
  obtain ⟨ψExt, hψExt⟩ := contravariant_sequence_exact₁ hS S.X₁
    (mk₀ (ModuleCat.ofHom φ)) hdeg hφ
  obtain ⟨ψ, rfl⟩ := homEquiv₀.symm.surjective ψExt
  have hcomp : S.f ≫ ψ = ModuleCat.ofHom φ := by
    -- Translate the lifted `Ext⁰` class back to an equality of module morphisms.
    apply homEquiv₀.symm.injective
    simpa [Ext.homEquiv₀_symm_apply, Ext.mk₀_comp_mk₀] using hψExt
  letI : Projective S.X₂ := hX₂
  letI : Module.Projective R S.X₂ := by
    infer_instance
  have hfactor : φ = ψ.hom.comp S.f.hom := by
    simpa using (ModuleCat.hom_ext_iff.mp hcomp).symm
  exact ⟨S.X₂, inferInstance, inferInstance, inferInstance, S.f.hom, ψ.hom, hfactor⟩

/-- Lemma 15.71.6: in a short exact sequence `0 ⟶ K ⟶ P ⟶ M ⟶ 0` of `R`-modules, if `M` is
`I`-projective and `P` is projective, then `K` is `I`-projective. -/
@[stacks 0G95]
theorem isIdealProjective_X₁ (hS : S.ShortExact) (hX₃ : Module.IsIdealProjective I S.X₃)
    (hX₂ : Projective S.X₂) :
    Module.IsIdealProjective I S.X₁ := by
  -- For each `a ∈ I`, kill the extension class by `a` and lift the resulting scalar map.
  refine ⟨fun a ↦ ?_⟩
  exact linearMap_factorsThroughProjective_of_extClass_comp_zero (S := S) (R := R)
    hS hX₂ (LinearMap.lsmul R S.X₁ (a : R))
    (smul_extClass_eq_comp_lsmul_mk0 (S := S) (R := R) hS hX₃ a)

end CategoryTheory.ShortComplex.ShortExact
