import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_8_1
import stacks_proof.stacks_project.Chap13.Lemma_13_15_5

-- Declarations for this item's helper module.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory
open scoped ZeroObject

universe v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

local instance isInjective_containsZero : (isInjective 𝒜).ContainsZero where
  exists_zero := ⟨0, isZero_zero 𝒜, inferInstance⟩

local instance isInjective_hasMonoEmbedding : HasMonoEmbedding (isInjective 𝒜) where
  exists_mono X := ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩

/-- Helper for Lemma 13.20.2: every bounded-below homotopy object admits a quasi-isomorphism to a
bounded-below homotopy object whose cochain terms are injective. -/
theorem exists_quasiIso_to_boundedBelowInjective
    (X : K⁺(𝒜)) :
    ∃ (X' : K⁺(𝒜)) (s : X ⟶ X'),
      (∀ n : ℤ, Injective (X'.obj.as.X n)) ∧
        HomotopyCategory.quasiIso 𝒜 (up ℤ) s.hom := by
  let K : CochainComplex 𝒜 ℤ := X.obj.as
  have hPlus : CochainComplex.plus 𝒜 K := by
    -- Proof comment: unpack bounded-below on the homotopy object into bounded-below on its
    -- representing cochain complex.
    simpa [K, HomotopyCategory.plus] using X.property
  obtain ⟨a, hK⟩ := (CochainComplex.plus_iff 𝒜 K).1 hPlus
  -- Proof comment: resolve the representing cochain complex by a bounded-below injective complex.
  obtain ⟨I, α, hα⟩ :=
    exists_termwiseMono_quasiIso_with_terms_in_of_isStrictlyGE (isInjective 𝒜) a K hK
  let Xc : Comp⁺(𝒜) := ⟨K, X.property⟩
  have hXeq : (HomotopyCategory.Plus.quotient 𝒜).obj Xc = X := by
    rfl
  let Iplus : Comp⁺(𝒜) := hα.toPlusWithTermsIn
  let X' : K⁺(𝒜) := (HomotopyCategory.Plus.quotient 𝒜).obj Iplus
  let α' : Xc ⟶ Iplus := ⟨α⟩
  let s : X ⟶ X' := by
    -- Proof comment: pass the cochain-level quasi-isomorphism to the bounded-below homotopy
    -- category.
    simpa [X', hXeq] using (HomotopyCategory.Plus.quotient 𝒜).map α'
  refine ⟨X', s, ?_, ?_⟩
  · -- Proof comment: the replacement inherits termwise injectivity from the cochain-level
    -- resolution.
    intro n
    simpa [X'] using hα.toPlusWithTermsIn.term_mem n
  · -- Proof comment: the bounded-below homotopy morphism is a quasi-isomorphism because its
    -- underlying homotopy-category morphism comes from a quasi-isomorphism of cochain complexes.
    simpa [s, X', hXeq] using
      (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          ((HomotopyCategory.quotient 𝒜 (up ℤ)).map α) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hα.quasiIso)

end

end CategoryTheory
