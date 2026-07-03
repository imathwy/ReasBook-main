import Mathlib
import StacksProject_2024.Chap18.Lemma_18_19_2
import StacksProject_2024.Chap18.Lemma_18_28_7
import StacksProject_2024.Chap18.Lemma_18_30_4
import StacksProject_2024.Chap18.Lemma_18_30_7
import StacksProject_2024.Chap18.Situation_18_30_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

-- Proof sketch: write the source module as an iterated cokernel of maps from summands
-- `j_{W!}\mathcal O_W` with `W ∈ B`, reduce to a single such summand mapping into the target
-- presentation, represent the corresponding section locally using the covering families supplied by
-- Situation `18.30.5`, use quasi-compactness of the basis objects to replace the local cover by a
-- finite one, and fold the resulting finite family into a new presentation of the cokernel.
/-- Lemma 18.30.8: in Situation `18.30.5`, the cokernel of any morphism between modules
presented as in `18.30.7.2` by basis objects again admits a finite basis cokernel presentation. -/
theorem ringedSite_constructibleModule_cokernel_of_morphism
    {n₁ m₁ n₂ m₂ : ℕ}
    (U₁ : Fin n₁ → C) (V₁ : Fin m₁ → C)
    (U₂ : Fin n₂ → C) (V₂ : Fin m₂ → C)
    (hU₁ : ∀ i, U₁ i ∈ B) (hV₁ : ∀ j, V₁ j ∈ B)
    (hU₂ : ∀ i, U₂ i ∈ B) (hV₂ : ∀ j, V₂ j ∈ B)
    (f :
      (∐ fun j : Fin m₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₁ j)) ⟶
        (∐ fun i : Fin n₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₁ i)))
    (g :
      (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j)) ⟶
        (∐ fun i : Fin n₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₂ i)))
    (φ : cokernel f ⟶ cokernel g) :
    SheafOfModules.RingedSite.HasFiniteBasisConstructibleModuleCokernelPresentation
      𝒪 B (cokernel φ) := sorry

end
