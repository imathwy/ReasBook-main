import Mathlib
import StacksProject_2024.Chap07.Lemma_7_29_4
import StacksProject_2024.Chap18.Lemma_18_28_7
import StacksProject_2024.Chap18.Situation_18_30_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type u)]
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

-- Proof sketch: use Situation `18.30.5` to choose, for each local section of `ℱ`, a covering
-- family by basis objects on which that section is represented by maps from the corresponding
-- `h_U^#`. Taking the coproduct over all such chosen basis objects gives a morphism to `ℱ` whose
-- image sieve contains a covering sieve at every section, hence is locally surjective.
/-- Lemma 18.30.6 (1): in Situation `18.30.5`, every sheaf of sets is the target of a locally
surjective map from a coproduct of sheafified representables `h_{U_i}^#` with `U_i ∈ B`. -/
theorem exists_locallySurjective_from_coproduct_basis_sheafifiedRepresentables
    (ℱ : Sheaf J (Type u)) :
    ∃ (I : Type u) (U : I → C),
      (∀ i, U i ∈ B) ∧
        ∃ _hc : HasCoproduct (fun i : I ↦ J.sheafifiedRepresentable (U i)),
          ∃ (φ : (∐ fun i : I ↦ J.sheafifiedRepresentable (U i)) ⟶ ℱ),
            Sheaf.IsLocallySurjective φ := sorry

end CategoryTheory.GrothendieckTopology

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

-- Proof sketch: apply Situation `18.30.5` to choose, for every local generator of `ℱ`, a basis
-- object over which that generator is represented. By adjunction this yields maps
-- `j_{U!}\mathcal O_U ⟶ ℱ`; summing over all chosen basis objects produces an epimorphism.
/-- Lemma 18.30.6 (2): in Situation `18.30.5`, every `\mathcal O`-module is a quotient of a
direct sum of `j_{U_i!}\mathcal O_{U_i}` with `U_i ∈ B`. -/
theorem exists_epi_from_coproduct_basis_localizedStructureModuleExtensionByZero
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (I : Type u) (U : I → C),
      (∀ i, U i ∈ B) ∧
        ∃ (φ : (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ ℱ),
          Epi φ := sorry

end SheafOfModules.RingedSite
