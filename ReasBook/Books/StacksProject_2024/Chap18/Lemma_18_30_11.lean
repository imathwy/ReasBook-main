import Mathlib
import StacksProject_2024.Chap12.Definition_12_10_1
import StacksProject_2024.Chap18.Lemma_18_30_7
import StacksProject_2024.Chap18.Situation_18_30_5
import StacksProject_2024.Chap18.Lemma_18_30_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
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

-- Proof sketch: apply the weak-LinearRepresentations_Serre_1977 criterion to the object property of modules admitting a
-- finite basis cokernel presentation as in `18.30.7.2`. The basis assumptions are the setup from
-- Situation `18.30.5`, the displayed hypothesis gives the kernel step for maps between the
-- standard finite presentation objects, and the remaining closure properties are exactly the ones
-- established earlier in this subsection.
/-- Lemma 18.30.11: in Situation `18.30.5`, let `\mathcal A \subset \operatorname{Mod}(\mathcal
O)` be the full subcategory of modules isomorphic to a cokernel as in `18.30.7.2`. If the kernel
of every map
`\bigoplus_{j = 1, \ldots, m} j_{V_j!}\mathcal O_{V_j} \to
\bigoplus_{i = 1, \ldots, n} j_{U_i!}\mathcal O_{U_i}`
with `U_i` and `V_j` in `B` again lies in `\mathcal A`, then `\mathcal A` is a weak LinearRepresentations_Serre_1977
subcategory of `\operatorname{Mod}(\mathcal O)`. -/
theorem ringedSite_finiteBasisConstructibleModuleCokernelPresentation_isWeakSerreSubcategory_of_kernel_condition
    (hkernel :
      ∀ {n m : ℕ} (U : Fin n → C) (V : Fin m → C),
        (∀ i, U i ∈ B) →
        (∀ j, V j ∈ B) →
        (f :
          (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
            (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))) →
          HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B (kernel f)) :
    IsWeakSerreClass (HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B) := sorry

end
