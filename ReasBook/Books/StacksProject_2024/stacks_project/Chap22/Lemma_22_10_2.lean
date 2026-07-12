import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Lemma_13_10_2
import StacksProject_2024.Chap22.DGModuleModel
import StacksProject_2024.Chap22.Lemma_22_7_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open ComplexShape
open HomologicalComplex
open CochainComplex

universe u

section

variable {A : Type u} [Ring A]

-- Canonical reuse: the source-facing Chapter 22 statement is the differential-graded-module
-- specialization of the Chapter 13 cochain-complex octahedron theorem, and the only extra Chapter
-- 22 input is the bridge from admissible monomorphisms to termwise split monomorphisms.

/-- Lemma 22.10.2: if `α : M ⟶ N` and `β : N ⟶ P` are admissible monomorphisms of differential
graded `A`-modules, then after forgetting the differential one obtains the three degreewise split
short complexes from Chapter 13, and the associated canonical triangles fit into an octahedron in
the homotopy category. -/
@[stacks 09KI]
theorem admissible_injections_of_dgModules_have_octahedron
    {M N P : ModuleCat.DGMod A} (α : M ⟶ N) (β : N ⟶ P)
    (hα : IsAdmissibleMono dgModuleUnderlyingGradedHomSystem α)
    (hβ : IsAdmissibleMono dgModuleUnderlyingGradedHomSystem β) :
    ∃ (Q₁ Q₂ Q₃ : ModuleCat.DGMod A)
      (p₁ : N ⟶ Q₁) (hαp₁ : α ≫ p₁ = 0)
      (p₂ : P ⟶ Q₂) (hαβp₂ : (α ≫ β) ≫ p₂ = 0)
      (p₃ : P ⟶ Q₃) (hβp₃ : β ≫ p₃ = 0),
      (let S₁₂ := ShortComplex.mk α p₁ hαp₁
       let Q := HomotopyCategory.quotient (ModuleCat A) (up ℤ)
       let S₁₃ := ShortComplex.mk (α ≫ β) p₂ hαβp₂
       let S₂₃ := ShortComplex.mk β p₃ hβp₃
       ∃ (σ₁₂ : ∀ n : ℤ, (S₁₂.map (eval (ModuleCat A) (up ℤ) n)).Splitting)
         (σ₁₃ : ∀ n : ℤ, (S₁₃.map (eval (ModuleCat A) (up ℤ) n)).Splitting)
         (σ₂₃ : ∀ n : ℤ, (S₂₃.map (eval (ModuleCat A) (up ℤ) n)).Splitting),
         let T₁₂ := trianglehOfDegreewiseSplit S₁₂ σ₁₂
         let T₁₃ := trianglehOfDegreewiseSplit S₁₃ σ₁₃
         let T₂₃ := trianglehOfDegreewiseSplit S₂₃ σ₂₃
         ∃ (h₁₂ : Triangle.mk (Q.map α) T₁₂.mor₂ T₁₂.mor₃ ∈ distTriang (ModuleCat.KDGMod A))
           (h₂₃ : Triangle.mk (Q.map β) T₂₃.mor₂ T₂₃.mor₃ ∈ distTriang (ModuleCat.KDGMod A))
           (h₁₃ :
             Triangle.mk (Q.map (α ≫ β)) T₁₃.mor₂ T₁₃.mor₃ ∈ distTriang (ModuleCat.KDGMod A)),
           Nonempty
             (Octahedron (Functor.map_comp Q α β).symm h₁₂ h₂₃ h₁₃)) := by
  exact
    split_injections_of_cochain_complexes_have_octahedron α β
      (termwiseSplitMono_of_admissibleMono hα)
      (termwiseSplitMono_of_admissibleMono hβ)

end

/- Companion recall: the cochain-complex owner reused by Lemma 22.10.2 is the Chapter 13 theorem
`split_injections_of_cochain_complexes_have_octahedron`. -/
recall split_injections_of_cochain_complexes_have_octahedron

/- Companion recall: the admissible-monomorphism hypothesis is converted to the termwise split
monomorphism input needed by the Chapter 13 octahedron theorem via the canonical bridge
`termwiseSplitMono_of_admissibleMono`. -/
recall termwiseSplitMono_of_admissibleMono

/- Companion recall: the TR4 witness produced by the canonical theorem lives in the owner
`CategoryTheory.Triangulated.Octahedron`. -/
recall Octahedron

/- Companion recall: Chapter 22 packages admissible monomorphisms of differential graded modules by
the graded-split owner `IsAdmissibleMono dgModuleUnderlyingGradedHomSystem`. -/
recall IsAdmissibleMono

/- Companion recall: the concrete graded-forgetful system for differential graded `A`-modules is
`dgModuleUnderlyingGradedHomSystem`. -/
recall dgModuleUnderlyingGradedHomSystem
