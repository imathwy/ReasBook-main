import StacksProject_2024.stacks_project.Chap10.Definition_10_69_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_30_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_30_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Opposite
open RingTheory
open RingTheory.Sequence
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "Γ" => X.presheaf.obj (op ⊤)

-- Semantic recall: `RingTheory.Sequence.IsRegular`, `IsKoszulRegularSequence`,
-- `IsH1RegularSequence`, and `IsQuasiRegularSequence` are the canonical sequence owners here, and
-- Chapter 15 already exports the owner-level implication theorems reused below.

/-- Lemma 31.20.1 (1): for a ringed space, a finite family of global sections that is a regular
sequence is Koszul-regular. -/
@[stacks 063C]
theorem isKoszulRegularSequence_of_isRegular {r : ℕ}
    (f : Fin r → Γ)
    (hreg : IsRegular Γ (List.ofFn f)) :
    IsKoszulRegularSequence f := by
  let P : (Σ n, Fin n → Γ) → Prop := fun s ↦ IsKoszulRegularOn Γ s.2
  have hsigma :
      (⟨(List.ofFn f).length, (List.ofFn f).get⟩ : Σ n, Fin n → Γ) = ⟨r, f⟩ := by
    exact Fin.sigma_eq_of_eq_comp_cast List.length_ofFn <| funext fun i ↦ List.get_ofFn f i
  have hKoszul : P ⟨(List.ofFn f).length, (List.ofFn f).get⟩ := hreg.isKoszulRegularOn
  have htransport : P ⟨r, f⟩ := Eq.ndrec hKoszul hsigma
  exact htransport

/-- Lemma 31.20.1 (2): for a ringed space, a finite family of global sections that is
Koszul-regular is `H_1`-regular. -/
@[stacks 063C]
theorem isH1RegularSequence_of_isKoszulRegularSequence {r : ℕ}
    (f : Fin r → Γ)
    (hKoszul : IsKoszulRegularSequence f) :
    IsH1RegularSequence f := by
  simpa [IsKoszulRegularSequence, IsH1RegularSequence, IsKoszulRegularOn, IsH1RegularOn] using
    hKoszul 1 le_rfl

/-- Lemma 31.20.1 (3): for a ringed space, a finite family of global sections that is
`H_1`-regular is quasi-regular. -/
@[stacks 063C]
theorem isQuasiRegularSequence_of_isH1RegularSequence {r : ℕ}
    (f : Fin r → Γ)
    (hH1 : IsH1RegularSequence f) :
    IsQuasiRegularSequence (List.ofFn f) := by
  sorry

end AlgebraicGeometry.RingedSpace
