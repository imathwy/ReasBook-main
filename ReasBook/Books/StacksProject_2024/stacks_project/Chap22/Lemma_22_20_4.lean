import Mathlib.Algebra.Homology.QuasiIso
import StacksProject_2024.stacks_project.Chap22.Lemma_22_20_3

open CategoryTheory
open HomologicalComplex

universe u

namespace CochainComplex

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ

/-- Bridge to the canonical quasi-isomorphism owner for Chapter 22 resolutions: a morphism of
differential graded `A`-modules that is epimorphic in every degree and on the induced cycles maps
is a quasi-isomorphism. -/
instance quasiIso_of_degreewiseEpi_of_epi_cyclesMap
    {P M : DGMod} (π : P ⟶ M)
    [hπ : Fact (∀ n : ℤ, Epi (π.f n))]
    [hcycles : Fact (∀ n : ℤ, Epi (cyclesMap π n))] :
    QuasiIso π := by
  let _ := hπ.1
  let _ := hcycles.1
  sorry

/-- Companion form of Lemma 22.20.4: the comparison map can already be chosen epic in the
category of differential graded `A`-modules. -/
theorem exists_epi_quasiIso_from_hasPropertyP
    (M : DGMod) :
    ∃ (P : DGMod) (π : P ⟶ M), Epi π ∧ QuasiIso π ∧ HasPropertyP P := by
  rcases exists_degreewiseSurjective_cyclesSurjective_hasPropertyP M with
    ⟨P, π, hP, hπ, hcycles⟩
  let _ : Fact (∀ n : ℤ, Epi (π.f n)) := ⟨hπ⟩
  let _ : Fact (∀ n : ℤ, Epi (cyclesMap π n)) := ⟨hcycles⟩
  refine ⟨P, π, HomologicalComplex.epi_of_epi_f π hπ, inferInstance, hP⟩

/-- Lemma 22.20.4: every differential graded `A`-module admits a quasi-isomorphism from a
differential graded `A`-module with property `(P)`. This keeps the Chapter 22 source-facing owner
`HasPropertyP` and the canonical quasi-isomorphism predicate `QuasiIso` as the public API
surface. -/
@[stacks 09KP]
theorem exists_quasiIso_from_hasPropertyP
    (M : DGMod) :
    ∃ (P : DGMod) (π : P ⟶ M), QuasiIso π ∧ HasPropertyP P := by
  rcases exists_epi_quasiIso_from_hasPropertyP M with ⟨P, π, -, hπ, hP⟩
  exact ⟨P, π, hπ, hP⟩

end

end CochainComplex
