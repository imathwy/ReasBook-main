import StacksProject_2024.stacks_project.Chap22.Lemma_22_7_3

open CategoryTheory

noncomputable section

universe u

namespace CochainComplex

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ

/-- Core/canonical construction for Lemma 22.16.1: if `f : M ⟶ P` is termwise epi and the
underlying graded `A`-module of `P` is degreewise projective, then `f` is split after forgetting
the differential. -/
instance forget_isSplitEpi_of_termwiseEpi_of_gradedProjective
    {M P : DGMod} (f : M ⟶ P)
    (hf : ∀ n : ℤ, Epi (f.f n)) (hP : ∀ n : ℤ, Projective (P.X n)) :
    IsSplitEpi (dgModuleUnderlyingGradedHomSystem.map f) :=
  let gradedSection : dgModuleUnderlyingGradedHomSystem.obj P ⟶
      dgModuleUnderlyingGradedHomSystem.obj M :=
    fun n ↦
      letI : Projective ((dgModuleUnderlyingGradedHomSystem.obj P) n) := by
        simpa [dgModuleUnderlyingGradedHomSystem] using hP n
      letI : Epi ((dgModuleUnderlyingGradedHomSystem.map f) n) := by
        simpa using hf n
      Projective.factorThru
        (𝟙 ((dgModuleUnderlyingGradedHomSystem.obj P) n))
        ((dgModuleUnderlyingGradedHomSystem.map f) n)
  IsSplitEpi.mk' ⟨gradedSection, by
    funext n
    letI : Projective ((dgModuleUnderlyingGradedHomSystem.obj P) n) := by
      simpa [dgModuleUnderlyingGradedHomSystem] using hP n
    letI : Epi ((dgModuleUnderlyingGradedHomSystem.map f) n) := by
      simpa using hf n
    simpa [gradedSection] using
      Projective.factorThru_comp
        (𝟙 ((dgModuleUnderlyingGradedHomSystem.obj P) n))
        ((dgModuleUnderlyingGradedHomSystem.map f) n)⟩

/-- Lemma 22.16.1: in the canonical cochain-complex model for differential graded `A`-modules, a
termwise epimorphism `M ⟶ P` with graded-projective target is an admissible epimorphism after
forgetting the differential. -/
@[stacks 09K0]
theorem isAdmissibleEpi_of_termwiseEpi_of_gradedProjective
    {M P : DGMod} (f : M ⟶ P)
    (hf : ∀ n : ℤ, Epi (f.f n)) (hP : ∀ n : ℤ, Projective (P.X n)) :
    IsAdmissibleEpi dgModuleUnderlyingGradedHomSystem f := by
  letI := forget_isSplitEpi_of_termwiseEpi_of_gradedProjective f hf hP
  infer_instance

/-- Companion view of Lemma 22.16.1: the admissible-epimorphism criterion yields the termwise
split-epimorphism conclusion used by the Chapter 13 strictification results. -/
theorem termwiseSplitEpi_of_termwiseEpi_of_gradedProjective
    {M P : DGMod} (f : M ⟶ P)
    (hf : ∀ n : ℤ, Epi (f.f n)) (hP : ∀ n : ℤ, Projective (P.X n)) :
    ∀ n : ℤ, IsSplitEpi (f.f n) := by
  exact
    termwiseSplitEpi_of_admissibleEpi
      (isAdmissibleEpi_of_termwiseEpi_of_gradedProjective f hf hP)

end

end CochainComplex
