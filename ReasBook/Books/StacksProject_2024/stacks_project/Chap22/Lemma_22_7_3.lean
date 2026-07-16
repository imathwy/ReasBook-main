import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap22.Definition_22_7_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_9_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open HomologicalComplex

universe u

-- This source item introduces no new owner: in the cochain-complex model for differential graded
-- modules, the Chapter 22 admissible mono/epi hypotheses are exactly the termwise split
-- mono/epi hypotheses used by the Chapter 13 strictification theorems below. The source-facing
-- entry is therefore a recall block rather than a duplicate local wrapper.

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ

/-- The graded-forgetful owner used to express admissibility for differential graded `A`-modules in
the canonical cochain-complex model. -/
def dgModuleUnderlyingGradedHomSystem :
    DGMod ⥤ GradedObject ℤ (ModuleCat A) :=
  HomologicalComplex.forget (ModuleCat A) (ComplexShape.up ℤ)

/-- Applying `dgModuleUnderlyingGradedHomSystem` to a morphism of differential graded `A`-modules
forgets the differential and keeps the degreewise maps. -/
@[simp] theorem dgModuleUnderlyingGradedHomSystem_ofHom
    {K L : DGMod} (f : K ⟶ L) (n : ℤ) :
    ((dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)).map f) n = f.f n :=
  rfl

/-- Bridge for Lemma 22.7.3 (1): an admissible monomorphism of differential graded `A`-modules is
termwise split after forgetting the differential. -/
theorem termwiseSplitMono_of_admissibleMono
    {K L : DGMod} {ι : K ⟶ L}
    (hι :
      IsAdmissibleMono
        (dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)) ι) :
    ∀ n : ℤ, IsSplitMono (ι.f n) := by
  intro n
  letI :
      IsSplitMono
        ((dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)).map ι) := hι
  refine IsSplitMono.mk' ⟨retraction
    ((dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)).map ι) n, ?_⟩
  simpa [dgModuleUnderlyingGradedHomSystem] using
    congr_fun (IsSplitMono.id
      ((dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)).map ι)) n

/-- Companion bridge for Lemma 22.7.3 (1): if a morphism of differential graded `A`-modules is
termwise split monic, then it is admissible after forgetting the differential. -/
theorem isAdmissibleMono_of_termwiseSplitMono
    {K L : DGMod} {ι : K ⟶ L}
    (hι : ∀ n : ℤ, IsSplitMono (ι.f n)) :
    IsAdmissibleMono
      (dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)) ι := by
  change IsSplitMono
    ((dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)).map ι)
  refine IsSplitMono.mk' ⟨fun n ↦ @retraction (ModuleCat A) _ _ _ (ι.f n) (hι n), ?_⟩
  funext n
  simpa [dgModuleUnderlyingGradedHomSystem_ofHom] using
    @IsSplitMono.id (ModuleCat A) _ _ _ (ι.f n) (hι n)

/-- Source-facing equivalence for Lemma 22.7.3 (1): admissibility in the cochain-complex model is
exactly the Chapter 13 termwise split-monomorphism condition. -/
theorem isAdmissibleMono_iff_termwiseSplitMono
    {K L : DGMod} {ι : K ⟶ L} :
    IsAdmissibleMono
      (dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)) ι ↔
      ∀ n : ℤ, IsSplitMono (ι.f n) := by
  constructor
  · exact termwiseSplitMono_of_admissibleMono
  · exact isAdmissibleMono_of_termwiseSplitMono

/-- Bridge for Lemma 22.7.3 (2): an admissible epimorphism of differential graded `A`-modules is
termwise split after forgetting the differential. -/
theorem termwiseSplitEpi_of_admissibleEpi
    {K L : DGMod} {π : K ⟶ L}
    (hπ :
      IsAdmissibleEpi
        (dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)) π) :
    ∀ n : ℤ, IsSplitEpi (π.f n) := by
  intro n
  letI :
      IsSplitEpi
        ((dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)).map π) := hπ
  refine IsSplitEpi.mk' ⟨section_
    ((dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)).map π) n, ?_⟩
  simpa [dgModuleUnderlyingGradedHomSystem] using
    congr_fun (IsSplitEpi.id
      ((dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)).map π)) n

/-- Companion bridge for Lemma 22.7.3 (2): if a morphism of differential graded `A`-modules is
termwise split epic, then it is admissible after forgetting the differential. -/
theorem isAdmissibleEpi_of_termwiseSplitEpi
    {K L : DGMod} {π : K ⟶ L}
    (hπ : ∀ n : ℤ, IsSplitEpi (π.f n)) :
    IsAdmissibleEpi
      (dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)) π := by
  change IsSplitEpi
    ((dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)).map π)
  refine IsSplitEpi.mk' ⟨fun n ↦ @section_ (ModuleCat A) _ _ _ (π.f n) (hπ n), ?_⟩
  funext n
  simpa [dgModuleUnderlyingGradedHomSystem_ofHom] using
    @IsSplitEpi.id (ModuleCat A) _ _ _ (π.f n) (hπ n)

/-- Source-facing equivalence for Lemma 22.7.3 (2): admissibility in the cochain-complex model is
exactly the Chapter 13 termwise split-epimorphism condition. -/
theorem isAdmissibleEpi_iff_termwiseSplitEpi
    {K L : DGMod} {π : K ⟶ L} :
    IsAdmissibleEpi
      (dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)) π ↔
      ∀ n : ℤ, IsSplitEpi (π.f n) := by
  constructor
  · exact termwiseSplitEpi_of_admissibleEpi
  · exact isAdmissibleEpi_of_termwiseSplitEpi

/-- Lemma 22.7.3 (1): in the cochain-complex model for differential graded modules, an admissible
monomorphism is exactly the termwise split-monomorphism hypothesis used by the Chapter 13
strictification theorem. -/
@[stacks 09JV]
theorem exists_homotopic_rightMap_of_admissibleMono
    {B C D E : DGMod}
    {f : B ⟶ C} {a : B ⟶ D} {b : C ⟶ E} {g : D ⟶ E}
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hf :
      IsAdmissibleMono
        (dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)) f) :
    ∃ (b' : C ⟶ E) (_ : Homotopy b b'), CommSq f a b' g :=
  CochainComplex.exists_homotopic_rightMap_of_termwiseSplitMono hcomm
    (termwiseSplitMono_of_admissibleMono hf)

/-- Lemma 22.7.3 (2): in the cochain-complex model for differential graded modules, an admissible
epimorphism is exactly the termwise split-epimorphism hypothesis used by the Chapter 13
strictification theorem. -/
@[stacks 09JV]
theorem exists_homotopic_leftMap_of_admissibleEpi
    {B C D E : DGMod}
    {f : B ⟶ C} {a : B ⟶ D} {b : C ⟶ E} {g : D ⟶ E}
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hg :
      IsAdmissibleEpi
        (dgModuleUnderlyingGradedHomSystem : DGMod ⥤ GradedObject ℤ (ModuleCat A)) g) :
    ∃ (a' : B ⟶ D) (_ : Homotopy a a'), CommSq f a' b g :=
  CochainComplex.exists_homotopic_leftMap_of_termwiseSplitEpi hcomm
    (termwiseSplitEpi_of_admissibleEpi hg)

end

/- Companion recall for Lemma 22.7.3 (1): the Chapter 13 strictification theorem is the canonical
termwise-split core reused above. -/
recall CochainComplex.exists_homotopic_rightMap_of_termwiseSplitMono

/- Companion recall for Lemma 22.7.3 (2): the Chapter 13 strictification theorem is the canonical
termwise-split core reused above. -/
recall CochainComplex.exists_homotopic_leftMap_of_termwiseSplitEpi
