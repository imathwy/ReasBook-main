import StacksProject_2024.stacks_project.Chap13.Lemma_13_9_6
import StacksProject_2024.stacks_project.Chap22.Lemma_22_7_3

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

universe u

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ

-- Semantic recall hits: `HomologicalComplex.forget` confirms the canonical graded-forgetful
-- viewpoint, while `CategoryTheory.SplitMono.mk` / `CategoryTheory.IsSplitMono.mk'` confirm that
-- admissibility should be expressed through degreewise retractions after forgetting the
-- differential; `CochainComplex.splitMono_factorization_through_biproduct_mappingCone_id` supplies
-- the canonical middle object `L ⊞ C(1_K)`.

/-- Lemma 22.7.4 (1): the canonical map from `K` to `L ⊞ C(1_K)` in the standard
factorization of a morphism of differential graded `A`-modules is an admissible monomorphism. -/
@[stacks 09JW]
theorem admissibleMono_factorization_through_biproduct_mappingCone_id
    {K L : DGMod} (α : K ⟶ L) :
    IsAdmissibleMono dgModuleUnderlyingGradedHomSystem
      (CochainComplex.splitMonoFactorizationι α) := by
  exact (isAdmissibleMono_iff_termwiseSplitMono).2
    (CochainComplex.splitMonoFactorizationι_f_isSplitMono α)

/-- Lemma 22.7.4 (2): the canonical admissible monomorphism followed by the projection
to `L` recovers the original morphism. -/
@[stacks 09JW]
theorem splitMonoFactorizationι_comp_biprod_fst
    {K L : DGMod} (α : K ⟶ L) :
    CochainComplex.splitMonoFactorizationι α ≫
        (biprod.fst : CochainComplex.splitMonoFactorizationObj K L ⟶ L) = α := by
  simpa using CochainComplex.splitMonoFactorizationι_comp_fst α

/-- Lemma 22.7.4 (3): `biprod.inl` is a section of the projection from the canonical
middle object to `L`. -/
@[stacks 09JW]
theorem splitMonoFactorization_biprod_inl_comp_fst
    {K L : DGMod} :
    (biprod.inl : L ⟶ CochainComplex.splitMonoFactorizationObj K L) ≫
        (biprod.fst : CochainComplex.splitMonoFactorizationObj K L ⟶ L) = 𝟙 L := by
  simp

/-- Lemma 22.7.4 (4): the reverse composite of the canonical projection and section is
homotopic to the identity on the middle object. -/
@[stacks 09JW]
theorem splitMonoFactorization_biprod_fst_comp_inl_homotopic_id
    {K L : DGMod} :
    Nonempty
      (Homotopy
        ((biprod.fst : CochainComplex.splitMonoFactorizationObj K L ⟶ L) ≫
          (biprod.inl : L ⟶ CochainComplex.splitMonoFactorizationObj K L))
        (𝟙 (CochainComplex.splitMonoFactorizationObj K L))) := by
  exact ⟨(CochainComplex.splitMonoFactorizationProjectionHomotopyEquiv K L).homotopyHomInvId⟩

end
