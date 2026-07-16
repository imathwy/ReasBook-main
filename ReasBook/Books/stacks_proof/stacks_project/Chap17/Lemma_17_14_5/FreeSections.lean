import Mathlib
import stacks_proof.stacks_project.Chap17.Definition_17_14_1

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- Helper for Lemma 17.14.5: sections of a module sheaf on the slice over `U` are recovered by
evaluating at the terminal object `U → U`. -/
noncomputable def over_sections_equiv_evaluation
    {U : Opens X} (M : SheafOfModules (X.ringCatSheaf.over U)) :
    M.sections ≃ M.val.obj (op (Over.mk (𝟙 U))) where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
  invFun m :=
    M.val.sectionsMk
      (fun W ↦ M.val.map ((Over.mkIdTerminal.from W.unop).op) m)
      (fun W Y f ↦ by
        -- Proof comment: every object of `Over U` has a unique map to the terminal object.
        have h :
            (Over.mkIdTerminal.from W.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from W.unop)
            (Over.mkIdTerminal.from Y.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- Proof comment: a section is determined by its restrictions from the terminal object.
    ext W
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from W.unop).op)
  right_inv m := by
    -- Proof comment: the reconstructed section evaluates back to `m` at the terminal object.
    change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h :
        Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 17.14.5: under terminal evaluation, a section map is the terminal component
of the sheaf morphism. -/
theorem over_sections_equiv_evaluation_sectionsMap
    {U : Opens X} {M N : SheafOfModules (X.ringCatSheaf.over U)}
    (ψ : M ⟶ N) (s : M.sections) :
    (over_sections_equiv_evaluation N) (SheafOfModules.sectionsMap ψ s) =
      (ψ.val.app (op (Over.mk (𝟙 U)))) ((over_sections_equiv_evaluation M) s) := by
  -- Proof comment: both sides are definitionally evaluation of the mapped section at `U → U`.
  rfl

/-- Helper for Lemma 17.14.5: the inverse of terminal evaluation is natural in the sheaf
morphism. -/
theorem sectionsMap_over_sections_equiv_evaluation_symm
    {U : Opens X} {M N : SheafOfModules (X.ringCatSheaf.over U)}
    (ψ : M ⟶ N) (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    SheafOfModules.sectionsMap ψ ((over_sections_equiv_evaluation M).symm m) =
      (over_sections_equiv_evaluation N).symm ((ψ.val.app (op (Over.mk (𝟙 U)))) m) := by
  -- Proof comment: evaluate both sections at the terminal object and use the terminal-component
  -- formula above.
  apply (over_sections_equiv_evaluation N).injective
  rw [over_sections_equiv_evaluation_sectionsMap]
  simp

/-- Helper for Lemma 17.14.5: a split epimorphism of the free rank-`r` module sheaf on an open
subset induces a surjective endomorphism on global sections over that open. -/
theorem global_sections_surjective_of_split_epi_free_endomorphism
    (X : RingedSpace.{u}) (r : ℕ) {U : Opens X}
    {α β :
      (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
        SheafOfModules (X.ringCatSheaf.over U)) ⟶
      (SheafOfModules.free.{u} (ULift.{u} (Fin r)) :
        SheafOfModules (X.ringCatSheaf.over U))}
    (hβ : β ≫ α = 𝟙 _) :
    Function.Surjective
      (((SheafOfModules.evaluation (X.ringCatSheaf.over U)
          (op (Over.mk (𝟙 U)))).map α).hom) := by
  intro s
  refine ⟨((SheafOfModules.evaluation (X.ringCatSheaf.over U)
      (op (Over.mk (𝟙 U)))).map β).hom s, ?_⟩
  -- Proof comment: evaluating the left inverse on global sections produces a preimage.
  change
    ((((SheafOfModules.evaluation (X.ringCatSheaf.over U)
        (op (Over.mk (𝟙 U)))).map β) ≫
        ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
          (op (Over.mk (𝟙 U)))).map α)).hom s) = s
  rw [← Functor.map_comp]
  rw [hβ]
  rfl

end AlgebraicGeometry.RingedSpace
