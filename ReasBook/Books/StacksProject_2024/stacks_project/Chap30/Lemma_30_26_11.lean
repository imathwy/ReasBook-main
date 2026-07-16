import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1
import StacksProject_2024.stacks_project.Chap30.Definition_30_26_2
import StacksProject_2024.stacks_project.Chap30.Lemma_30_23_2
import StacksProject_2024.stacks_project.Chap30.Lemma_30_26_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f] [IsNoetherian S]

/-- Source-side Noetherian transfer used to put `Coh(X, I)` in the abelian context under the
finite-type morphism and Noetherian base hypotheses. -/
local instance instIsNoetherianSourceOfFiniteType : IsNoetherian X := sorry

-- Semantic recall: `lean_leansearch` returned `Scheme.IdealSheafData.support`; local Chapter 30
-- precedent supplies `Scheme.CoherentFormalModules`, `ClosedSubset.IsProperOver`, and the
-- affine-open section form of ideal-sheaf annihilation.

/-- A coherent formal module has closed support at each coherent stage. -/
theorem coherentFormalModuleStage_isClosed_moduleSupport
    {I : X.IdealSheafData} (M : Scheme.CoherentFormalModules X I) (n : ℕ) :
    IsClosed (moduleSupport (((M.obj).obj (op n)).obj)) := sorry

/-- Lemma 30.26.11 (1): for a finite type morphism `f : X ⟶ S` with `S` Noetherian and a
quasi-coherent ideal sheaf `I`, the objects of `\textit{Coh}(X, I)` whose first coherent stage
has support proper over `S` form a Serre subcategory. -/
@[stacks 0CYV]
theorem coherentFormalModules_firstStageProperSupport_isSerreClass
    (I : X.IdealSheafData) :
    ObjectProperty.IsSerreClass
      ((fun M : Scheme.CoherentFormalModules X I ↦
        ClosedSubset.IsProperOver f
          (⟨moduleSupport (((M.obj).obj (op 1)).obj),
            coherentFormalModuleStage_isClosed_moduleSupport M 1⟩ :
            TopologicalSpace.Closeds X)) :
        ObjectProperty (Scheme.CoherentFormalModules X I)) := sorry

/-- Lemma 30.26.11 (2): for a finite type morphism `f : X ⟶ S` with `S` Noetherian and a
quasi-coherent ideal sheaf `I`, the objects of `\textit{Coh}(X, I)` annihilated in every positive
stage by the ideal sheaf of some closed subscheme proper over `S` form a Serre subcategory. -/
@[stacks 0CYV]
theorem coherentFormalModules_annihilatedByProperClosedSubscheme_isSerreClass
    (I : X.IdealSheafData) :
    ObjectProperty.IsSerreClass
      ((fun M : Scheme.CoherentFormalModules X I ↦
        ∃ Z : X.IdealSheafData,
          IsProper (Z.subschemeι ≫ f) ∧
            ∀ n : ℕ, 1 ≤ n → ∀ U : X.affineOpens,
              Z.ideal U •
                (⊤ : Submodule Γ(X, U.1) (Γ(((M.obj).obj (op n)).obj, U.1))) = ⊥) :
        ObjectProperty (Scheme.CoherentFormalModules X I)) := sorry

end AlgebraicGeometry.Scheme.Modules
