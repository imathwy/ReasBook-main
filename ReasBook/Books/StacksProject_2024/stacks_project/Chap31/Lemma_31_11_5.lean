import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_22_9
import StacksProject_2024.stacks_project.Chap17.Definition_17_17_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_25_2
import StacksProject_2024.stacks_project.Chap31.Lemma_31_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

-- Semantic recall: `lean_leansearch` surfaced the module-level flat-to-torsion-free bridge
-- `Module.Flat.torsion_eq_bot`, while the local Chapter 31 owner for the scheme statement is
-- `IsTorsionFree`. The affine-open sectionwise surface matches Chapter 29's flatness criterion
-- for quasi-coherent modules.

/-- Affine-open sections of a flat quasi-coherent `\mathcal O_X`-module on an integral scheme are
torsion free over the corresponding affine coordinate ring. -/
theorem IsFlat.torsionFree_sections
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFlat]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U)) := by
  have hflatSections : affineOpenSectionsFlatOver ℱ (𝟙 X) := by
    refine (flatOver_iff_affineOpenSectionsFlatOver ℱ (𝟙 X)).1 ?_
    simpa [relativeModuleOver] using (inferInstance : ℱ.IsFlat)
  letI : Module.Flat (Γ(X, U)) (Γ(ℱ, U)) :=
    by
      simpa using hflatSections hU hU (show U ≤ (𝟙 X) ⁻¹ᵁ U by simpa)
  exact flat_isTorsionFree (R := Γ(X, U)) (M := Γ(ℱ, U))

/-- The affine-open form of Lemma 31.11.5, packaged using `X.affineOpens`. -/
theorem IsFlat.torsionFree_sections_affineOpen
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFlat]
    (U : X.affineOpens) :
    Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U)) := by
  simpa using IsFlat.torsionFree_sections ℱ U.1 U.2

/-- Lemma 31.11.5: let `X` be an integral scheme. Any flat quasi-coherent `\mathcal O_X`-module
is torsion free. -/
@[stacks 0AXU]
theorem IsFlat.isTorsionFree
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFlat] :
    IsTorsionFree ℱ :=
  (isTorsionFree_iff_affineOpen ℱ).2 <|
    IsFlat.torsionFree_sections ℱ

/-- A flat quasi-coherent `\mathcal O_X`-module on an integral scheme is torsion free. -/
instance instIsTorsionFree_of_isFlat
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFlat] :
    IsTorsionFree ℱ :=
  IsFlat.isTorsionFree ℱ

end AlgebraicGeometry.Scheme.Modules
