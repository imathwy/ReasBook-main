import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import StacksProject_2024.stacks_project.Chap29.Lemma_29_32_18

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

variable {Z X Y : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]

-- Semantic recall: `lean_leansearch` surfaced the general immersion and differential exactness
-- APIs; local Chapter 29 precedent fixes this conormal sequence as existential comparison maps
-- in `Z.Modules`, with smoothness upgrading Lemma 29.32.18 from `.Exact ∧ Epi` to `ShortExact`.

/-- Lemma 29.34.18: let `Z ⟶ X ⟶ Y` be a commutative diagram of schemes, written with
`i : Z ⟶ X`, `j : Z ⟶ Y`, and `f : X ⟶ Y`. If `i` and `j` are immersions and `f` is smooth,
then the canonical sequence
`0 ⟶ \mathcal C_{Z/Y} ⟶ \mathcal C_{Z/X} ⟶ i^* \Omega_{X/Y} ⟶ 0`
from Lemma 29.32.18 is short exact. In the current project, the canonical comparison maps from
Lemma 29.32.18 are represented by existential morphisms in `Z.Modules`. -/
@[stacks 06AB]
theorem exists_shortExact_immersionConormalToPullbackDifferentialsSequence_of_smooth
    (i : Z ⟶ X) (j : Z ⟶ Y) (f : X ⟶ Y) [IsImmersion i] [IsImmersion j]
    (hcomm : i ≫ f = j) (hf : Smooth f) :
    ∃ φ : immersionConormalSheaf j ⟶ immersionConormalSheaf i,
      ∃ ψ : immersionConormalSheaf i ⟶
          (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom],
        ∃ hφψ : φ ≫ ψ = 0, (ShortComplex.mk φ ψ hφψ).ShortExact := sorry

end AlgebraicGeometry
