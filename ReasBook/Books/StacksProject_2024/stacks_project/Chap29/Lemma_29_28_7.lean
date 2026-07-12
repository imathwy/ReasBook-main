import StacksProject_2024.Chap05.Definition_5_10_1
import StacksProject_2024.Chap29.Definition_29_28_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open AlgebraicGeometry

namespace AlgebraicGeometry
namespace Scheme.Hom

section

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)

-- Semantic recall: Chapter 29 uses `Scheme.Hom.fiber`, `Scheme.Hom.fiberToSpecResidueField`,
-- and the induced residue-field map on a point of the fiber; `Definition_5_10_1` fixes
-- `topologicalKrullDimAt` as the owner for fiberwise local dimension.

/-- The canonical `κ(s)`-algebra structure on the residue field of a point of the fiber `X_s`. -/
local instance fiberResidueFieldAlgebra (s : S) (x : f.fiber s) :
    Algebra (S.residueField s) ((f.fiber s).residueField x) :=
  (((Scheme.ΓSpecIso (S.residueField s)).inv ≫
      appTop (f.fiberToSpecResidueField s)).residueFieldMap x).hom.toAlgebra

local notation "fiberResidueFieldTrdeg" =>
  fun {s : S} (x : f.fiber s) ↦
    Cardinal.toNat (Algebra.trdeg (S.residueField s) ((f.fiber s).residueField x))

/-- Lemma 29.28.7 (1): for a locally finite type morphism of schemes, a nontrivial specialization
in a fixed fiber can only increase the local topological Krull dimension. -/
@[stacks 06RU "(1)"]
theorem topologicalKrullDimAt_le_of_specializes [LocallyOfFiniteType f] {s : S}
    {x x' : f.fiber s} (hxx' : Specializes x x') (hneq : x ≠ x') :
    topologicalKrullDimAt x ≤ topologicalKrullDimAt x' := sorry

/-- Lemma 29.28.7 (2): for a locally finite type morphism of schemes, a nontrivial specialization
in a fixed fiber strictly increases the Krull dimension of the local ring. -/
@[stacks 06RU "(2)"]
theorem ringKrullDim_stalk_lt_of_specializes [LocallyOfFiniteType f] {s : S}
    {x x' : f.fiber s} (hxx' : Specializes x x') (hneq : x ≠ x') :
    ringKrullDim ((f.fiber s).presheaf.stalk x) <
      ringKrullDim ((f.fiber s).presheaf.stalk x') := sorry

/-- Lemma 29.28.7 (3): for a locally finite type morphism of schemes, a nontrivial specialization
in a fixed fiber strictly decreases the transcendence degree of the residue field over the base
residue field seen by `fiberToSpecResidueField`. -/
@[stacks 06RU "(3)"]
theorem trdeg_residueField_gt_of_specializes [LocallyOfFiniteType f] {s : S}
    {x x' : f.fiber s} (hxx' : Specializes x x') (hneq : x ≠ x') :
    fiberResidueFieldTrdeg x > fiberResidueFieldTrdeg x' :=
  sorry

end

end Scheme.Hom
end AlgebraicGeometry
