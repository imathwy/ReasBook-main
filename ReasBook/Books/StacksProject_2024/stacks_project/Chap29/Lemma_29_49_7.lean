import Mathlib.AlgebraicGeometry.Morphisms.Separated
import StacksProject_2024.stacks_project.Chap29.Definition_29_49_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall note: `lean_leansearch` was rate-limited for this item, so the owner/API here
-- was verified directly against mathlib's `AlgebraicGeometry/FunctionField` and `Topology/Sober`.

section

variable {X : Scheme.{u}} [IsIntegral X]

/- The image of the local ring map `𝒪_{X, x} → R(X)`. -/
noncomputable abbrev stalkInFunctionField (x : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk x) X.functionField).range

/- The image in `R(X)` of the local ring at the generic point of an irreducible closed subset. -/
noncomputable abbrev genericPointStalkInFunctionField
    (Z : IrreducibleCloseds X) : Subring X.functionField :=
  X.stalkInFunctionField Z.isIrreducible.genericPoint

/-- Characterize membership in the image of the local ring map `𝒪_{X, x} → R(X)`. -/
@[simp] theorem mem_stalkInFunctionField_iff (x : X) (f : X.functionField) :
    f ∈ X.stalkInFunctionField x ↔
      ∃ a : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField a = f :=
  Iff.rfl

/-- Characterize membership in the image of the local ring at the generic point of an irreducible
closed subset inside the function field `R(X)`. -/
@[simp] theorem mem_genericPointStalkInFunctionField_iff
    (Z : IrreducibleCloseds X) (f : X.functionField) :
    f ∈ X.genericPointStalkInFunctionField Z ↔
      ∃ a : X.presheaf.stalk Z.isIrreducible.genericPoint,
        algebraMap (X.presheaf.stalk Z.isIrreducible.genericPoint) X.functionField a = f := by
  simpa [genericPointStalkInFunctionField] using
    X.mem_stalkInFunctionField_iff Z.isIrreducible.genericPoint f

section

variable [X.IsSeparated]

/-- Lemma 29.49.7 (1): if `Z₁` and `Z₂` are distinct irreducible closed subsets of an integral
separated scheme `X`, and `Z₁` is not contained in `Z₂`, then the local ring at the generic point
of `Z₁` is not contained in the local ring at the generic point of `Z₂` inside the function field
`R(X) = X.functionField`. -/
theorem genericPointStalkRange_not_subset_of_not_subset
    (Z₁ Z₂ : IrreducibleCloseds X) (hnot : ¬ (Z₁ : Set X) ⊆ Z₂) :
    ¬ X.genericPointStalkInFunctionField Z₁ ≤ X.genericPointStalkInFunctionField Z₂ := sorry

/-- Lemma 29.49.7 (2): if `x` is a closed point of an integral separated scheme `X` and
`x ∉ Z₂`, then some function regular on a neighborhood of `x` does not lie in the local ring at
the generic point of `Z₂` inside the function field `R(X) = X.functionField`. -/
theorem exists_regularFunction_near_closedPoint_not_mem_genericPointStalk
    (Z₂ : IrreducibleCloseds X) (x : X) (hxClosed : IsClosed ({x} : Set X))
    (hxNotMem : x ∉ (Z₂ : Set X)) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : Γ(X, U)),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hxU f) ∉
        X.genericPointStalkInFunctionField Z₂ := sorry

end

end

end AlgebraicGeometry.Scheme
