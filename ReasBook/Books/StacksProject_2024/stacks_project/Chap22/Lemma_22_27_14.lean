import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import StacksProject_2024.stacks_project.Chap22.Lemma_22_27_12

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated

universe u v w

namespace DifferentialGradedCategory

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasAdmissibleCones R A]
variable [HasShift (K R A) ℤ]
variable [((Comp.inKFunctor : Comp R A ⥤ K R A)).CommShift ℤ]

/- Source/core/bridge triage for Lemma 22.27.14:
- `source-facing`: the statement that the Chapter 22 homotopy category `K(𝒜)` with its chosen
  shift functors and chosen admissible-cone triangles is pretriangulated;
- `core/canonical`: `CategoryTheory.Pretriangulated`;
- `bridge/view`: the Chapter 22 distinguished triangles on `K R A`, defined as the triangles
  isomorphic to the chosen cone triangles `HasAdmissibleCones.admissibleCone f`.

The concrete non-Prop data here is the source-facing class of distinguished triangles. The TR1,
TR2, and TR3 verification remains proof debt and is therefore left in proof fields only.
-/

namespace HasAdmissibleCones

/-- The Chapter 22 distinguished triangles on `K(𝒜)`: those isomorphic to the triangle attached
to the chosen admissible cone on some morphism in `Comp(𝒜)`. -/
def distinguishedTrianglesInK : Set (Triangle (K R A)) :=
  { T | ∃ (x y : Comp R A) (f : x ⟶ y),
      Nonempty (T ≅ (HasAdmissibleCones.admissibleCone f).triangleInK) }

/-- Membership in `distinguishedTrianglesInK` is exactly being isomorphic to one of the chosen
admissible-cone triangles from Situation `22.27.2`. -/
theorem mem_distinguishedTrianglesInK {T : Triangle (K R A)} :
    T ∈ distinguishedTrianglesInK ↔
      ∃ (x y : Comp R A) (f : x ⟶ y),
        Nonempty (T ≅ (HasAdmissibleCones.admissibleCone f).triangleInK) :=
  Iff.rfl

/-- The triangle attached to the chosen admissible cone on `f` is distinguished by definition. -/
@[simp] theorem admissibleCone_triangleInK_mem_distinguishedTrianglesInK
    {x y : Comp R A} (f : x ⟶ y) :
    (HasAdmissibleCones.admissibleCone f).triangleInK ∈
      distinguishedTrianglesInK :=
  ⟨x, y, f, ⟨Iso.refl _⟩⟩

end HasAdmissibleCones

variable [Limits.HasZeroObject (K R A)]
variable [Preadditive (K R A)]
variable [∀ n : ℤ, (shiftFunctor (K R A) n).Additive]

/-- Lemma 22.27.14: under Situation `22.27.2`, the Chapter 22 homotopy category `K(𝒜)` is
pretriangulated, with distinguished triangles given by the triangles isomorphic to the chosen
admissible-cone triangles. The concrete owner data is
`HasAdmissibleCones.distinguishedTrianglesInK`; the TR1, TR2, and TR3 proofs are deferred to the
proof stage. -/
@[stacks 09QW]
noncomputable instance instPretriangulatedK : Pretriangulated (K R A) where
  distinguishedTriangles := HasAdmissibleCones.distinguishedTrianglesInK
  isomorphic_distinguished := by
    intro T₁ hT₁ T₂ e
    rcases hT₁ with ⟨x, y, f, ⟨i⟩⟩
    exact ⟨x, y, f, ⟨e ≪≫ i⟩⟩
  contractible_distinguished := by
    sorry
  distinguished_cocone_triangle := by
    intro X Y f
    sorry
  rotate_distinguished_triangle := by
    intro T
    sorry
  complete_distinguished_triangle_morphism := by
    intro T₁ T₂ hT₁ hT₂ a b hab
    sorry

end

end DifferentialGradedCategory
