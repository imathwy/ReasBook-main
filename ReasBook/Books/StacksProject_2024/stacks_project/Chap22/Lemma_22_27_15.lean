import StacksProject_2024.Chap22.Lemma_22_27_14

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Triangulated
open DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasAdmissibleCones R A]
variable [HasShift (K R A) ℤ]
variable [((Comp.inKFunctor : Comp R A ⥤ K R A)).CommShift ℤ]

-- Semantic recall hits: Situation `22.27.2` already fixes the source-facing cone owner
-- `HasAdmissibleCones.admissibleCone`, Lemma `22.27.12` exports the associated triangles
-- `AdmissibleCone.triangleInK`, and Lemma `22.27.14` provides the Chapter 22 pretriangulated
-- structure on `K(𝒜)` built from those triangles. The source-facing main statement here should
-- therefore live at the canonical triangle-level owner `CategoryTheory.Triangulated.Octahedron`.
-- The source's explicit third-row short complex is witness-level data derived from an octahedron,
-- so it should only be exported once that witness is constructed concretely rather than through a
-- public existential theorem.

/- Source/core/bridge triage for Lemma 22.27.15:
- `source-facing`: for admissible monomorphisms `α : x ⟶ y` and `β : y ⟶ z` in Situation
  `22.27.2`, the chosen associated triangles on `α`, `α ≫ β`, and `β` satisfy the octahedron
  axiom in `K(𝒜)`;
- `core/canonical`: `CategoryTheory.Triangulated.Octahedron`;
- `bridge/view`: the source's third-row short complex on the cone objects `c(α)`, `c(α ≫ β)`,
  and `c(β)`, together with the boundary comparison in `K(𝒜)` identifying its connecting
  morphism with the textbook composite `δ₃ ≫ p₁⟦(1 : ℤ)⟧'`; this witness-level bridge is not
  exported here until it is constructed without sorry-backed existential data.
-/

section

variable {x y z : Comp R A} (α : x ⟶ y) (β : y ⟶ z)

local notation "C₁₂" => HasAdmissibleCones.admissibleCone α
local notation "C₁₃" => HasAdmissibleCones.admissibleCone (α ≫ β)
local notation "C₂₃" => HasAdmissibleCones.admissibleCone β

section

variable [HasZeroObject (K R A)]
variable [Preadditive (K R A)]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor (K R A) n)]

/-- Lemma `22.27.15`: in Situation `22.27.2`, the three chosen cone triangles
`C₁₂.triangleInK`, `C₁₃.triangleInK`, and `C₂₃.triangleInK` fit into an octahedron in `K(𝒜)`.
This is the source-facing `TR4` owner for the Chapter 22 admissible-cone triangles. -/
@[stacks 09QX]
theorem admissibleConeTriangles_have_octahedron
    : Nonempty
        (Octahedron
          ((Comp.inKFunctor.map_comp α β).symm)
          (AdmissibleCone.triangleInK_distinguished C₁₂)
          (AdmissibleCone.triangleInK_distinguished C₂₃)
          (AdmissibleCone.triangleInK_distinguished C₁₃)) := by
  sorry

end

end

end
