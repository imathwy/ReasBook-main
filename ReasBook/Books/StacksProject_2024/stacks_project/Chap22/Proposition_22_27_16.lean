import StacksProject_2024.stacks_project.Chap22.Lemma_22_27_15

open CategoryTheory
open DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasAdmissibleCones R A]
variable [HasShift (K R A) ℤ]
variable [((Comp.inKFunctor : Comp R A ⥤ K R A)).CommShift ℤ]
variable [Limits.HasZeroObject (K R A)]
variable [Preadditive (K R A)]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor (K R A) n)]

/- Proposition 22.27.16: under Situation `22.27.2`, the Chapter 22 homotopy category `K(𝒜)` is
triangulated. This is the canonical owner `CategoryTheory.IsTriangulated`, built from the
source-facing pretriangulated structure of Lemma `22.27.14` and the admissible-cone octahedron
datum of Lemma `22.27.15` via the standard reduction constructor `CategoryTheory.IsTriangulated.mk'`.
-/
noncomputable instance instIsTriangulatedK : IsTriangulated (K R A) :=
  IsTriangulated.mk' (by
    rintro ⟨X₁⟩ ⟨X₂⟩ ⟨X₃⟩ u₁₂' u₂₃'
    obtain ⟨u₁₂, rfl⟩ := Quotient.exists_rep u₁₂'
    obtain ⟨u₂₃, rfl⟩ := Quotient.exists_rep u₂₃'
    let C₁₂ := HasAdmissibleCones.admissibleCone u₁₂
    let C₂₃ := HasAdmissibleCones.admissibleCone u₂₃
    let C₁₃ := HasAdmissibleCones.admissibleCone (u₁₂ ≫ u₂₃)
    refine ⟨⟨X₁⟩, ⟨X₂⟩, ⟨X₃⟩, C₁₂.obj.inK, C₂₃.obj.inK, C₁₃.obj.inK, u₁₂.inK, u₂₃.inK,
        Iso.refl _, Iso.refl _, Iso.refl _, ?_, ?_,
        C₁₂.triangleInK.mor₂, C₁₂.triangleInK.mor₃, ?_,
        C₂₃.triangleInK.mor₂, C₂₃.triangleInK.mor₃, ?_,
        C₁₃.triangleInK.mor₂, C₁₃.triangleInK.mor₃, ?_, ?_⟩
    · calc
        ⟦u₁₂⟧ ≫ (Iso.refl _).hom = ⟦u₁₂⟧ := by simp
        _ = u₁₂.inK := rfl
        _ = (Iso.refl _).hom ≫ u₁₂.inK := by simp
    · calc
        ⟦u₂₃⟧ ≫ (Iso.refl _).hom = ⟦u₂₃⟧ := by simp
        _ = u₂₃.inK := rfl
        _ = (Iso.refl _).hom ≫ u₂₃.inK := by simp
    · change C₁₂.triangleInK ∈ distTriang (K R A)
      exact C₁₂.triangleInK_distinguished
    · change C₂₃.triangleInK ∈ distTriang (K R A)
      exact C₂₃.triangleInK_distinguished
    · change C₁₃.triangleInK ∈ distTriang (K R A)
      exact C₁₃.triangleInK_distinguished
    simpa using admissibleConeTriangles_have_octahedron u₁₂ u₂₃)

/-- Proposition 22.27.16: in Situation `22.27.2`, the homotopy category `K(𝒜)` with its natural
translation functors and distinguished triangles is triangulated. -/
@[stacks 09QY]
theorem isTriangulatedK : IsTriangulated (K R A) := inferInstance

end
