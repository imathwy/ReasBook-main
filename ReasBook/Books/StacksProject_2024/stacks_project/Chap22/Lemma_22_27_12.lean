import Mathlib.CategoryTheory.Triangulated.Functor
import StacksProject_2024.Chap22.Lemma_22_27_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated
open DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable [CompBoundaryMap R A]

variable [HasShift (K R A) ℤ]
variable [((Comp.inKFunctor : Comp R A ⥤ K R A)).CommShift ℤ]

namespace AdmissibleCone

/-- The associated triangle in `K(𝒜)` attached to an admissible cone. -/
abbrev triangleInK
    {x y : Comp R A}
    {f : x ⟶ y}
    (C : AdmissibleCone f) :
    Triangle (K R A) :=
  Triangle.mk
    f.inK
    C.toCone.inK
    (C.toShift.inK ≫
      (((Comp.inKFunctor : Comp R A ⥤ K R A).commShiftIso (1 : ℤ)).hom.app x))

@[simp] theorem triangleInK_mor₁
    {x y : Comp R A}
    {f : x ⟶ y}
    (C : AdmissibleCone f) :
    C.triangleInK.mor₁ = f.inK :=
  rfl

@[simp] theorem triangleInK_mor₂
    {x y : Comp R A}
    {f : x ⟶ y}
    (C : AdmissibleCone f) :
    C.triangleInK.mor₂ = C.toCone.inK :=
  rfl

@[simp] theorem triangleInK_mor₃
    {x y : Comp R A}
    {f : x ⟶ y}
    (C : AdmissibleCone f) :
    C.triangleInK.mor₃ =
      C.toShift.inK ≫
        (((Comp.inKFunctor : Comp R A ⥤ K R A).commShiftIso (1 : ℤ)).hom.app x) :=
  rfl

/-- Assemble the induced morphism between the associated triangles in `K(𝒜)` from the three
commutative squares expressing that `(a, b, c)` is a triangle morphism. -/
abbrev homInK
    {x₁ y₁ x₂ y₂ : Comp R A}
    {f₁ : x₁ ⟶ y₁}
    {f₂ : x₂ ⟶ y₂}
    (C₁ : AdmissibleCone f₁)
    (C₂ : AdmissibleCone f₂)
    {a : x₁ ⟶ x₂}
    {b : y₁ ⟶ y₂}
    {c : C₁.obj ⟶ C₂.obj}
    (sq₁ : CommSq C₁.triangleInK.mor₁ a.inK b.inK C₂.triangleInK.mor₁)
    (sq₂ : CommSq C₁.triangleInK.mor₂ b.inK c.inK C₂.triangleInK.mor₂)
    (sq₃ : CommSq C₁.triangleInK.mor₃ c.inK (a.inK⟦(1 : ℤ)⟧') C₂.triangleInK.mor₃) :
    C₁.triangleInK ⟶ C₂.triangleInK :=
  Triangle.homMk _ _ a.inK b.inK c.inK sq₁.w sq₂.w sq₃.w

@[simp] theorem homInK_hom₁
    {x₁ y₁ x₂ y₂ : Comp R A}
    {f₁ : x₁ ⟶ y₁}
    {f₂ : x₂ ⟶ y₂}
    (C₁ : AdmissibleCone f₁)
    (C₂ : AdmissibleCone f₂)
    {a : x₁ ⟶ x₂}
    {b : y₁ ⟶ y₂}
    {c : C₁.obj ⟶ C₂.obj}
    (sq₁ : CommSq C₁.triangleInK.mor₁ a.inK b.inK C₂.triangleInK.mor₁)
    (sq₂ : CommSq C₁.triangleInK.mor₂ b.inK c.inK C₂.triangleInK.mor₂)
    (sq₃ : CommSq C₁.triangleInK.mor₃ c.inK (a.inK⟦(1 : ℤ)⟧') C₂.triangleInK.mor₃) :
    (C₁.homInK C₂ sq₁ sq₂ sq₃).hom₁ = a.inK :=
  rfl

@[simp] theorem homInK_hom₂
    {x₁ y₁ x₂ y₂ : Comp R A}
    {f₁ : x₁ ⟶ y₁}
    {f₂ : x₂ ⟶ y₂}
    (C₁ : AdmissibleCone f₁)
    (C₂ : AdmissibleCone f₂)
    {a : x₁ ⟶ x₂}
    {b : y₁ ⟶ y₂}
    {c : C₁.obj ⟶ C₂.obj}
    (sq₁ : CommSq C₁.triangleInK.mor₁ a.inK b.inK C₂.triangleInK.mor₁)
    (sq₂ : CommSq C₁.triangleInK.mor₂ b.inK c.inK C₂.triangleInK.mor₂)
    (sq₃ : CommSq C₁.triangleInK.mor₃ c.inK (a.inK⟦(1 : ℤ)⟧') C₂.triangleInK.mor₃) :
    (C₁.homInK C₂ sq₁ sq₂ sq₃).hom₂ = b.inK :=
  rfl

@[simp] theorem homInK_hom₃
    {x₁ y₁ x₂ y₂ : Comp R A}
    {f₁ : x₁ ⟶ y₁}
    {f₂ : x₂ ⟶ y₂}
    (C₁ : AdmissibleCone f₁)
    (C₂ : AdmissibleCone f₂)
    {a : x₁ ⟶ x₂}
    {b : y₁ ⟶ y₂}
    {c : C₁.obj ⟶ C₂.obj}
    (sq₁ : CommSq C₁.triangleInK.mor₁ a.inK b.inK C₂.triangleInK.mor₁)
    (sq₂ : CommSq C₁.triangleInK.mor₂ b.inK c.inK C₂.triangleInK.mor₂)
    (sq₃ : CommSq C₁.triangleInK.mor₃ c.inK (a.inK⟦(1 : ℤ)⟧') C₂.triangleInK.mor₃) :
    (C₁.homInK C₂ sq₁ sq₂ sq₃).hom₃ = c.inK :=
  rfl

section Distinguished

variable [Limits.HasZeroObject (K R A)]
variable [Preadditive (K R A)]
variable [∀ n : ℤ, (shiftFunctor (K R A) n).Additive]
variable [Pretriangulated (K R A)]

/-- Bridge/view companion for Section `22.27`: once the ambient Chapter 22 triangulated structure
on `K(𝒜)` is available, the triangle in `K(𝒜)` attached to an admissible cone is distinguished.
This is the canonical owner needed to feed admissible-cone triangle morphisms into
`Pretriangulated.isIso₃_of_isIso₁₂`. -/
theorem triangleInK_distinguished
    {x y : Comp R A}
    {f : x ⟶ y}
    (C : AdmissibleCone f) :
    C.triangleInK ∈ distTriang (K R A) := by
  sorry

end Distinguished

end AdmissibleCone

-- Semantic recall hits: `Triangle`, `TriangleMorphism`, and `Triangle.homMk` are the canonical
-- category-theoretic owners for the associated cone triangles in `K(𝒜)`. The Chapter 13 file
-- `Lemma_13_9_13` records the same two-out-of-three pattern for standard mapping-cone triangles,
-- so this source-facing admissible-cone statement should bridge directly to a canonical triangle
-- morphism rather than package a parallel local wrapper.

section TriangleInKMorphism

variable {x₁ y₁ x₂ y₂ : Comp R A}
variable {f₁ : x₁ ⟶ y₁}
variable {f₂ : x₂ ⟶ y₂}
variable {C₁ : AdmissibleCone f₁}
variable {C₂ : AdmissibleCone f₂}
variable [Limits.HasZeroObject (K R A)]
variable [Preadditive (K R A)]
variable [∀ n : ℤ, (shiftFunctor (K R A) n).Additive]
variable [Pretriangulated (K R A)]

variable (C₁) (C₂)
variable {a : x₁ ⟶ x₂}
variable {b : y₁ ⟶ y₂}
variable {c : C₁.obj ⟶ C₂.obj}

/-- Lemma 22.27.12: if `a`, `b`, and `c` form a morphism between the triangles in `K(𝒜)`
associated to chosen admissible cones on `f₁` and `f₂`, and if `a` and `b` become isomorphisms in
`K(𝒜)`, then so does `c`. The repository-facing formulation uses the canonical morphism property
`Comp.homotopyEquivalences`. -/
@[stacks 09QT]
theorem homotopyEquivalences_coneMap_of_triangleMorphism
    (sq₁ : CommSq C₁.triangleInK.mor₁ a.inK b.inK C₂.triangleInK.mor₁)
    (sq₂ : CommSq C₁.triangleInK.mor₂ b.inK c.inK C₂.triangleInK.mor₂)
    (sq₃ : CommSq C₁.triangleInK.mor₃ c.inK (a.inK⟦(1 : ℤ)⟧') C₂.triangleInK.mor₃)
    (ha : Comp.homotopyEquivalences a)
    (hb : Comp.homotopyEquivalences b) :
    Comp.homotopyEquivalences c := by
  let φ := C₁.homInK C₂ sq₁ sq₂ sq₃
  have hφ₃ : IsIso φ.hom₃ := by
    letI : IsIso φ.hom₁ := by
      simpa [φ, Comp.homotopyEquivalences] using ha
    letI : IsIso φ.hom₂ := by
      simpa [φ, Comp.homotopyEquivalences] using hb
    exact
      Pretriangulated.isIso₃_of_isIso₁₂ φ
        C₁.triangleInK_distinguished
        C₂.triangleInK_distinguished
        inferInstance inferInstance
  simpa [φ, Comp.homotopyEquivalences] using hφ₃

end TriangleInKMorphism

end
