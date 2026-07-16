import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling for Remark 13.34.4:
- primary domain: distinguished triangles and morphisms of triangles in a pretriangulated category;
- inspected owner declarations: `Triangle`, `TriangleMorphism`,
  `complete_distinguished_triangle_morphism₁`, and `CommSq`;
- owner abstraction: this remark is a bridge from a commuting square between the `mor₂` terms of
  two chosen Milnor triangles to a morphism of those triangles;
- primitive data: the two distinguished-triangle witnesses and the commuting `mor₂`-square;
  derived API: the resulting `TriangleMorphism` with prescribed second and third components. -/

private theorem exists_triangleMorphism_of_commSq_mor₂
    {T₁ T₂ : Triangle D}
    (hT₁ : T₁ ∈ distTriang D) (hT₂ : T₂ ∈ distTriang D)
    {b : T₁.obj₂ ⟶ T₂.obj₂} {c : T₁.obj₃ ⟶ T₂.obj₃}
    (hcomm : CommSq T₁.mor₂ b c T₂.mor₂) :
    ∃ φ : T₁ ⟶ T₂, φ.hom₂ = b ∧ φ.hom₃ = c := by
  obtain ⟨a, ha₁, ha₃⟩ :=
    complete_distinguished_triangle_morphism₁ T₁ T₂ hT₁ hT₂ b c hcomm.w
  refine ⟨Triangle.homMk T₁ T₂ a b c ?_ hcomm.w ?_, rfl, rfl⟩
  · simpa using ha₁
  · simpa using ha₃

-- Proof sketch: apply `Pretriangulated.complete_distinguished_triangle_morphism₁` to the two
-- chosen derived-limit triangles and to the commutative square defined by the product-level maps
-- `a'` and `a''`. The resulting first component is the dotted arrow `K ⟶ L`; the remark warns
-- that this component is generally not unique.
/-- Remark 13.34.4: for two chosen derived-limit triangles
`K ⟶ ∏ K_n ⟶ ∏ K_n ⟶ K[1]` and `L ⟶ ∏ L_n ⟶ ∏ L_n ⟶ L[1]`, if maps
`a', a'' : ∏ K_n ⟶ ∏ L_n` make the square between the two product terms commute, then they extend
to a morphism of distinguished triangles. Thus, once a morphism of pro-objects has produced such
maps `a'` and `a''`, it yields at least one map between the chosen derived limits, but no
uniqueness is asserted. -/
theorem exists_triangleMorphism_between_derivedLimit_triangles
    {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    {K L : D}
    {ιK : K ⟶ ∏ᶜ inverseSystemFamily Ksys}
    {δK : ∏ᶜ inverseSystemFamily Ksys ⟶ K⟦(1 : ℤ)⟧}
    {ιL : L ⟶ ∏ᶜ inverseSystemFamily Lsys}
    {δL : ∏ᶜ inverseSystemFamily Lsys ⟶ L⟦(1 : ℤ)⟧}
    {a' a'' : ∏ᶜ inverseSystemFamily Ksys ⟶ ∏ᶜ inverseSystemFamily Lsys}
    (hK :
      Triangle.mk ιK (derivedLimitDifferenceMap Ksys) δK ∈ distTriang D)
    (hL :
      Triangle.mk ιL (derivedLimitDifferenceMap Lsys) δL ∈ distTriang D)
    (hcomm :
      CommSq (derivedLimitDifferenceMap Ksys) a' a'' (derivedLimitDifferenceMap Lsys)) :
    ∃ φ :
        Triangle.mk ιK (derivedLimitDifferenceMap Ksys) δK ⟶
          Triangle.mk ιL (derivedLimitDifferenceMap Lsys) δL,
      φ.hom₂ = a' ∧ φ.hom₃ = a'' := by
  simpa using exists_triangleMorphism_of_commSq_mor₂ hK hL hcomm

end

end CategoryTheory
