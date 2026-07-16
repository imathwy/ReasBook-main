import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Triangulated.Subcategory
import stacks_proof.stacks_project.Chap15.Definition_15_59_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open ComplexShape HomotopyCategory MonoidalCategory
open scoped ZeroObject

noncomputable section

universe v u

namespace CochainComplex

section

variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]
variable [∀ (X Y : CochainComplex C ℤ), CochainComplex.HasMapBifunctor X Y (curriedTensor C)]

local notation "KHom" => HomotopyCategory C (up ℤ)

/-- The K-flat objects of `K(C)` form an object property closed under isomorphisms. -/
instance isKFlat_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : KHom ↦ K.IsKFlat) := by
  infer_instance

/-- Canonical owner form of Lemma 15.59.5: the K-flat objects of `K(C)` form a triangulated
object property. -/
instance isKFlat_isTriangulated :
    ObjectProperty.IsTriangulated (fun K : KHom ↦ K.IsKFlat) := by
  infer_instance

end

section

variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]
variable [∀ (X Y : CochainComplex C ℤ), CochainComplex.HasMapBifunctor X Y (curriedTensor C)]

local notation "KHom" => HomotopyCategory C (up ℤ)

/-- Lemma 15.59.5 (1): if `T` is a distinguished triangle in `K(C)` and the first two vertices are
represented by K-flat cochain complexes, then the third vertex is also represented by a K-flat
cochain complex. -/
@[stacks 06Y2]
theorem isKFlat_obj₃_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₁ : T.obj₁.IsKFlat)
    (h₂ : T.obj₂.IsKFlat) :
    T.obj₃.IsKFlat := by
  -- Apply the generic third-vertex closure axiom for the local `K`-flat object property.
  let P : ObjectProperty KHom := fun K ↦ K.IsKFlat
  exact P.ext_of_isTriangulatedClosed₃ T hT h₁ h₂

/-- Lemma 15.59.5 (2): if `T` is a distinguished triangle in `K(C)` and the first and third
vertices are represented by K-flat cochain complexes, then the second vertex is also represented
by a K-flat cochain complex. -/
@[stacks 06Y2]
theorem isKFlat_obj₂_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₁ : T.obj₁.IsKFlat)
    (h₃ : T.obj₃.IsKFlat) :
    T.obj₂.IsKFlat := by
  -- Apply the generic middle-vertex closure axiom for the local `K`-flat object property.
  let P : ObjectProperty KHom := fun K ↦ K.IsKFlat
  exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

/-- Lemma 15.59.5 (3): if `T` is a distinguished triangle in `K(C)` and the second and third
vertices are represented by K-flat cochain complexes, then the first vertex is also represented by
a K-flat cochain complex. -/
@[stacks 06Y2]
theorem isKFlat_obj₁_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₂ : T.obj₂.IsKFlat)
    (h₃ : T.obj₃.IsKFlat) :
    T.obj₁.IsKFlat := by
  -- Apply the generic first-vertex closure axiom for the local `K`-flat object property.
  let P : ObjectProperty KHom := fun K ↦ K.IsKFlat
  exact P.ext_of_isTriangulatedClosed₁ T hT h₂ h₃

end

end CochainComplex
