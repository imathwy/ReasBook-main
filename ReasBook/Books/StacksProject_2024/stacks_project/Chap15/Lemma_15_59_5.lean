import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.Chap15.Definition_15_59_1

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
variable [MonoidalCategory C] [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]

local notation "KHom" => HomotopyCategory C (up ℤ)

/-- The K-flat objects of `K(C)` form an object property closed under isomorphisms. -/
instance isKFlat_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : KHom ↦ K.IsKFlat) := by
  sorry

/-- Canonical owner form of Lemma 15.59.5: the K-flat objects of `K(C)` form a triangulated
object property. -/
instance isKFlat_isTriangulated :
    ObjectProperty.IsTriangulated (fun K : KHom ↦ K.IsKFlat) := by
  sorry

end

section

variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [MonoidalCategory C] [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]

local notation "KHom" => HomotopyCategory C (up ℤ)

/-- Lemma 15.59.5 (1): if `T` is a distinguished triangle in `K(C)` and the first two vertices are
represented by K-flat cochain complexes, then the third vertex is also represented by a K-flat
cochain complex. -/
theorem isKFlat_obj₃_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₁ : T.obj₁.IsKFlat)
    (h₂ : T.obj₂.IsKFlat) :
    T.obj₃.IsKFlat := by
  exact
    ObjectProperty.ext_of_isTriangulatedClosed₃ (fun K : KHom ↦ K.IsKFlat) T hT h₁ h₂

/-- Lemma 15.59.5 (2): if `T` is a distinguished triangle in `K(C)` and the first and third
vertices are represented by K-flat cochain complexes, then the second vertex is also represented
by a K-flat cochain complex. -/
theorem isKFlat_obj₂_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₁ : T.obj₁.IsKFlat)
    (h₃ : T.obj₃.IsKFlat) :
    T.obj₂.IsKFlat := by
  exact
    ObjectProperty.ext_of_isTriangulatedClosed₂ (fun K : KHom ↦ K.IsKFlat) T hT h₁ h₃

/-- Lemma 15.59.5 (3): if `T` is a distinguished triangle in `K(C)` and the second and third
vertices are represented by K-flat cochain complexes, then the first vertex is also represented by
a K-flat cochain complex. -/
theorem isKFlat_obj₁_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₂ : T.obj₂.IsKFlat)
    (h₃ : T.obj₃.IsKFlat) :
    T.obj₁.IsKFlat := by
  exact
    ObjectProperty.ext_of_isTriangulatedClosed₁ (fun K : KHom ↦ K.IsKFlat) T hT h₂ h₃

end

end CochainComplex
