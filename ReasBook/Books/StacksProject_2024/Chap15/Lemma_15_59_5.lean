import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open ComplexShape HomotopyCategory MonoidalCategory

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

/- Domain-style sampling for Lemma 15.59.5:
- primary domain: K-flat objects in the homotopy category `K(C)` of cochain complexes in a
  monoidal preadditive category, together with the distinguished-triangle owner API on `K(C)`;
- sampled owner declarations:
  `HomotopyCategory.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `HomotopyCategory.subcategoryAcyclic`,
  `ObjectProperty.IsTriangulatedClosed₁/₂/₃`;
- best owner abstraction: the source-facing statements remain the three `obj₁`/`obj₂`/`obj₃`
  closure theorems for `K.IsKFlat`, but their natural canonical owner layer is the object property
  on `K(C)` given by `K ↦ K.IsKFlat`; the acyclicity argument belongs to the canonical
  triangulated object property `HomotopyCategory.subcategoryAcyclic C`, not to a parallel local
  tensor wrapper;
- primitive vs derived:
  primitive data are only the distinguished triangle `T` and the K-flatness hypotheses on its
  vertices;
  the two-out-of-three closure mechanism is derived API from the triangulated object-property layer
  on `K(C)`, and does not require extra ambient assumptions such as abelianness, homology, or
  cocompleteness in the public theorem headers.

Source/core/bridge triage:
* `source-facing`: the three two-out-of-three closure statements for `IsKFlat` in distinguished
  triangles of `K(C)`;
* `core/canonical`: `HomotopyCategory.IsKFlat`, `HomotopyCategory.subcategoryAcyclic C`, and the
  canonical mapping-cone distinguished triangles in `K(C)`;
* `bridge/view`: the identification of K-flatness with preservation of acyclicity after tensoring
  against an acyclic test complex. -/

-- Proof sketch: K-flatness is an object property on `K(C)` via `K ↦ K.IsKFlat`. The proof of
-- closure under isomorphisms compares chosen representatives of isomorphic homotopy-category
-- objects, and the triangulated-owner proof tensors a distinguished triangle with an arbitrary
-- acyclic test complex and uses the two-out-of-three property of
-- `HomotopyCategory.subcategoryAcyclic C`.
/-- The K-flat objects of `K(C)` form an object property closed under isomorphisms. -/
instance isKFlat_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : KHom ↦ K.IsKFlat) where
  of_iso e hK := by
    sorry

/-- Canonical owner form of Lemma 15.59.5: the K-flat objects of `K(C)` form a triangulated
object property. -/
instance isKFlat_isTriangulated :
    ObjectProperty.IsTriangulated (fun K : KHom ↦ K.IsKFlat) where
  exists_zero := by
    sorry
  isStableUnderShiftBy n := by
    refine .mk ?_
    intro K hK
    sorry
  ext₂' T hT h₁ h₃ := by
    sorry

end

section

variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [MonoidalCategory C]
variable [(curriedTensor C).Additive]
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
  let P : ObjectProperty KHom := fun K ↦ K.IsKFlat
  exact P.ext_of_isTriangulatedClosed₃ T hT h₁ h₂

/-- Lemma 15.59.5 (2): if `T` is a distinguished triangle in `K(C)` and the first and third
vertices are represented by K-flat cochain complexes, then the second vertex is also represented
by a K-flat cochain complex. -/
theorem isKFlat_obj₂_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₁ : T.obj₁.IsKFlat)
    (h₃ : T.obj₃.IsKFlat) :
    T.obj₂.IsKFlat := by
  let P : ObjectProperty KHom := fun K ↦ K.IsKFlat
  exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

/-- Lemma 15.59.5 (3): if `T` is a distinguished triangle in `K(C)` and the second and third
vertices are represented by K-flat cochain complexes, then the first vertex is also represented by
a K-flat cochain complex. -/
theorem isKFlat_obj₁_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₂ : T.obj₂.IsKFlat)
    (h₃ : T.obj₃.IsKFlat) :
    T.obj₁.IsKFlat := by
  let P : ObjectProperty KHom := fun K ↦ K.IsKFlat
  exact P.ext_of_isTriangulatedClosed₁ T hT h₂ h₃

end

end CochainComplex
