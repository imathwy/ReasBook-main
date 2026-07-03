import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap04.Definition_4_27_20
import StacksProject_2024.Chap04.Remark_4_27_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open scoped MorphismPropertyUnder

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-
Domain-style sampling:
- primary domain: denominator categories in a pretriangulated category, built from morphisms from
  a fixed triangle into distinguished triangles;
- sampled owner declarations:
  `ObjectProperty.FullSubcategory`,
  `MorphismProperty.Under`,
  `MorphismProperty.localizationTargetArrows_isFiltered`,
  `Triangle.π₁`, `Triangle.π₂`, `Triangle.π₃`;
- best owner abstraction: the source-facing object is the full subcategory of `Under T`
  consisting of arrows to distinguished triangles whose three components lie in `S`, and the
  public derived API should be the three projection functors to the denominator categories over
  the vertices of `T`.

Primitive-vs-derived split:
- primitive data: an object of `Under T`, together with the conditions that its target triangle is
  distinguished and its three components lie in `S`;
- derived API: the full subcategory
  `distinguished_triangle_denominators S T`, its three projection functors, and the cofinality and
  filteredness theorems below.

Source/core/bridge triage:
- `source-facing`: `distinguished_triangle_denominators S T` and the projection functors to
  `T.objᵢ / S`;
- `core/canonical`: `ObjectProperty.FullSubcategory` on `Under T` and the canonical denominator
  owner `T.objᵢ / S`;
- `bridge/view`: the private predicate cutting out the full subcategory and the private generic
  projection helper.
-/

private abbrev triangleDenominatorProperty (S : MorphismProperty D) (T : Triangle D) :
    ObjectProperty (Under T) :=
  fun U ↦ U.right ∈ distTriang D ∧ S U.hom.hom₁ ∧ S U.hom.hom₂ ∧ S U.hom.hom₃

/-- The category of morphisms from `T` to distinguished triangles whose three components lie in
`S`, realized as the corresponding full subcategory of `Under T`. -/
abbrev distinguished_triangle_denominators (S : MorphismProperty D) (T : Triangle D) : Type _ :=
  (triangleDenominatorProperty S T).FullSubcategory

/-- A triangle projection `πᵢ : Triangle D ⥤ D` canonically yields a functor from `Under T` to
the under-category over `πᵢ.obj T` by applying `πᵢ` to the structural arrows. -/
private def triangle_projection_to_under (T : Triangle D) (π : Triangle D ⥤ D) :
    Under T ⥤ Under (π.obj T) :=
  Functor.toUnder (Under.forget T ⋙ π) (π.obj T) (fun U ↦ π.map U.hom) fun {U V} f ↦ by
    change π.map U.hom ≫ π.map f.right = π.map V.hom
    rw [← π.map_comp]
    exact congrArg (fun φ ↦ π.map φ) (Under.w f)

/-- A triangle projection `πᵢ : Triangle D ⥤ D` induces a projection from the
triangle-denominator category to the corresponding denominator category under `πᵢ.obj T`. -/
private def distinguished_triangle_denominators_to_under
    (S : MorphismProperty D) (T : Triangle D) (π : Triangle D ⥤ D)
    (hπ : ∀ U : Under T, triangleDenominatorProperty S T U → S (π.map U.hom)) :
    distinguished_triangle_denominators S T ⥤ π.obj T / S :=
  MorphismProperty.Comma.lift
    ((triangleDenominatorProperty S T).ι ⋙ triangle_projection_to_under T π)
    (fun U ↦ hπ U.obj U.property)
    (fun {_ _} _ ↦ trivial)
    (fun {_ _} _ ↦ trivial)

/-- The projection from the triangle-denominator category to the under-category over the first
vertex of `T`, remembering only the first component of a morphism of triangles. -/
def distinguished_triangle_denominators_to_under_one (S : MorphismProperty D) (T : Triangle D) :
    distinguished_triangle_denominators S T ⥤ T.obj₁ / S :=
  distinguished_triangle_denominators_to_under S T Triangle.π₁
    fun _ hU ↦ hU.2.1

/-- The projection from the triangle-denominator category to the under-category over the second
vertex of `T`, remembering only the second component of a morphism of triangles. -/
def distinguished_triangle_denominators_to_under_two (S : MorphismProperty D) (T : Triangle D) :
    distinguished_triangle_denominators S T ⥤ T.obj₂ / S :=
  distinguished_triangle_denominators_to_under S T Triangle.π₂
    fun _ hU ↦ hU.2.2.1

/-- The projection from the triangle-denominator category to the under-category over the third
vertex of `T`, remembering only the third component of a morphism of triangles. -/
def distinguished_triangle_denominators_to_under_three (S : MorphismProperty D) (T : Triangle D) :
    distinguished_triangle_denominators S T ⥤ T.obj₃ / S :=
  distinguished_triangle_denominators_to_under S T Triangle.π₃
    fun _ hU ↦ hU.2.2.2

variable (S : MorphismProperty D) [IsSaturatedMultiplicativeSystem S]
  [S.IsCompatibleWithTriangulation] (T : Triangle D)

-- Proof sketch: complete any arrow in `S` out of `T.obj₁` to a morphism of distinguished
-- triangles using the compatibility axiom of `S`, use saturation to control arrows in the
-- localization, and then verify the structured-arrow connectedness criterion for cofinality.
/-- The first projection from the triangle-denominator category to the under-category over
`T.obj₁` is cofinal. -/
theorem distinguished_triangle_denominators_to_under_one_final
    (hT : T ∈ distTriang D) :
    (distinguished_triangle_denominators_to_under_one S T).Final := sorry

-- Proof sketch: use the compatibility of `S` with the triangulated structure to complete arrows
-- in `S` to morphisms of distinguished triangles, obtaining surjectivity of the first projection
-- on objects and arrows; use rotation to transfer the same statements to the other two
-- projections; and then verify the three filteredness axioms by reducing to the filtered
-- denominator categories over the three vertices of `T`.
/-- Lemma 13.5.10: let `T` be a distinguished triangle in a pretriangulated category `D`, and let
`S` be a saturated multiplicative system compatible with the triangulated structure. Then the
category of morphisms of triangles from `T` to distinguished triangles whose three components lie
in `S` is filtered. The three canonical projections to the denominator categories over the
vertices of `T` are defined above and shown cofinal in the companion theorems. -/
theorem distinguished_triangle_denominators_are_filtered
    (hT : T ∈ distTriang D) :
    IsFiltered (distinguished_triangle_denominators S T) := sorry

-- Proof sketch: rotate distinguished triangles and apply the cofinality statement for the first
-- projection to identify the second projection with the same argument after rotation.
/-- The second projection from the triangle-denominator category to the under-category over
`T.obj₂` is cofinal. -/
theorem distinguished_triangle_denominators_to_under_two_final
    (hT : T ∈ distTriang D) :
    (distinguished_triangle_denominators_to_under_two S T).Final := sorry

-- Proof sketch: rotate distinguished triangles twice and reduce the third projection to the first
-- projection after transporting the denominator category along the rotation equivalence.
/-- The third projection from the triangle-denominator category to the under-category over
`T.obj₃` is cofinal. -/
theorem distinguished_triangle_denominators_to_under_three_final
    (hT : T ∈ distTriang D) :
    (distinguished_triangle_denominators_to_under_three S T).Final := sorry

end

end CategoryTheory
