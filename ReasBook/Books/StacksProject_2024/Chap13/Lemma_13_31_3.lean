import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated
open ComplexShape

universe v u

namespace CochainComplex

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KHom" => HomotopyCategory 𝒜 (up ℤ)
local notation "AcycOrth" =>
  ObjectProperty.rightOrthogonal (HomotopyCategory.subcategoryAcyclic 𝒜)

-- Domain-style sampling for Lemma 13.31.3:
-- * primary domain: K-injective cochain complexes inside the triangulated homotopy category
--   `K(𝒜)`;
-- * sampled owner declarations:
--   `CochainComplex.isKInjective_iff_rightOrthogonal`,
--   `HomotopyCategory.subcategoryAcyclic`,
--   `ObjectProperty.rightOrthogonal`,
--   `ObjectProperty.ext_of_isTriangulatedClosed₁/₂/₃`;
-- * source/core/bridge triage:
--   `source-facing`: the three two-out-of-three statements below;
--   `core/canonical`: the object property
--   `(HomotopyCategory.subcategoryAcyclic 𝒜).rightOrthogonal`;
--   `bridge/view`: the equivalence `isKInjective_iff_rightOrthogonal`;
-- * primitive data: only the distinguished triangle `T` and the K-injectivity hypotheses on its
--   vertices;
-- * derived API: two-out-of-three for membership in the canonical right orthogonal.

-- Proof sketch: identify K-injective complexes with the right orthogonal to the acyclic
-- subcategory via `CochainComplex.isKInjective_iff_rightOrthogonal`. Right orthogonals are
-- triangulated, and `K(\mathcal A)` is triangulated, so `ObjectProperty.ext_of_isTriangulatedClosed₃`
-- gives the third vertex from the first two.
/-- Lemma 13.31.3: if `T` is a distinguished triangle in `K(\mathcal A)` and the first two
vertices are represented by K-injective cochain complexes, then the third vertex is represented by
a K-injective cochain complex. Together with the rotated companion lemmas below, this is the
two-out-of-three property for K-injective complexes in distinguished triangles. -/
theorem isKInjective_obj₃_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₁ : CochainComplex.IsKInjective T.obj₁.as) (h₂ : CochainComplex.IsKInjective T.obj₂.as) :
    CochainComplex.IsKInjective T.obj₃.as := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal] at h₁ h₂ ⊢
  exact (AcycOrth).ext_of_isTriangulatedClosed₃ T hT h₁ h₂

-- Proof sketch: rewrite K-injectivity as right orthogonality to acyclic complexes and use the
-- triangulated closure of right orthogonals together with
-- `ObjectProperty.ext_of_isTriangulatedClosed₂`.
/-- The `obj₁`-`obj₃` case of the K-injective two-out-of-three property in a distinguished
triangle of `K(\mathcal A)`. -/
theorem isKInjective_obj₂_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₁ : CochainComplex.IsKInjective T.obj₁.as) (h₃ : CochainComplex.IsKInjective T.obj₃.as) :
    CochainComplex.IsKInjective T.obj₂.as := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal] at h₁ h₃ ⊢
  exact (AcycOrth).ext_of_isTriangulatedClosed₂ T hT h₁ h₃

-- Proof sketch: after the same identification with a right orthogonal, apply
-- `ObjectProperty.ext_of_isTriangulatedClosed₁` to the distinguished triangle `T`.
/-- The `obj₂`-`obj₃` case of the K-injective two-out-of-three property in a distinguished
triangle of `K(\mathcal A)`. -/
theorem isKInjective_obj₁_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₂ : CochainComplex.IsKInjective T.obj₂.as) (h₃ : CochainComplex.IsKInjective T.obj₃.as) :
    CochainComplex.IsKInjective T.obj₁.as := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal] at h₂ h₃ ⊢
  exact (AcycOrth).ext_of_isTriangulatedClosed₁ T hT h₂ h₃

end

end CochainComplex
