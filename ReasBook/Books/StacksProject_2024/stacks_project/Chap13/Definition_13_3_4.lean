import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.ObjectProperty

open Limits

/- Domain-style sampling for Definition 13.3.4:
- primary domain: triangulated subcategories of a pretriangulated category, expressed as object
  properties stable under the canonical triangulated operations;
- sampled core/canonical declarations:
  `ObjectProperty.IsTriangulated`,
  `Pretriangulated P.FullSubcategory`,
  `IsTriangulated P.FullSubcategory`;
- best owner abstraction: `ObjectProperty.IsTriangulated P`;
- primitive data: only the object property `P : ObjectProperty C`;
- derived API: the induced pretriangulated structure on `P.FullSubcategory`, and, when the ambient
  category is triangulated, the induced triangulated structure on `P.FullSubcategory`;
- source/core/bridge triage:
  `source-facing`: the textbook notion of a pretriangulated subcategory of `C`;
  `core/canonical`: `ObjectProperty.IsTriangulated`;
  `bridge/view`: the full-subcategory realizations `Pretriangulated P.FullSubcategory` and
    `IsTriangulated P.FullSubcategory`.

No parallel local wrapper is needed: the source notion is already owned canonically by
`ObjectProperty.IsTriangulated`. -/

/- Definition 13.3.4: a pre-triangulated subcategory of a pre-triangulated category `C` is
formalized by the canonical owner predicate `ObjectProperty.IsTriangulated` on an object property
`P : ObjectProperty C`. -/
recall IsTriangulated

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)
  [P.IsTriangulated]

/- Companion recall: a triangulated object property induces the canonical pretriangulated
structure on the full subcategory `P.FullSubcategory`. -/
#check (inferInstance : Pretriangulated P.FullSubcategory)

/-- A triangulated object property in a preadditive pretriangulated category is closed under
binary coproducts. This is the binary-coproduct companion to the existing binary-product owner
instance from mathlib's triangulated-subcategory API. -/
instance [P.IsClosedUnderIsomorphisms] : P.IsClosedUnderBinaryCoproducts where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    let X₁ := p.diag.obj (.mk .left)
    let X₂ := p.diag.obj (.mk .right)
    let B : BinaryCofan X₁ X₂ := BinaryCofan.mk (p.ι.app (.mk .left)) (p.ι.app (.mk .right))
    have hB : IsColimit B := by
      let hp := ((IsColimit.precomposeHomEquiv (diagramIsoPair p.diag).symm p.cocone).2 p.isColimit)
      simpa [B, BinaryCofan.inl, BinaryCofan.inr] using
        (IsColimit.ofIsoColimit hp (isoBinaryCofanMk _))
    have e : X ≅ X₁ ⨿ X₂ := by
      simpa [B] using hB.coconePointUniqueUpToIso (coprodIsCoprod X₁ X₂)
    let _ : HasBinaryBiproduct X₁ X₂ := HasBinaryBiproduct.of_hasBinaryCoproduct X₁ X₂
    exact P.prop_of_iso e.symm <|
      P.prop_of_iso (biprodIso X₁ X₂) <|
        P.prop_prod X₁ X₂
          (by simpa [X₁] using p.prop_diag_obj (.mk .left))
          (by simpa [X₂] using p.prop_diag_obj (.mk .right))

/-- A triangulated object property in a preadditive pretriangulated category is closed under
finite coproducts. This is the finite-coproduct companion to the binary-coproduct bridge above. -/
instance [P.IsClosedUnderIsomorphisms] : P.IsClosedUnderFiniteCoproducts := by
  let _ : P.IsClosedUnderBinaryCoproducts := inferInstance
  exact IsClosedUnderFiniteCoproducts.mk'

variable [IsTriangulated C]

/- Companion recall: if the ambient category is triangulated, the induced full subcategory is
triangulated in the usual sense. -/
#check (inferInstance : IsTriangulated P.FullSubcategory)

end

end CategoryTheory.ObjectProperty
