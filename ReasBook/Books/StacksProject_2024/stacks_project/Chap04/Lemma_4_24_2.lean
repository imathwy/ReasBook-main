import Mathlib.CategoryTheory.Adjunction.PartialAdjoint

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling for Lemma 4.24.2:
- primary domain: representability criteria for adjoints, owned by
  `Mathlib/CategoryTheory/Adjunction/PartialAdjoint`.
- sampled owner API:
  `Functor.rightAdjointObjIsDefined`,
  `Functor.rightAdjointObjIsDefined_iff`,
  `Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top`,
  `Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top`.
- best owner abstraction: `u.rightAdjointObjIsDefined : ObjectProperty D`.
- source-facing layer: the hypothesis that each presheaf `X ↦ (u.obj X ⟶ Y)` is representable.
- core/canonical layer: the owner criterion that `u.rightAdjointObjIsDefined = ⊤`.
- bridge/view: the theorem below turns the source hypothesis into that owner criterion and then
  reuses the owner theorem for left adjoints.
- primitive data: only the functor `u`.
- derived API: objectwise representability is the pointwise description of
  `u.rightAdjointObjIsDefined`, and `u.IsLeftAdjoint` is then derived from the owner theorem.
-/

/-- Lemma 4.24.2: if for every object `Y : D` the presheaf
`X ↦ (u.obj X ⟶ Y)` is representable, then `u` is a left adjoint, so it has a right adjoint. -/
theorem isLeftAdjoint_of_objwise_hom_isRepresentable (u : C ⥤ D)
    (h : ∀ Y : D, (u.op ⋙ yoneda.obj Y).IsRepresentable) : u.IsLeftAdjoint := by
  rw [u.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top]
  ext Y
  simpa [u.rightAdjointObjIsDefined_iff Y] using h Y

end Functor
end CategoryTheory
